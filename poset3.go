package ssa

import (
	"errors"
	"fmt"
	"os"
)

const uintSize = 32 << (^uint(0) >> 32 & 1) // 32 or 64
type bitset []uint

func newBitset(n int) bitset {
	return make(bitset, (n+uintSize-1)/uintSize)
}

func (bs bitset) Set(idx uint32) {
	bs[idx/uintSize] |= 1 << (idx % uintSize)
}

func (bs bitset) Test(idx uint32) bool {
	return bs[idx/uintSize]&(1<<(idx%uintSize)) != 0
}

const (
	flagDummy = 1 << iota
)

type posetUndo struct {
	typ    string
	idx    uint32
	parent uint32
	ID     ID
	flags  uint8
	refs   []uint32
}

type posetNode struct {
	l, r uint32 // left/right child
}

// poset is a union-find datastructure that can represent a partial order.
// It is implemented as a forest of DAGs, where each DAG is made by nodes
// that can have max 2 children.
// poset is memory efficient.
type poset struct {
	lastidx uint32        // last generated dense index
	values  map[ID]uint32 // map SSA values to dense indices
	nodes   []posetNode   // nodes (in all DAGs)
	roots   []uint32      // list of root nodes (forest)
	undo    []posetUndo
}

func newPoset() *poset {
	return &poset{
		values: make(map[ID]uint32),
		nodes:  make([]posetNode, 1, 1024),
		roots:  make([]uint32, 0, 64),
		undo:   make([]posetUndo, 0, 256),
	}
}

// Handle children
func (po *poset) setchl(i uint32, l uint32)          { po.nodes[i].l = l }
func (po *poset) setchr(i uint32, r uint32)          { po.nodes[i].r = r }
func (po *poset) chl(i uint32) uint32                { return po.nodes[i].l }
func (po *poset) chr(i uint32) uint32                { return po.nodes[i].r }
func (po *poset) children(i uint32) (uint32, uint32) { return po.nodes[i].l, po.nodes[i].r }

// upush records a new undo step
func (po *poset) upush(s string, i, p uint32, flags uint8) {
	po.undo = append(po.undo, posetUndo{typ: s, idx: i, parent: p, flags: flags})
}

func (po *poset) upushnew(s string, ID ID, i1, i2 uint32, refs []uint32) {
	po.undo = append(po.undo, posetUndo{typ: s, ID: ID, idx: i1, parent: i2, refs: refs})
}

// addchild adds i2 as direct child of i1
func (po *poset) addchild(i1, i2 uint32) {
	i1l, i1r := po.children(i1)
	if i1l == 0 {
		po.setchl(i1, i2)
		po.upush("addchild_left", i2, i1, 0)
	} else if i1r == 0 {
		po.setchr(i1, i2)
		po.upush("addchild_right", i2, i1, 0)
	} else {
		// If n1 already has two children, add an intermediate dummy
		// node to record the relation correctly (without relating
		// n2 to other existing nodes).
		//
		//      n1
		//     /  \
		//   i1l  dummy
		//        /   \
		//      i1r   n2
		//
		dummy := po.newnode(nil)
		po.setchl(dummy, i1r)
		po.setchr(dummy, i2)
		po.setchr(i1, dummy)
		po.upush("addchild_1", dummy, i1, flagDummy)
		po.upush("addchild_2", i2, dummy, 0)
	}
}

// newnode allocates a new node bound to SSA value n.
// If n is nil, this is a dummy node (= only used internally).
func (po *poset) newnode(n *Value) uint32 {
	i := po.lastidx + 1
	po.lastidx++
	if n != nil {
		if po.values[n.ID] != 0 {
			panic("newnode for Value already inserted")
		}
		po.values[n.ID] = i
		po.upushnew("newnode", n.ID, i, 0, nil)
	} else {
		po.upushnew("newdummy", ID(0), i, 0, nil)
	}
	po.nodes = append(po.nodes, posetNode{})
	return i
}

// aliasnode records that n2 is an alias of n1
func (po *poset) aliasnode(n1, n2 *Value) {
	i1 := po.values[n1.ID]
	if i1 == 0 {
		panic("aliasnode for non-existing node")
	}

	var refs []uint32
	i2 := po.values[n2.ID]
	if i2 != 0 {
		// Rename all references to i2 into i1
		for idx, n := range po.nodes {
			if n.l == i2 {
				po.setchl(uint32(idx), i1)
				refs = append(refs, uint32(idx*2))
			}
			if n.r == i2 {
				po.setchr(uint32(idx), i1)
				refs = append(refs, uint32(idx*2+1))
			}
		}
	}

	po.upushnew("aliasnode", n2.ID, i1, i2, refs)
	po.values[n2.ID] = i1
}

func (po *poset) isroot(r uint32) bool {
	for i := range po.roots {
		if po.roots[i] == r {
			return true
		}
	}
	return false
}

func (po *poset) changeroot(oldr, newr uint32) {
	for i := range po.roots {
		if po.roots[i] == oldr {
			po.roots[i] = newr
			return
		}
	}
	panic("changeroot on non-root")
}

func (po *poset) removeroot(r uint32) {
	for i := range po.roots {
		if po.roots[i] == r {
			po.roots = append(po.roots[:i], po.roots[i+1:]...)
			return
		}
	}
	panic("removeroot on non-root")
}

// dfs performs a depth-first search within the DAG whose root is r.
// f is the visit function called for each node; if it returns true,
// the search is aborted and true is returned.
// If the visit ends, false is returned.
func (po *poset) dfs(r uint32, f func(i uint32) bool) bool {
	closed := newBitset(int(po.lastidx + 1))
	open := make([]uint32, 1, po.lastidx+1)
	open[0] = r

	for len(open) > 0 {
		i := open[len(open)-1]
		open = open[:len(open)-1]

		if !closed.Test(i) {
			if f(i) {
				return true
			}
			closed.Set(i)
			l, r := po.children(i)
			if l != 0 {
				open = append(open, l)
			}
			if r != 0 {
				open = append(open, r)
			}
		}
	}
	return false
}

// Returns true if i1 dominates i2 (that is, i1<i2 maybe transitively)
func (po *poset) dominates(i1, i2 uint32) bool {
	return po.dfs(i1, func(n uint32) bool {
		return n == i2
	})
}

// findroot finds i's root, that is which DAG contains i.
// Returns the root; if i is itself a root, it is returned.
// Panic if i is not in any DAG.
func (po *poset) findroot(i uint32) uint32 {
	// TODO(rasky): if needed, a way to speed up this search is
	// storing a bitset for each root using it as a mini bloom filter
	// of nodes present under that root.
	for _, r := range po.roots {
		if po.dominates(r, i) {
			return r
		}
	}
	panic("findroot didn't find any root")
}

// checkIntegrity verifies internal integrity of a poset
// (for debugging purposes)
func (po *poset) checkIntegrity() (err error) {
	// Verify that each node appears in a single DAG
	seen := newBitset(int(po.lastidx + 1))
	for _, r := range po.roots {
		if r == 0 {
			err = errors.New("empty root")
			return
		}

		po.dfs(r, func(i uint32) bool {
			if seen.Test(i) {
				err = errors.New("duplicate node")
				return true
			}
			seen.Set(i)
			return false
		})
		if err != nil {
			return
		}
	}

	// Verify that values contain the minimum set
	for id, idx := range po.values {
		if !seen.Test(idx) {
			err = fmt.Errorf("spurious value [%d]=%d", id, idx)
			return
		}
	}

	// Verify that only existing nodes have non-zero children
	for i, n := range po.nodes {
		if n.l|n.r != 0 && !seen.Test(uint32(i)) {
			err = fmt.Errorf("children of unknown node %d->%v", i, n)
			return
		}
	}

	return
}

// dotdump dumps the poset in graphviz format for debugging
func (po *poset) dotdump(fn string, title string) error {
	f, err := os.Create(fn)
	if err != nil {
		return err
	}
	defer f.Close()

	// Create reverse index mapping (taking aliases into account)
	names := make(map[uint32]string)
	for id, i := range po.values {
		s := names[i]
		if s == "" {
			s = fmt.Sprintf("v%d", id)
		} else {
			s += fmt.Sprintf(", v%d", id)
		}
		names[i] = s
	}

	fmt.Fprintf(f, "digraph poset {\n")
	for ridx, r := range po.roots {
		fmt.Fprintf(f, "\tsubgraph root%d {\n", ridx)
		po.dfs(r, func(i uint32) bool {
			fmt.Fprintf(f, "\t\tnode%d [label=\"%s\"]\n", i, names[i])
			chl, chr := po.children(i)
			if chl != 0 {
				fmt.Fprintf(f, "\t\tnode%d -> node%d\n", i, chl)
			}
			if chr != 0 {
				fmt.Fprintf(f, "\t\tnode%d -> node%d\n", i, chr)
			}
			return false
		})
		fmt.Fprintf(f, "\t}\n")
	}
	fmt.Fprintf(f, "\tlabelloc=\"t\"\n")
	fmt.Fprintf(f, "\tlabeldistance=\"3.0\"\n")
	fmt.Fprintf(f, "\tlabel=%q\n", title)
	fmt.Fprintf(f, "}\n")
	return nil
}

// Ordered returns true if n1<n2. It panics if n1 and n2 are
// the same object, to ease debugging, as this is trivially false
// and should always be checked before calling Ordered when the caller
// knows that it is a possibility.
func (po *poset) Ordered(n1, n2 *Value) bool {
	if n1.ID == n2.ID {
		panic("should not call Ordered with n1==n2")
	}

	i1, f1 := po.values[n1.ID]
	i2, f2 := po.values[n2.ID]
	if !f1 || !f2 {
		return false
	}

	return po.dominates(i1, i2)
}

// Add records that n1<n2. Returns false if this is a contradiction
func (po *poset) Add(n1, n2 *Value) bool {
	if n1.ID == n2.ID {
		panic("should not call Add with n1==n2")
	}

	i1, f1 := po.values[n1.ID]
	i2, f2 := po.values[n2.ID]

	switch {
	case !f1 && !f2:
		// Neither n1 nor n2 are in the poset, so they are not related
		// in any way to existing nodes.
		// Create a new DAG to record the relation.
		i1, i2 = po.newnode(n1), po.newnode(n2)
		po.roots = append(po.roots, i1)
		po.setchl(i1, i2)
		po.upush("addnew_1", i1, 0, 0)
		po.upush("addnew_2", i2, i1, 0)

	case f1 && !f2:
		// n1 is in one of the DAGs, while n2 is not. Add n2 as children
		// of n1.
		i2 = po.newnode(n2)
		po.addchild(i1, i2)

	case !f1 && f2:
		// n1 is not in any DAG but n2 is. If n2 is a root, we can put
		// n1 in its place as a root; otherwise, we need to create a new
		// dummy root to record the relation.
		i1 = po.newnode(n1)

		if po.isroot(i2) {
			po.setchl(i1, i2)
			po.changeroot(i2, i1)
			po.upush("addasroot", i1, 0, flagDummy)
			return true
		}

		// Search for i2's root; this requires a O(n) search on all
		// DAGs
		r := po.findroot(i2)

		// Re-parent as follows:
		//
		//                  dummy
		//     r            /   \
		//      \   ===>   r    i1
		//      i2          \   /
		//                    i2
		//
		dummy := po.newnode(nil)
		po.setchl(dummy, r)
		po.setchr(dummy, i1)
		po.setchl(i1, i2)
		po.changeroot(r, dummy)
		po.upush("addleftdummy_1", dummy, 0, flagDummy)
		po.upush("addleftdummy_2", i1, dummy, 0)

	case f1 && f2:
		// Both n1 and n2 are in the poset. First, check if they're already related
		if po.dominates(i1, i2) {
			return true
		}
		if po.dominates(i2, i1) {
			// Contradiction!
			return false
		}

		// Find their roots
		r1, r2 := po.findroot(i1), po.findroot(i2)
		if r1 != r2 {
			// We need to merge the two DAGs. Merge the two roots with a dummy node
			r := po.newnode(nil)
			po.setchl(r, r1)
			po.setchr(r, r2)
			po.changeroot(r1, r)
			po.removeroot(r2)
			po.upush("addboth", r, 0, flagDummy)
		}

		// Connect n1 and n2
		po.addchild(i1, i2)
	}

	return true
}

// Alias records that n1==n2. Returns false if this is a contradiction
// (that is, if it is already recorded that n1<n2 or n2<n1).
func (po *poset) Alias(n1, n2 *Value) bool {
	if n1.ID == n2.ID {
		panic("should not call Add with n1==n2")
	}

	i1, f1 := po.values[n1.ID]
	i2, f2 := po.values[n2.ID]

	switch {
	case !f1 && !f2:
		i1 = po.newnode(n1)
		po.roots = append(po.roots, i1)
		po.aliasnode(n1, n2)
	case f1 && !f2:
		po.aliasnode(n1, n2)
	case !f1 && f2:
		po.aliasnode(n2, n1)
	case f1 && f2:
		if i1 == i2 {
			// Already aliased, ignore
			return true
		}

		r1 := po.findroot(i1)
		r2 := po.findroot(i2)
		if r1 == r2 {
			// If they're in the same DAG, they cannot possibly be equal.
			return false
		}

		// Merge the DAGs. First, merge the roots
		r := po.newnode(nil)
		po.setchl(r, r1)
		po.setchr(r, r2)
		po.changeroot(r1, r)
		po.removeroot(r2)
		po.upush("alias_mergedag", r, 0, flagDummy)

		// Set n2 as alias of n1. This will also update all the references
		// to n2 to become references to n1
		po.aliasnode(n1, n2)

		// Connect i2 as child of i1 (possibly with a dummy node)
		po.addchild(i1, i2)
	}
	return true
}

func (po *poset) Checkpoint() {
	po.undo = append(po.undo, posetUndo{typ: "checkpoint"})
}

func (po *poset) Undo() {
	if len(po.undo) == 0 {
		panic("empty undo stack")
	}

	for len(po.undo) > 0 {
		pass := po.undo[len(po.undo)-1]
		po.undo = po.undo[:len(po.undo)-1]

		switch pass.typ {
		case "checkpoint":
			return

		case "newdummy":
			po.setchl(pass.idx, 0)
			po.setchr(pass.idx, 0)

		case "newnode":
			if po.values[pass.ID] != pass.idx {
				panic("invalid newnode undo pass")
			}
			delete(po.values, pass.ID)
			po.setchl(pass.idx, 0)
			po.setchr(pass.idx, 0)

		case "aliasnode":
			ID, cur, prev := pass.ID, pass.idx, pass.parent
			if po.values[ID] != cur {
				panic("invalid aliasnode id in undo pass")
			}
			if prev == 0 {
				// Born as an alias, die as an alias
				delete(po.values, ID)
			} else {
				// Give it back previous value
				po.values[ID] = prev

				// Restore references to the previous value
				for _, r := range pass.refs {
					idx := r / 2
					if r&1 == 0 {
						if po.nodes[idx].l != cur {
							panic("invalid aliasnode ref in undo pass")
						}
						po.nodes[idx].l = prev
					} else {
						if po.nodes[idx].r != cur {
							panic("invalid aliasnode ref in undo pass")
						}
						po.nodes[idx].r = prev
					}
				}
			}

		default:
			i, p := pass.idx, pass.parent
			l, r := po.children(i)
			isdummy := (pass.flags & flagDummy) != 0

			// We need to remove node i. This is the potential layout
			// (but some nodes could be zero):
			//
			//    p
			//    |
			//    i
			//   / \
			//  l   r
			//
			if p != 0 {
				// p exists, so i is not a root node.
				// If i has two children, we assume it's been
				// parented to p while it was already in the DAG,
				// so we simply disconnect the parent.
				// Otherwise, connect the only child to the parent.
				var child uint32
				if isdummy {
					child = l
					if r != 0 {
						child = r
					}
				}
				if po.chl(p) == i {
					po.setchl(p, child)
				} else {
					po.setchr(p, child)
				}
			} else {
				// Undo adding a new root
				if l != 0 && r != 0 {
					// Split DAGs in two
					po.changeroot(i, l)
					po.roots = append(po.roots, r)
				} else {
					child := l
					if r != 0 {
						child = r
					}
					if child != 0 {
						po.changeroot(i, child)
					} else {
						po.removeroot(i)
					}
				}
			}
		}
	}
}
