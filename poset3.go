package poset

import (
	"errors"
	"fmt"
)

type Values struct {
	ID int64
}

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
	flagNewNode
)

type undoPass struct {
	typ    string
	idx    uint32
	parent uint32
	flags  uint8
}

var undoCheckpoint = undoPass{"", 0, 0, 0}

type node struct {
	l, r uint32
}

// podag is a union-find datastructure that can represent a partial order.
// It is implemented as a forest of DAGs, where each DAG is made by nodes
// that can have max 2 children.
// podag is memory efficient.
type podag struct {
	lastidx uint32             // last generated dense index
	nodes   map[*Values]uint32 // map SSA values to dense indices
	c       []node             // given node i, c[i*2] and c[i*2+1] are the two children
	roots   []uint32           // list of root nodes (forest)
	undo    []undoPass
}

func newPodag() *podag {
	return &podag{
		nodes: make(map[*Values]uint32),
		c:     make([]node, 1, 1024),
		roots: make([]uint32, 0, 64),
		undo:  make([]undoPass, 0, 256),
	}
}

func (po *podag) upush(p undoPass) {
	po.undo = append(po.undo, p)
}

// set children
func (po *podag) setchl(i uint32, l uint32)          { po.c[i].l = l }
func (po *podag) setchr(i uint32, r uint32)          { po.c[i].r = r }
func (po *podag) chl(i uint32) uint32                { return po.c[i].l }
func (po *podag) chr(i uint32) uint32                { return po.c[i].r }
func (po *podag) children(i uint32) (uint32, uint32) { return po.c[i].l, po.c[i].r }

// addchild adds i2 as direct child of i1
func (po *podag) addchild(i1, i2 uint32) {
	i1l, i1r := po.children(i1)
	if i1l == 0 {
		po.setchl(i1, i2)
		po.upush(undoPass{"addchild_left", i2, i1, 0})
	} else if i1r == 0 {
		po.setchr(i1, i2)
		po.upush(undoPass{"addchild_right", i2, i1, 0})
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
		po.upush(undoPass{"addchild_1", dummy, i1, flagDummy})
		po.upush(undoPass{"addchild_2", i2, dummy, 0})
	}
}

// newnode allocates a new node bound to SSA value n.
// If n is nil, this is a dummy node (= only used internally).
func (po *podag) newnode(n *Values) uint32 {
	i := po.lastidx + 1
	po.lastidx++
	if n != nil {
		po.nodes[n] = i
	}
	po.c = append(po.c, node{0, 0})
	return i
}

func (po *podag) isroot(r uint32) bool {
	for i := range po.roots {
		if po.roots[i] == r {
			return true
		}
	}
	return false
}

func (po *podag) changeroot(oldr, newr uint32) {
	for i := range po.roots {
		if po.roots[i] == oldr {
			po.roots[i] = newr
			return
		}
	}
	panic("changeroot on non-root")
}

func (po *podag) removeroot(r uint32) {
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
func (po *podag) dfs(r uint32, f func(i uint32) bool) bool {
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
func (po *podag) dominates(i1, i2 uint32) bool {
	return po.dfs(i1, func(n uint32) bool {
		return n == i2
	})
}

// findroot finds i's root, that is which DAG contains i.
// Returns the root; if i is itself a root, it is returned.
// Panic if i is not in any DAG.
func (po *podag) findroot(i uint32) uint32 {
	for _, r := range po.roots {
		if po.dominates(r, i) {
			return r
		}
	}
	panic("findroot didn't find any root")
}

// checkIntegrity verifies internal integrity of a podag
// (for debugging purposes)
func (po *podag) checkIntegrity() (err error) {
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

	// Verify that only existing nodes have non-zero children
	for i, n := range po.c {
		if n.l|n.r != 0 && !seen.Test(uint32(i)) {
			err = fmt.Errorf("children of unknown node %d->%v", i/2, n)
			return
		}
	}

	return
}

// Ordered returns true if n1<n2. It panics if n1 and n2 are
// the same object, to ease debugging, as this is trivially false
// and should always be checked before calling Ordered when the caller
// knows that it is a possibility.
func (po *podag) Ordered(n1, n2 *Values) bool {
	if n1 == n2 {
		panic("should not call Ordered with n1==n2")
	}

	i1, f1 := po.nodes[n1]
	i2, f2 := po.nodes[n2]
	if !f1 || !f2 {
		return false
	}

	return po.dominates(i1, i2)
}

// Add records that n1<n2. Returns false if this is a contradiction
func (po *podag) Add(n1, n2 *Values) bool {
	i1, f1 := po.nodes[n1]
	i2, f2 := po.nodes[n2]

	switch {
	case !f1 && !f2:
		// Neither n1 nor n2 are in the podag, so they are not related
		// in any way to existing nodes.
		// Create a new DAG to record the relation.
		i1, i2 = po.newnode(n1), po.newnode(n2)
		po.roots = append(po.roots, i1)
		po.setchl(i1, i2)
		po.upush(undoPass{"addnew_1", i1, 0, 0})
		po.upush(undoPass{"addnew_2", i2, i1, 0})

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
			po.upush(undoPass{"addasroot", i1, 0, flagDummy})
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
		po.upush(undoPass{"addleftdummy_1", dummy, 0, flagDummy})
		po.upush(undoPass{"addleftdummy_2", i1, dummy, flagNewNode})

	case f1 && f2:
		// Both n1 and n2 are in the podag. First, check if they're already related
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
			po.upush(undoPass{"addboth", r, 0, flagDummy})
		}

		// Connect n1 and n2
		po.addchild(i1, i2)
	}

	return true
}

func (po *podag) Checkpoint() {
	po.upush(undoCheckpoint)
}

func (po *podag) Undo() {
	if len(po.undo) == 0 {
		panic("empty undo stack")
	}

	for len(po.undo) > 0 {
		pass := po.undo[len(po.undo)-1]
		po.undo = po.undo[:len(po.undo)-1]
		if pass == undoCheckpoint {
			break
		}

		i, p := pass.idx, pass.parent
		l, r := po.children(i)
		isdummy := (pass.flags & flagDummy) != 0
		isnew := (pass.flags & flagNewNode) != 0

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
			fmt.Printf("undo %s %d->%d->[%d,%d] delete:%d\n", pass.typ, p, i, l, r, child)
			if po.chl(p) == i {
				po.setchl(p, child)
			} else {
				po.setchr(p, child)
			}
			// Disconnect children of i. While not strictly necessary (as i
			// is now removed from the DAG), it's useful for debugging purposes:
			// checkIntegrity() will detect dangling children and report bugs.
			if isdummy || isnew {
				po.setchl(i, 0)
				po.setchr(i, 0)
			}
		} else {
			// Undo adding a new root
			fmt.Printf("undoroot %s %d->%d->[%d,%d]\n", pass.typ, p, i, l, r)
			if l != 0 && r != 0 {
				// Split DAGs in two
				po.changeroot(i, l)
				po.roots = append(po.roots, r)
				po.setchl(i, 0)
				po.setchr(i, 0)
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
				po.setchl(i, 0)
				po.setchr(i, 0)
			}
		}

	}
}
