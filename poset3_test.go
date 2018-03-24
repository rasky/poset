package ssa

import (
	"fmt"
	"testing"
)

func TestPoset(t *testing.T) {
	const (
		add         = "add"
		addfail     = "addfail"
		ordered     = "ordered"
		orderedfail = "orderedfail"
		alias       = "alias"
		aliasfail   = "aliasfail"
		checkpoint  = "checkpoint"
		undo        = "undo"
	)

	var v [1024]*Value
	for i := range v {
		v[i] = new(Value)
		v[i].ID = ID(i)
	}

	var ops = []struct {
		typ  string
		a, b int
	}{
		{orderedfail, 123, 124},

		// Dag #0: 100<101
		{checkpoint, 0, 0},
		{add, 100, 101},
		{ordered, 100, 101},
		{orderedfail, 101, 100},
		{addfail, 101, 100},
		{add, 100, 101}, // repeat

		// Dag #1: 4<7<12
		{checkpoint, 0, 0},
		{add, 4, 7},
		{ordered, 4, 7},
		{add, 7, 12},
		{ordered, 7, 12},
		{ordered, 4, 12},
		{orderedfail, 12, 4},

		// Dag #1: 1<4<7<12
		{checkpoint, 0, 0},
		{add, 1, 4},
		{ordered, 1, 4},
		{ordered, 1, 12},
		{orderedfail, 12, 1},

		// Dag #1: 1<4<7<12, 6<7
		{checkpoint, 0, 0},
		{add, 6, 7},
		{ordered, 6, 7},
		{ordered, 6, 12},
		{addfail, 7, 4},
		{addfail, 7, 6},
		{addfail, 7, 1},

		// Dag #1: 1<4<7<12, 1<6<7
		{checkpoint, 0, 0},
		{orderedfail, 1, 6},
		{add, 1, 6},
		{ordered, 1, 6},
		{addfail, 6, 1},

		// Dag #1: 1<4<6<7<12
		{checkpoint, 0, 0},
		{orderedfail, 4, 6},
		{add, 4, 6},
		{ordered, 4, 6},
		{addfail, 6, 4},

		// Merge: 1<4<6<7<12, 6<101
		{checkpoint, 0, 0},
		{orderedfail, 6, 101},
		{add, 6, 101},
		{ordered, 6, 101},
		{ordered, 1, 101},

		// Merge: 1<4<6<7<12, 6<100<101
		{checkpoint, 0, 0},
		{orderedfail, 6, 100},
		{add, 6, 100},
		{ordered, 1, 100},

		// Undo: 1<4<6<7<12, 6<101
		{ordered, 100, 101},
		{undo, 0, 0},
		{ordered, 100, 101},
		{orderedfail, 6, 100},
		{ordered, 6, 101},
		{ordered, 1, 101},

		// Undo: 1<4<6<7<12, 100<101
		{undo, 0, 0},
		{orderedfail, 1, 100},
		{orderedfail, 1, 101},
		{orderedfail, 6, 100},
		{orderedfail, 6, 101},

		// Merge: 1<4<6<7<12, 6<100<101
		{checkpoint, 0, 0},
		{ordered, 100, 101},
		{add, 6, 100},
		{ordered, 6, 100},
		{ordered, 6, 101},
		{ordered, 1, 101},

		// Undo 2 times: 1<4<7<12, 1<6<7
		{undo, 0, 0},
		{undo, 0, 0},
		{ordered, 1, 6},
		{ordered, 4, 12},
		{orderedfail, 4, 6},
		{addfail, 6, 1},

		// Undo 2 times: 1<4<7<12
		{undo, 0, 0},
		{undo, 0, 0},
		{ordered, 1, 12},
		{ordered, 7, 12},
		{orderedfail, 1, 6},
		{orderedfail, 6, 7},
		{ordered, 100, 101},
		{orderedfail, 1, 101},

		// Undo: 4<7<12
		{undo, 0, 0},
		{orderedfail, 1, 12},
		{orderedfail, 1, 4},
		{ordered, 4, 12},
		{ordered, 100, 101},

		// Undo: 100<101
		{undo, 0, 0},
		{orderedfail, 4, 7},
		{orderedfail, 7, 12},
		{ordered, 100, 101},

		// Recreated DAG #1 from scratch, reusing same nodes.
		// This also stresses that undo has done its job correctly.
		// DAG: 1<2<(5|6), 101<102<(105|106<107)
		{checkpoint, 0, 0},
		{add, 101, 102},
		{add, 102, 105},
		{add, 102, 106},
		{add, 106, 107},
		{add, 1, 2},
		{add, 2, 5},
		{add, 2, 6},
		{aliasfail, 1, 6},
		{aliasfail, 107, 102},

		// Now alias 2 and 102
		// New DAG: (1|101)<2<(5|6|105|106<107)
		{checkpoint, 0, 0},
		{alias, 2, 102},
		{ordered, 1, 107},
		{ordered, 101, 6},
		{ordered, 101, 105},
		{ordered, 2, 106},
		{ordered, 102, 6},
		{alias, 2, 102}, // trivially pass

		// Undo alias
		{undo, 0, 0},
		{checkpoint, 0, 0},
		{orderedfail, 2, 102},
		{orderedfail, 1, 107},
		{orderedfail, 101, 6},
		{alias, 2, 100},
		{ordered, 1, 107},
		{ordered, 100, 6},

		// Alias with new node
		{undo, 0, 0},
		{checkpoint, 0, 0},
		{alias, 2, 400},
		{alias, 401, 2},
		{ordered, 1, 400},
		{ordered, 400, 6},
		{ordered, 1, 401},
		{ordered, 401, 6},

		// Alias unseen nodes and then connect
		{checkpoint, 0, 0},
		{alias, 500, 501},
		{alias, 102, 501},
		{ordered, 501, 106},
		{ordered, 100, 500},
		{alias, 500, 501},

		// Undo back to beginning, leave the poset empty
		{undo, 0, 0},
		{undo, 0, 0},
		{undo, 0, 0},
		{undo, 0, 0},
	}

	po := newPoset()
	for idx, op := range ops {
		switch op.typ {
		case add:
			if !po.Add(v[op.a], v[op.b]) {
				t.Errorf("op%d%v failed", idx, op)
			}
		case addfail:
			if po.Add(v[op.a], v[op.b]) {
				t.Errorf("op%d%v passed", idx, op)
			}
		case ordered:
			if !po.Ordered(v[op.a], v[op.b]) {
				t.Errorf("op%d%v failed", idx, op)
			}
		case orderedfail:
			if po.Ordered(v[op.a], v[op.b]) {
				t.Errorf("op%d%v passed", idx, op)
			}
		case checkpoint:
			po.Checkpoint()
		case undo:
			po.Undo()
		case alias:
			if !po.Alias(v[op.a], v[op.b]) {
				t.Errorf("op%d%v failed", idx, op)
			}
		case aliasfail:
			if po.Alias(v[op.a], v[op.b]) {
				t.Errorf("op%d%v passed", idx, op)
			}
		default:
			panic("unimplemented")
		}

		po.dotdump(fmt.Sprintf("op%d.dot", idx), fmt.Sprintf("Last op: %v", op))

		if err := po.checkIntegrity(); err != nil {
			t.Error("Undo stack", po.undo)
			t.Fatalf("op%d%v: integrity error: %v", idx, op, err)
		}
	}

	// Check that the poset is completely empty
	if len(po.values) != 0 {
		t.Errorf("end of test: non-empty value map: %v", po.values)
	}
	if len(po.roots) != 0 {
		t.Errorf("end of test: non-empty root list: %v", po.roots)
	}
	for idx, n := range po.nodes {
		if n.l|n.r != 0 {
			t.Errorf("end of test: non-empty node %v->[%d,%d]", idx, n.l, n.r)
		}
	}
}
