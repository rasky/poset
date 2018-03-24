package ssa

import (
	"testing"
)

func TestPoset(t *testing.T) {
	const (
		add = iota
		addfail
		ordered
		orderedfail
		checkpoint
		undo
	)

	var v [1024]*Value
	for i := range v {
		v[i] = new(Value)
		v[i].ID = ID(i)
	}

	var ops = []struct {
		typ  int
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

		// Undo: 1<4<6<7<12
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

		// Undo 2 times: 4<7<12
		{undo, 0, 0},
		{orderedfail, 1, 12},
		{orderedfail, 1, 4},
		{ordered, 4, 12},
		{ordered, 100, 101},

		// Undo 2 times: 100<101
		{undo, 0, 0},
		{orderedfail, 4, 7},
		{orderedfail, 7, 12},
		{ordered, 100, 101},
	}

	po := newPoset()
	for idx, op := range ops {
		switch op.typ {
		case add:
			if !po.Add(v[op.a], v[op.b]) {
				t.Errorf("op%d: add(%d,%d) failed", idx, op.a, op.b)
			}
		case addfail:
			if po.Add(v[op.a], v[op.b]) {
				t.Errorf("op%d: addfail(%d,%d) passed", idx, op.a, op.b)
			}
		case ordered:
			if !po.Ordered(v[op.a], v[op.b]) {
				t.Errorf("op%d: ordered(%d,%d) failed", idx, op.a, op.b)
			}
		case orderedfail:
			if po.Ordered(v[op.a], v[op.b]) {
				t.Errorf("op%d: orderedfail(%d,%d) passed", idx, op.a, op.b)
			}
		case checkpoint:
			po.Checkpoint()
		case undo:
			po.Undo()
		}

		if err := po.checkIntegrity(); err != nil {
			t.Fatalf("op%d: integrity error: %v", idx, err)
		}
	}
}
