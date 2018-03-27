package ssa

type ID int64

type Op int

const (
	OpGeneric Op = iota
	OpConst8
	OpConst16
	OpConst32
	OpConst64
)

type Value struct {
	ID     ID
	Op     Op
	AuxInt int64
}

func (v *Value) isGenericIntConst() bool {
	switch v.Op {
	case OpConst8, OpConst16, OpConst32, OpConst64:
		return true
	}
	return false
}

func (v *Value) AuxUnsigned() uint64 {
	c := v.AuxInt
	switch v.Op {
	case OpConst64:
		return uint64(c)
	case OpConst32:
		return uint64(uint32(c))
	case OpConst16:
		return uint64(uint16(c))
	case OpConst8:
		return uint64(uint8(c))
	}
	panic("non-constant op")
}
