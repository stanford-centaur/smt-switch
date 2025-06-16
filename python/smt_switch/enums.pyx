from .cppenums cimport to_string


cdef class SortKind:
    def __eq__(self, SortKind other):
        return (<int> self.sk) == (<int> other.sk)

    def __ne__(self, SortKind other):
        return (<int> self.sk) != (<int> other.sk)

    def __hash__(self):
        return hash(<int> self.sk)

    def __str__(self):
        return to_string(self.sk).decode()

    def __repr__(self):
        return to_string(self.sk).decode()

    def as_int(self):
        return <int> self.sk


cdef class SolverEnum:
    def __eq__(self, SolverEnum other):
        return (<int> self.se) == (<int> other.se)

    def __ne__(self, SolverEnum other):
        return (<int> self.se) != (<int> other.se)

    def __hash__(self):
        return hash((<int> self.se, self.name))

    def __str__(self):
        return to_string(self.se).decode()

    def __repr__(self):
        return to_string(self.se).decode()

    def as_int(self):
        return <int> self.se


cdef class SolverAttribute:
    def __eq__(self, SolverAttribute other):
        return (<int> self.sa) == (<int> other.sa)

    def __ne__(self, SolverAttribute other):
        return (<int> self.sa) != (<int> other.sa)

    def __hash__(self):
        return hash((<int> self.sa, self.name))

    def __str__(self):
        return to_string(self.sa).decode()

    def __repr__(self):
        return to_string(self.sa).decode()

    def as_int(self):
        return <int> self.sa


cdef class PrimOp:
    def __eq__(self, PrimOp other):
        return (<int> self.po) == (<int> other.po)

    def __ne__(self, PrimOp other):
        return (<int> self.po) != (<int> other.po)

    def __hash__(self):
        return (<int> self.po)

    def __str__(self):
        return to_string(self.po).decode()

    def __repr__(self):
        return to_string(self.po).decode()

    def as_int(self):
        return <int> self.po
