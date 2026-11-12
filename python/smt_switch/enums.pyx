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


cdef class SolverKind:
    def __eq__(self, SolverKind other):
        return (<int> self.ck) == (<int> other.ck)

    def __ne__(self, SolverKind other):
        return (<int> self.ck) != (<int> other.ck)

    def __hash__(self):
        return hash(<int> self.ck)

    def __str__(self):
        return to_string(self.ck).decode()

    def __repr__(self):
        return to_string(self.ck).decode()

    def as_int(self):
        return <int> self.ck


cdef class InterpolatorKind:
    def __eq__(self, InterpolatorKind other):
        return (<int> self.ck) == (<int> other.ck)

    def __ne__(self, InterpolatorKind other):
        return (<int> self.ck) != (<int> other.ck)

    def __hash__(self):
        return hash(<int> self.ck)

    def __str__(self):
        return to_string(self.ck).decode()

    def __repr__(self):
        return to_string(self.ck).decode()

    def as_int(self):
        return <int> self.ck


cdef class OpKind:
    def __eq__(self, OpKind other):
        return (<int> self.ck) == (<int> other.ck)

    def __ne__(self, OpKind other):
        return (<int> self.ck) != (<int> other.ck)

    def __hash__(self):
        return (<int> self.ck)

    def __str__(self):
        return to_string(self.ck).decode()

    def __repr__(self):
        return to_string(self.ck).decode()

    def as_int(self):
        return <int> self.ck
