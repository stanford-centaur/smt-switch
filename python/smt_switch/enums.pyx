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
