/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/interrupt.h"
#include "util/utf8.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_option.h"

namespace lean {
struct vm_string : public vm_external {
    std::string m_value;  // string using utf-8 encoding
    size_t      m_length; // number of unicode scalar values
    vm_string(std::string const & v, size_t len):m_value(v), m_length(len) {}
    virtual ~vm_string() {}
    virtual void dealloc() override { this->~vm_string(); get_vm_allocator().deallocate(sizeof(vm_string), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_string(m_value, m_length); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_string))) vm_string(m_value, m_length); }
};

bool is_string(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_string*>(to_external(o));
}

vm_string const & to_vm_string(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_string*>(to_external(o)));
    return *static_cast<vm_string*>(to_external(o));
}

std::string to_string(vm_obj const & o) {
    return to_vm_string(o).m_value;
}

vm_obj to_obj(std::string const & s, size_t len) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_string))) vm_string(s, len));
}

vm_obj to_obj(std::string const & s) {
    return to_obj(s, utf8_strlen(s.c_str()));
}

static pair<std::string, size_t> list_as_string(vm_obj const & lst) {
    std::string s;
    size_t len = 0;
    vm_obj o   = lst;
    while (!is_simple(o)) {
        push_unicode_scalar(s, cidx(cfield(o, 0)));
        o  = cfield(o, 1);
        len++;
    }
    return mk_pair(s, len);
}

vm_obj string_imp_mk(vm_obj const & lst) {
    std::string s;
    size_t len;
    std::tie(s, len) = list_as_string(lst);
    return to_obj(s, len);
}

vm_obj string_empty() {
    return to_obj(std::string(""));
}

vm_obj string_length(vm_obj const & s) {
    return mk_vm_nat(to_vm_string(s).m_length);
}

vm_obj string_push(vm_obj const & s, vm_obj const & c) {
    vm_string const & vs = to_vm_string(s);
    if (s.raw()->get_rc() == 1) {
        const_cast<vm_string&>(vs).m_length++;
        push_unicode_scalar(const_cast<vm_string&>(vs).m_value, cidx(c));
        return s;
    } else {
        std::string new_s = vs.m_value;
        push_unicode_scalar(new_s, cidx(c));
        return to_obj(new_s, vs.m_length + 1);
    }
}

vm_obj string_append(vm_obj const & s1, vm_obj const & s2) {
    vm_string const & vs1 = to_vm_string(s1);
    vm_string const & vs2 = to_vm_string(s2);
    if (s1.raw()->get_rc() == 1) {
        const_cast<vm_string&>(vs1).m_length += vs2.m_length;
        const_cast<vm_string&>(vs1).m_value  += vs2.m_value;
        return s1;
    } else {
        std::string new_s = vs1.m_value;
        new_s += vs2.m_value;
        return to_obj(new_s, vs1.m_length + vs2.m_length);
    }
}

static vm_obj string_to_list_core(std::string const & str, bool reverse = false) {
    buffer<unsigned> tmp;
    utf8_decode(str, tmp);
    if (reverse)
        std::reverse(tmp.begin(), tmp.end());
    vm_obj   r = mk_vm_simple(0);
    unsigned i = tmp.size();
    while (i > 0) {
        --i;
        vm_obj args[2] = { mk_vm_simple(tmp[i]), r };
        r = mk_vm_constructor(1, 2, args);
    }
    return r;
}

vm_obj string_to_list(vm_obj const & s) {
    return string_to_list_core(to_vm_string(s).m_value);
}

unsigned string_imp_cases_on(vm_obj const & o, buffer<vm_obj> & data) {
    data.push_back(string_to_list(o));
    return 0;
}

vm_obj string_imp_data(vm_obj const & s) {
    return string_to_list(s);
}

vm_obj string_fold(vm_obj const &, vm_obj const & a, vm_obj const & f, vm_obj const & s) {
    vm_string const & vs = to_vm_string(s);
    vm_obj r    = a;
    size_t i    = 0;
    size_t len  = vs.m_value.size();
    while (i < len) {
        unsigned c = next_utf8(vs.m_value, i);
        r          = invoke(f, r, mk_vm_nat(c));
    }
    return r;
}

vm_obj string_mk_iterator(vm_obj const & s) {
    return mk_vm_pair(s, mk_vm_nat(0));
}

vm_string const & it_string(vm_obj const & it) {
    return to_vm_string(cfield(it, 0));
}

size_t it_pos(vm_obj const & it) {
    return force_to_size_t(cfield(it, 1));
}

/*
  instance : inhabited char :=
  ⟨'A'⟩
*/
static vm_obj mk_default_char() {
    return mk_vm_nat(65);
}

vm_obj string_iterator_curr(vm_obj const & it) {
    vm_string const & s = it_string(it);
    size_t i            = it_pos(it);
    if (i < s.m_value.size()) {
        return mk_vm_nat(next_utf8(s.m_value, i));
    } else {
        return mk_default_char();
    }
}

static bool is_unshared_it_vm_string(vm_obj const & it) {
    return it.raw()->get_rc() == 1 && cfield(it, 0).raw()->get_rc() == 1;
}

static unsigned get_utf8_char_size_at(std::string const & s, unsigned i) {
    if (auto sz = is_utf8_first_byte(s[i])) {
        return *sz;
    } else {
        return 1;
    }
}

/*
def set_curr : iterator → char → iterator
*/
vm_obj string_iterator_set_curr(vm_obj const & it, vm_obj const & c) {
    vm_string const & s = it_string(it);
    size_t i            = it_pos(it);
    if (i >= s.m_value.size()) {
        /* at end */
        return it;
    }
    unsigned code       = cidx(c);
    if (is_unshared_it_vm_string(it)) {
        if (static_cast<unsigned char>(s.m_value[i]) < 128 && code < 128) {
            /* easy case, old and new characters are encoded using 1 byte */
            const_cast<vm_string&>(s).m_value[i] = code;
            return it;
        } else {
            /* TODO(Leo): improve performance if bottleneck */
            std::string tmp;
            push_unicode_scalar(tmp, code);
            std::string & new_s = const_cast<vm_string&>(s).m_value;
            new_s.replace(i, get_utf8_char_size_at(new_s, i), tmp);
            return it;
        }
    } else {
        /* TODO(Leo): improve performance if bottleneck */
        std::string tmp;
        push_unicode_scalar(tmp, code);
        std::string new_s = s.m_value;
        new_s.replace(i, get_utf8_char_size_at(new_s, i), tmp);
        return mk_vm_pair(to_obj(new_s, s.m_length), cfield(it, 1));;
    }
}

/*
def next : iterator → iterator
*/
vm_obj string_iterator_next(vm_obj const & it) {
    vm_string const & s = it_string(it);
    size_t i            = it_pos(it);
    if (i < s.m_value.size()) {
        next_utf8(s.m_value, i);
        return update_vm_constructor(it, 1, mk_vm_nat(i));
    } else {
        return it;
    }
}

/*
def prev : iterator → iterator
*/
vm_obj string_iterator_prev(vm_obj const & it) {
    vm_string const & s = it_string(it);
    size_t i            = it_pos(it);
    if (i > 0) {
        size_t new_i = i;
        /* we have to walk at most 4 steps backwards */
        for (unsigned j = 0; j < 4; j++) {
            --new_i;
            if (is_utf8_first_byte(s.m_value[new_i])) {
                return update_vm_constructor(it, 1, mk_vm_nat(new_i));
            }
        }
        /* incorrectly encoded utf-8 string */
        return it;
    } else {
        return it;
    }
}

/*
def has_next : iterator → bool
*/
vm_obj string_iterator_has_next(vm_obj const & it) {
    vm_string const & s = it_string(it);
    size_t i            = it_pos(it);
    return mk_vm_bool(i < s.m_value.size());
}

/*
def has_prev : iterator → bool
*/
vm_obj string_iterator_has_prev(vm_obj const & it) {
    size_t i            = it_pos(it);
    return mk_vm_bool(i > 0);
}

/*
def insert : iterator → string → iterator
*/
vm_obj string_iterator_insert(vm_obj const & it, vm_obj const & s) {
    vm_string const & s_0 = it_string(it);
    vm_string const & s_1 = to_vm_string(s);
    size_t i              = it_pos(it);
    if (i >= s_0.m_value.size()) {
        /* insert s in the end */
        if (is_unshared_it_vm_string(it)) {
            const_cast<vm_string&>(s_0).m_value  += s_1.m_value;
            const_cast<vm_string&>(s_0).m_length += s_1.m_length;
            return it;
        } else {
            std::string new_s = s_0.m_value;
            new_s += s_1.m_value;
            return mk_vm_pair(to_obj(new_s, s_0.m_length + s_1.m_length), mk_vm_nat(i));
        }
    } else {
        /* insert in the middle */
        if (is_unshared_it_vm_string(it)) {
            const_cast<vm_string&>(s_0).m_value.insert(i, s_1.m_value);
            const_cast<vm_string&>(s_0).m_length += s_1.m_length;
            return it;
        } else {
            std::string new_s = s_0.m_value;
            new_s.insert(i, s_1.m_value);
            return mk_vm_pair(to_obj(new_s, s_0.m_length + s_1.m_length), mk_vm_nat(i));
        }
    }
}

/*
def remove : iterator → nat → iterator
*/
vm_obj string_iterator_remove(vm_obj const & it, vm_obj const & _n) {
    vm_string const & s = it_string(it);
    size_t sz           = s.m_value.size();
    size_t i            = it_pos(it);
    size_t j            = i;
    size_t n            = force_to_size_t(_n);
    size_t new_len      = s.m_length;
    for (size_t k = 0; k < n && j < sz; k++) {
        next_utf8(s.m_value, j);
        new_len--;
    }
    size_t count        = j - i;
    if (is_unshared_it_vm_string(it)) {
        const_cast<vm_string&>(s).m_value.erase(i, count);
        const_cast<vm_string&>(s).m_length = new_len;
        return it;
    } else {
        std::string new_s = s.m_value;
        new_s.erase(i, count);
        return mk_vm_pair(to_obj(new_s, new_len), mk_vm_nat(i));
    }
}

/*
def to_string : iterator → string
*/
vm_obj string_iterator_to_string(vm_obj const & it) {
    return cfield(it, 0);
}

/*
def to_end : iterator → iterator
*/
vm_obj string_iterator_to_end(vm_obj const & it) {
    vm_string const & s = it_string(it);
    return update_vm_constructor(it, 1, mk_vm_nat(s.m_value.size()));
}

/*
def next_to_string : iterator → string
*/
vm_obj string_iterator_next_to_string(vm_obj const & it) {
    vm_string const & s = it_string(it);
    size_t i            = it_pos(it);
    std::string r;
    for (; i < s.m_value.size(); i++) {
        r += s.m_value[i];
    }
    return to_obj(r);
}

/*
def prev_to_string : iterator → string
*/
vm_obj string_iterator_prev_to_string(vm_obj const & it) {
    vm_string const & s = it_string(it);
    size_t pos          = it_pos(it);
    std::string r;
    for (size_t i = 0; i < pos; i++) {
        r += s.m_value[i];
    }
    return to_obj(r);
}

static pair<std::string, size_t> rev_list_as_string(vm_obj const & lst) {
    buffer<unsigned> codes;
    size_t len = 0;
    vm_obj o   = lst;
    while (!is_simple(o)) {
        codes.push_back(cidx(cfield(o, 0)));
        o  = cfield(o, 1);
        len++;
    }
    std::reverse(codes.begin(), codes.end());
    std::string s;
    for (unsigned c : codes) {
        push_unicode_scalar(s, c);
    }
    return mk_pair(s, len);
}

vm_obj string_iterator_imp_mk(vm_obj const & l1, vm_obj const & l2) {
    pair<std::string, size_t> p1 = rev_list_as_string(l1);
    pair<std::string, size_t> p2 = list_as_string(l2);
    std::string s = p1.first;
    std::reverse(s.begin(), s.end());
    s += p2.first;
    vm_obj new_s = to_obj(s, p1.second + p2.second);
    return mk_vm_pair(new_s, mk_vm_nat(p1.second));
}

unsigned string_iterator_imp_cases_on(vm_obj const & o, buffer<vm_obj> & data) {
    vm_obj p = string_iterator_prev_to_string(o);
    vm_obj n = string_iterator_next_to_string(o);
    data.push_back(string_to_list_core(to_vm_string(p).m_value, true /* reverse */));
    data.push_back(string_to_list_core(to_vm_string(n).m_value));
    return 0;
}

vm_obj string_iterator_imp_fst(vm_obj const & o) {
    vm_obj p = string_iterator_prev_to_string(o);
    return string_to_list_core(to_vm_string(p).m_value, true /* reverse */);
}

vm_obj string_iterator_imp_snd(vm_obj const & o) {
    vm_obj n = string_iterator_next_to_string(o);
    return string_to_list_core(to_vm_string(n).m_value);
}

vm_obj string_has_decidable_eq(vm_obj const & s1, vm_obj const & s2) {
    return mk_vm_bool(to_vm_string(s1).m_value == to_vm_string(s2).m_value);
}

/*
inductive ordering
| lt | eq | gt

Remark: we may decide to expose this function in the future.
*/
static vm_obj string_cmp(vm_obj const & s1, vm_obj const & s2) {
    vm_string const & vs1 = to_vm_string(s1);
    vm_string const & vs2 = to_vm_string(s2);
    size_t sz1 = vs1.m_value.size();
    size_t sz2 = vs2.m_value.size();
    size_t i1  = 0;
    size_t i2  = 0;
    while (i1 < sz1 && i2 < sz2) {
        unsigned c1 = next_utf8(vs1.m_value, i1);
        unsigned c2 = next_utf8(vs2.m_value, i2);
        if (c1 < c2)
            return mk_vm_simple(0); /* lt */
        if (c1 > c2)
            return mk_vm_simple(2); /* gt */
    }
    if (i1 < sz1)
        return mk_vm_simple(2); /* gt */
    else if (i2 < sz2)
        return mk_vm_simple(0); /* lt */
    else
        return mk_vm_simple(1); /* eq */
}

vm_obj string_has_decidable_lt(vm_obj const & s1, vm_obj const & s2) {
    vm_obj r = string_cmp(s1, s2);
    if (cidx(r) == 0) return mk_vm_simple(1);
    else return mk_vm_simple(0);
}

vm_obj string_iterator_extract(vm_obj const & it1, vm_obj const & it2) {
    vm_string const & s1 = it_string(it1);
    vm_string const & s2 = it_string(it2);
    if (&s1 != &s2 && s1.m_value != s2.m_value)
        return mk_vm_none();
    size_t pos1 = it_pos(it1);
    size_t pos2 = it_pos(it2);
    if (pos2 < pos1)
        return mk_vm_none();
    return mk_vm_some(to_obj(s1.m_value.substr(pos1, pos2 - pos1), pos2 - pos1));
}

void initialize_vm_string() {
    DECLARE_VM_BUILTIN(name({"string_imp", "mk"}),             string_imp_mk);
    DECLARE_VM_BUILTIN(name({"string_imp", "data"}),           string_imp_data);
    DECLARE_VM_CASES_BUILTIN(name({"string_imp", "cases_on"}), string_imp_cases_on);

    DECLARE_VM_BUILTIN(name({"string", "length"}),            string_length);
    DECLARE_VM_BUILTIN(name({"string", "empty"}),             string_empty);
    DECLARE_VM_BUILTIN(name({"string", "push"}),              string_push);
    DECLARE_VM_BUILTIN(name({"string", "append"}),            string_append);
    DECLARE_VM_BUILTIN(name({"string", "to_list"}),           string_to_list);
    DECLARE_VM_BUILTIN(name({"string", "fold"}),              string_fold);
    DECLARE_VM_BUILTIN(name({"string", "mk_iterator"}),       string_mk_iterator);
    DECLARE_VM_BUILTIN(name({"string", "has_decidable_eq"}),  string_has_decidable_eq);
    // DECLARE_VM_BUILTIN(name({"string", "cmp"}),               string_cmp);
    DECLARE_VM_BUILTIN(name({"string", "has_decidable_lt"}),  string_has_decidable_lt);

    DECLARE_VM_BUILTIN(name({"string", "iterator", "curr"}),           string_iterator_curr);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "set_curr"}),       string_iterator_set_curr);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "next"}),           string_iterator_next);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "prev"}),           string_iterator_prev);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "has_next"}),       string_iterator_has_next);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "has_prev"}),       string_iterator_has_prev);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "insert"}),         string_iterator_insert);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "remove"}),         string_iterator_remove);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "to_string"}),      string_iterator_to_string);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "to_end"}),         string_iterator_to_end);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "next_to_string"}), string_iterator_next_to_string);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "prev_to_string"}), string_iterator_prev_to_string);
    DECLARE_VM_BUILTIN(name({"string", "iterator", "extract"}),        string_iterator_extract);

    DECLARE_VM_BUILTIN(name({"string", "iterator_imp", "mk"}),              string_iterator_imp_mk);
    DECLARE_VM_BUILTIN(name({"string", "iterator_imp", "fst"}),             string_iterator_imp_fst);
    DECLARE_VM_BUILTIN(name({"string", "iterator_imp", "snd"}),             string_iterator_imp_snd);
    DECLARE_VM_CASES_BUILTIN(name({"string", "iterator_imp", "cases_on"}),  string_iterator_imp_cases_on);
}

void finalize_vm_string() {
}
}
