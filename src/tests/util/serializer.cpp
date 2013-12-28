/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <sstream>
#include <string>
#include <cstring>
#include <vector>
#include <functional>
#include "util/test.h"
#include "util/object_serializer.h"
#include "util/debug.h"
#include "util/list.h"
using namespace lean;

template<typename T>
struct list_ptr_hash { unsigned operator()(list<T> const & l) const { return std::hash<typename list<T>::cell*>()(l.raw()); } };
template<typename T>
struct list_ptr_eq { bool operator()(list<T> const & l1, list<T> const & l2) const { return l1.raw() == l2.raw(); } };

class list_int_serializer : public object_serializer<list<int>, list_ptr_hash<int>, list_ptr_eq<int>> {
    typedef object_serializer<list<int>, list_ptr_hash<int>, list_ptr_eq<int>> super;
public:
    void write(list<int> const & l) {
        super::write(l, [&]() {
                serializer & s = get_owner();
                if (l) {
                    s.write_bool(true);
                    s.write_int(head(l));
                    write(tail(l));
                } else {
                    s.write_bool(false);
                }
            });
    }
};

class list_int_deserializer : public object_deserializer<list<int>> {
    typedef object_deserializer<list<int>> super;
public:
    list<int> read() {
        return super::read([&]() {
                deserializer & d = get_owner();
                if (d.read_bool()) {
                    int h       = d.read_int();
                    list<int> t = read();
                    return list<int>(h, t);
                } else {
                    return list<int>();
                }
            });
    }
};

struct list_int_initializer {
    unsigned m_serializer_extid;
    unsigned m_deserializer_extid;
    list_int_initializer() {
        m_serializer_extid   = serializer::register_extension([](){ return std::unique_ptr<serializer::extension>(new list_int_serializer()); });
        m_deserializer_extid = deserializer::register_extension([](){ return std::unique_ptr<deserializer::extension>(new list_int_deserializer()); });
    }
};

static list_int_initializer g_list_int_initializer;

serializer & operator<<(serializer & s, list<int> const & l) {
    s.get_extension<list_int_serializer>(g_list_int_initializer.m_serializer_extid).write(l);
    return s;
}

deserializer & operator>>(deserializer & d, list<int> & l) {
    l = d.get_extension<list_int_deserializer>(g_list_int_initializer.m_deserializer_extid).read();
    return d;
}

static void tst1() {
    std::ostringstream out;
    serializer s(out);
    s.write_int(10); s.write_int(20); s.write_bool(false); s.write_string("hello"); s.write_int(30);
    std::istringstream in(out.str());
    deserializer d(in);
    lean_assert(d.read_int() == 10);
    lean_assert(d.read_int() == 20);
    lean_assert(!d.read_bool());
    lean_assert(d.read_string() == "hello");
    lean_assert(d.read_int() == 30);
}

static void tst2() {
    std::ostringstream out;
    serializer s(out);
    list<int> l1{1, 2, 3, 4};
    list<int> l2;
    l2 = cons(10, l1);
    list<int> l3;
    l3 = cons(20, cons(30, l2));
    s << l1 << l2 << l3 << l2 << l3;

    std::cout << "OUT: ";
    auto str = out.str();
    for (auto c : str) {
        std::cout << static_cast<int>(c) << " ";
    }
    std::cout << "\n";

    std::istringstream in(out.str());
    deserializer d(in);
    list<int> new_l1, new_l2, new_l3, new_l4, new_l5;
    d >> new_l1 >> new_l2 >> new_l3 >> new_l4 >> new_l5;
    lean_assert_eq(l1, new_l1);
    lean_assert_eq(l2, new_l2);
    lean_assert_eq(l3, new_l3);
    lean_assert_eq(l2, new_l4);
    lean_assert_eq(l3, new_l5);
    lean_assert(is_eqp(new_l1, tail(new_l2)));
    lean_assert(is_eqp(new_l2, tail(tail(new_l3))));
    lean_assert(is_eqp(new_l4, new_l2));
    lean_assert(is_eqp(new_l5, new_l3));
}

int main() {
    tst1();
    tst2();
    return has_violations() ? 1 : 0;
}
