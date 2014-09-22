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
#include <cmath>
#include "util/test.h"
#include "util/object_serializer.h"
#include "util/debug.h"
#include "util/list.h"
#include "util/name.h"
#include "util/init_module.h"
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
                    return cons(h, t);
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

std::unique_ptr<list_int_initializer> g_list_int_initializer;

serializer & operator<<(serializer & s, list<int> const & l) {
    s.get_extension<list_int_serializer>(g_list_int_initializer->m_serializer_extid).write(l);
    return s;
}

deserializer & operator>>(deserializer & d, list<int> & l) {
    l = d.get_extension<list_int_deserializer>(g_list_int_initializer->m_deserializer_extid).read();
    return d;
}

void display(std::ostringstream const & out) {
    std::cout << "OUT: ";
    auto str = out.str();
    for (auto c : str) {
        std::cout << static_cast<int>(static_cast<unsigned char>(c)) << " ";
    }
    std::cout << "\n";
}

static void tst1() {
    std::ostringstream out;
    serializer s(out);
    s.write_int(10); s.write_int(-20); s.write_bool(false); s.write_string("hello"); s.write_int(30);
    display(out);
    std::istringstream in(out.str());
    deserializer d(in);
    lean_assert(d.read_int() == 10);
    lean_assert(d.read_int() == -20);
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
    display(out);

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

static void tst3() {
    std::ostringstream out;
    serializer s(out);
    name n1{"foo", "bla"};
    name n2(n1, 10);
    name n3(n2, "tst");
    name n4(n1, "hello");
    name n5("simple");
    s << n1 << n2 << n3 << n4 << n2 << n5;
    display(out);
    std::istringstream in(out.str());
    deserializer d(in);
    name m1, m2, m3, m4, m5, m6;
    d >> m1 >> m2 >> m3 >> m4 >> m5 >> m6;
    lean_assert(n1 == m1);
    lean_assert(n2 == m2);
    lean_assert(n3 == m3);
    lean_assert(n4 == m4);
    lean_assert(n2 == m5);
    lean_assert(n5 == m6);
}

static void tst4() {
    std::ostringstream out;
    serializer s(out);
    double d1, d2, d3, d4, d5;
    d1 = 0.1;
    d2 = -0.3;
    d3 = 0.0;
    d4 = 12317.123;
    d5 = std::atan(1.0)*4;
    s << d1 << d2 << d3 << d4 << d5;
    std::istringstream in(out.str());
    deserializer d(in);
    double o1, o2, o3, o4, o5;
    d >> o1 >> o2 >> o3 >> o4 >> o5;
    lean_assert_eq(d1, o1);
    lean_assert_eq(d2, o2);
    lean_assert_eq(d3, o3);
    lean_assert_eq(d4, o4);
    lean_assert_eq(d5, o5);
}

int main() {
    save_stack_info();
    initialize_util_module();
    g_list_int_initializer.reset(new list_int_initializer());
    tst1();
    tst2();
    tst3();
    tst4();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
