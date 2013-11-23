/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/interrupt.h"
#include "util/lazy_list.h"
#include "util/list.h"

namespace lean {
template<typename T, typename F>
void for_each(lazy_list<T> l, F && f) {
    while (true) {
        auto p = l.pull();
        if (p) {
            f(p->first);
            l = p->second;
        } else {
            break;
        }
        check_interrupted();
    }
}

template<typename T>
lazy_list<T> take(unsigned sz, lazy_list<T> const & l) {
    if (sz == 0) {
        return lazy_list<T>();
    } else {
        return lazy_list<T>([=]() {
                auto p = l.pull();
                if (p)
                    return some(mk_pair(p->first, take(sz - 1, p->second)));
                else
                    return p;
            });
    }
}

template<typename T>
lazy_list<T> to_lazy(list<T> l) {
    if (l) {
        return lazy_list<T>([=]() {
                return some(mk_pair(head(l), to_lazy(tail(l))));
            });
    } else {
        return lazy_list<T>();
    }
}

template<typename T>
lazy_list<T> append(lazy_list<T> const & l1, lazy_list<T> const & l2) {
    return lazy_list<T>([=]() {
            auto p = l1.pull();
            if (!p) {
                check_interrupted();
                return l2.pull();
            } else {
                return some(mk_pair(p->first, append(p->second, l2)));
            }
        });
}

template<typename T>
lazy_list<T> orelse(lazy_list<T> const & l1, lazy_list<T> const & l2) {
    return lazy_list<T>([=]() {
            auto p = l1.pull();
            if (!p) {
                check_interrupted();
                return l2.pull();
            } else {
                return some(mk_pair(p->first, orelse(p->second, lazy_list<T>())));
            }
        });
}

template<typename T>
lazy_list<T> interleave(lazy_list<T> const & l1, lazy_list<T> const & l2) {
    return lazy_list<T>([=]() {
            auto p = l1.pull();
            if (!p) {
                check_interrupted();
                return l2.pull();
            } else {
                return some(mk_pair(p->first, interleave(l2, p->second)));
            }
        });
}

template<typename T, typename F>
lazy_list<T> map(lazy_list<T> const & l, F && f) {
    return lazy_list<T>([=]() {
            auto p = l.pull();
            if (!p)
                return p;
            else
                return some(mk_pair(f(p->first), map(p->second, f)));
        });
}

template<typename T, typename P>
lazy_list<T> filter(lazy_list<T> const & l, P && pred) {
    return lazy_list<T>([=]() {
            auto p = l.pull();
            if (!p) {
                return p;
            } else if (pred(p->first)) {
                return some(mk_pair(p->first, p->second));
            } else {
                check_interrupted();
                return filter(p->second, pred).pull();
            }
        });
}

template<typename T, typename F>
lazy_list<T> map_append_aux(lazy_list<T> const & h, lazy_list<T> const & l, F && f) {
    return lazy_list<T>([=]() {
            auto p1 = h.pull();
            if (p1) {
                return some(mk_pair(p1->first, map_append_aux(p1->second, l, f)));
            } else {
                check_interrupted();
                auto p2 = l.pull();
                if (p2) {
                    check_interrupted();
                    return map_append_aux(f(p2->first), p2->second, f).pull();
                } else {
                    return typename lazy_list<T>::maybe_pair();
                }
            }
        });
}

template<typename T, typename F>
lazy_list<T> map_append(lazy_list<T> const & l, F && f) {
    return map_append_aux(lazy_list<T>(), l, f);
}
}
