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

/**
   \brief Create a lazy list that contains the first \c sz elements in \c l.
*/
template<typename T>
lazy_list<T> take(unsigned sz, lazy_list<T> const & l) {
    if (sz == 0 || l.is_nil()) {
        return lazy_list<T>();
    } else {
        return mk_lazy_list<T>([=]() {
                auto p = l.pull();
                if (p)
                    return some(mk_pair(p->first, take(sz - 1, p->second)));
                else
                    return p;
            });
    }
}

/**
   \brief Create a lazy list based on the list \c l.
*/
template<typename T>
lazy_list<T> to_lazy(list<T> l) {
    if (l) {
        return mk_lazy_list<T>([=]() {
                return some(mk_pair(head(l), to_lazy(tail(l))));
            });
    } else {
        return lazy_list<T>();
    }
}

/**
   \brief Appends the given lazy lists.
*/
template<typename T>
lazy_list<T> append(lazy_list<T> const & l1, lazy_list<T> const & l2, char const * cname = "lazy list") {
    if (l1.is_nil())
        return l2;
    else if (l2.is_nil())
        return l1;
    else
        return mk_lazy_list<T>([=]() {
                auto p = l1.pull();
                if (!p) {
                    check_system(cname);
                    return l2.pull();
                } else {
                    return some(mk_pair(p->first, append(p->second, l2, cname)));
                }
            });
}

/**
   \brief Return \c l1 if l1 is not empty, and \c l2 otherwise.
*/
template<typename T>
lazy_list<T> orelse(lazy_list<T> const & l1, lazy_list<T> const & l2, char const * cname = "lazy list") {
    if (l1.is_nil())
        return l2;
    else
        return mk_lazy_list<T>([=]() {
                auto p = l1.pull();
                if (!p) {
                    check_system(cname);
                    return l2.pull();
                } else {
                    return p;
                }
            });
}

/**
   \brief "Fair" version of \c append. That is, the elements of \c l1 and \c l2
   are interleaved.
*/
template<typename T>
lazy_list<T> interleave(lazy_list<T> const & l1, lazy_list<T> const & l2, char const * cname = "lazy list") {
    if (l1.is_nil())
        return l2;
    else if (l2.is_nil())
        return l1;
    else
        return mk_lazy_list<T>([=]() {
                auto p = l1.pull();
                if (!p) {
                    check_system(cname);
                    return l2.pull();
                } else {
                    return some(mk_pair(p->first, interleave(l2, p->second, cname)));
                }
            });
}

/**
   \brief Create a lazy list by applying \c f to the elements of \c l.
*/
template<typename T, typename F>
lazy_list<T> map(lazy_list<T> const & l, F && f, char const * cname = "lazy list") {
    if (l.is_nil())
        return l;
    else
        return mk_lazy_list<T>([=]() {
                auto p = l.pull();
                if (!p) {
                    return p;
                } else {
                    check_system(cname);
                    return some(mk_pair(f(p->first), map(p->second, f, cname)));
                }
            });
}

/**
   \brief Create a lazy list by applying \c f to the elements of \c l.
*/
template<typename To, typename From, typename F>
lazy_list<To> map2(lazy_list<From> const & l, F && f, char const * cname = "lazy list") {
    if (l.is_nil())
        return lazy_list<To>();
    else
        return mk_lazy_list<To>([=]() {
                typename lazy_list<From>::maybe_pair p = l.pull();
                if (!p) {
                    return typename lazy_list<To>::maybe_pair();
                } else {
                    check_system(cname);
                    return some(mk_pair(f(p->first), map2<To>(p->second, f, cname)));
                }
            });
}

/**
   \brief Create a lazy list that contains only the elements of \c l that satisfies \c pred.

   \remark Lazy lists may be infinite, and none of them may satisfy \c pred.

   \remark \c check_system() is invoked whenever \c pred returns false.
*/
template<typename T, typename P>
lazy_list<T> filter(lazy_list<T> const & l, P && pred, char const * cname = "lazy list") {
    if (l.is_nil())
        return l;
    else
        return mk_lazy_list<T>([=]() {
                auto p = l.pull();
                if (!p) {
                    return p;
                } else if (pred(p->first)) {
                    return some(mk_pair(p->first, filter(p->second, pred, cname)));
                } else {
                    check_system(cname);
                    return filter(p->second, pred, cname).pull();
                }
            });
}

/**
   \brief Auxiliary template for \c map_append.
*/
template<typename T, typename F>
lazy_list<T> map_append_aux(lazy_list<T> const & h, lazy_list<T> const & l, F && f, char const * cname) {
    return mk_lazy_list<T>([=]() {
            auto p1 = h.pull();
            if (p1) {
                return some(mk_pair(p1->first, map_append_aux(p1->second, l, f, cname)));
            } else {
                check_interrupted();
                auto p2 = l.pull();
                if (p2) {
                    check_system(cname);
                    return map_append_aux(f(p2->first), p2->second, f, cname).pull();
                } else {
                    return typename lazy_list<T>::maybe_pair();
                }
            }
        });
}

/**
   \brief Applies \c f to each element of \c l. The function \c must return a lazy_list.
   All lazy_lists are appended together.
*/
template<typename T, typename F>
lazy_list<T> map_append(lazy_list<T> const & l, F && f, char const * cname = "lazy list") {
    return map_append_aux(lazy_list<T>(), l, f, cname);
}

template<typename T, typename F>
lazy_list<T> repeat(T const & v, F && f, char const * cname = "lazy list") {
    return mk_lazy_list<T>([=]() {
            auto p = f(v).pull();
            if (!p) {
                return some(mk_pair(v, lazy_list<T>()));
            } else {
                check_system(cname);
                return append(repeat(p->first, f, cname),
                              map_append(p->second, [=](T const & v2) { return repeat(v2, f, cname); }, cname), cname).pull();
            }
        });
}

template<typename T, typename F>
lazy_list<T> repeat_at_most(T const & v, F && f, unsigned k, char const * cname = "lazy list") {
    return mk_lazy_list<T>([=]() {
            if (k == 0) {
                return some(mk_pair(v, lazy_list<T>()));
            } else {
                auto p = f(v).pull();
                if (!p) {
                    return some(mk_pair(v, lazy_list<T>()));
                } else {
                    check_system(cname);
                    return append(repeat_at_most(p->first, f, k - 1, cname),
                                  map_append(p->second, [=](T const & v2) { return repeat_at_most(v2, f, k - 1, cname); }, cname),
                                  cname).pull();
                }
            }
        });
}

/**
   \brief Return a lazy list such that only the elements that can be computed in
   less than \c ms milliseconds are kept. That is, it uses a timeout for the \c pull
   method in the class lazy_list. If the \c pull method timeouts, the lazy list
   is truncated.

   \remark the \c method is executed in a separate execution thread.

   \remark \c check_ms is how often the main thread checks whether the child
   thread finished.
*/
#if !defined(LEAN_MULTI_THREAD)
template<typename T>
lazy_list<T> timeout(lazy_list<T> const & l, unsigned, unsigned) {
    return l;
}
#else
template<typename T>
lazy_list<T> timeout(lazy_list<T> const & l, unsigned ms, unsigned check_ms = g_small_sleep) {
    if (check_ms == 0)
        check_ms = 1;
    return mk_lazy_list<T>([=]() {
            typename lazy_list<T>::maybe_pair r;
            atomic<bool> done(false);
            interruptible_thread th([&]() {
                    try {
                        r = l.pull();
                    } catch (...) {
                        r = typename lazy_list<T>::maybe_pair();
                    }
                    done = true;
                });
            try {
                auto start = chrono::steady_clock::now();
                chrono::milliseconds d(ms);
                chrono::milliseconds small(check_ms);
                while (!done) {
                    auto curr = chrono::steady_clock::now();
                    if (chrono::duration_cast<chrono::milliseconds>(curr - start) > d)
                        break;
                    check_interrupted();
                    this_thread::sleep_for(small);
                }
                th.request_interrupt();
                th.join();
                if (r)
                    return some(mk_pair(r->first, timeout(r->second, ms, check_ms)));
                else
                    return r;
            } catch (...) {
                th.request_interrupt();
                th.join();
                throw;
            }
        });
}
#endif

/**
   \brief Similar to interleave, but the heads are computed in parallel.
   Moreover, when pulling results from the lists, if one finishes before the other,
   then the other one is interrupted.
*/
#if !defined(LEAN_MULTI_THREAD)
template<typename T>
lazy_list<T> par(lazy_list<T> const & l1, lazy_list<T> const & l2, unsigned = g_small_sleep) {
    return interleave(l1, l2);
}
#else
template<typename T>
lazy_list<T> par(lazy_list<T> const & l1, lazy_list<T> const & l2, unsigned check_ms = g_small_sleep) {
    return mk_lazy_list<T>([=]() {
            typename lazy_list<T>::maybe_pair r1;
            typename lazy_list<T>::maybe_pair r2;
            atomic<bool>  done1(false);
            atomic<bool>  done2(false);
            interruptible_thread th1([&]() {
                    try {
                        r1 = l1.pull();
                    } catch (...) {
                        r1 = typename lazy_list<T>::maybe_pair();
                    }
                    done1 = true;
                });
            interruptible_thread th2([&]() {
                    try {
                        r2 = l2.pull();
                    } catch (...) {
                        r2 = typename lazy_list<T>::maybe_pair();
                    }
                    done2 = true;
                });
            try {
                chrono::milliseconds small(check_ms);
                while (!done1 && !done2) {
                    check_interrupted();
                    this_thread::sleep_for(small);
                }
                th1.request_interrupt();
                th2.request_interrupt();
                th1.join();
                th2.join();
                if (r1 && r2) {
                    lazy_list<T> tail(r2->first, par(r1->second, r2->second));
                    return some(mk_pair(r1->first, tail));
                } else if (r1) {
                    return some(mk_pair(r1->first, par(r1->second, l2)));
                } else if (r2) {
                    return some(mk_pair(r2->first, par(l1, r2->second)));
                } else {
                    return r2;
                }
            } catch (...) {
                th1.request_interrupt();
                th2.request_interrupt();
                th1.join();
                th2.join();
                throw;
            }
        });
}
#endif
}
