// Check F(I.lower()) \in F(I) and F(I.upper()) \in F(I).
#define check_bop(T, f, i, c) {                                          \
        cout << #f << "(" << #i << " " << i << ", " << c << ") = ";     \
        interval<T> tmp = f(i, c);                                               \
        cout << tmp << endl;                                            \
        if(!i.is_lower_inf()) {                                         \
            numeric_traits<T>::set_rounding(false);                  \
            T l = i.lower();                                            \
            numeric_traits<T>::f(l, c);                         \
            cout << "\t" << #f << "(" << i.lower() << ", " << c << ") = " << l << endl; \
            lean_assert(tmp.is_lower_inf() ||                           \
                        ((tmp.lower() <= l) && (tmp.is_upper_inf() || (l <= tmp.upper())))); \
        }                                                               \
        if(!i.is_upper_inf()) {                                         \
            numeric_traits<T>::set_rounding(true);                   \
            T u = i.upper();                                            \
            numeric_traits<T>::f(u, c);                                     \
            cout << "\t" << #f << "(" << i.upper() << ", " << c << ") = " << u << endl; \
            lean_assert(tmp.is_upper_inf() ||                           \
                        ((tmp.is_lower_inf() || (tmp.lower() <= u)) && (u <= tmp.upper()))); \
        }                                                               \
}

#define check_uop(T, f, i) {                                             \
        cout << #f << "(" << #i << " " << i << ") = ";                  \
        interval<T> tmp = f(i);                                                             \
        cout << tmp << endl;                                            \
        if(!i.is_lower_inf()) {                                         \
            numeric_traits<T>::set_rounding(false);                  \
            T l = i.lower();                                         \
            numeric_traits<T>::f(l);                            \
            cout << "\t" << #f << "(" << i.lower() << ") = " << l << endl; \
            lean_assert(tmp.is_lower_inf() ||                           \
                        ((tmp.lower() <= l) && (tmp.is_upper_inf() || (l <= tmp.upper())))); \
        }                                                               \
        if(!i.is_upper_inf()) {                                         \
            numeric_traits<T>::set_rounding(true);                   \
            T u = i.upper();                                         \
            numeric_traits<T>::f(u);                            \
            cout << "\t" << #f << "(" << i.upper() << ") = " << u << endl; \
            lean_assert(tmp.is_upper_inf() ||                           \
                        ((tmp.is_lower_inf() || (tmp.lower() <= u)) && (u <= tmp.upper()))); \
        }                                                               \
}
