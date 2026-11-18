// Lean compiler output
// Module: Std.Time.Internal.Bounded
// Imports: public import Init.Data.Int.DivMod.Lemmas public import Init.Data.Order.Ord public import Init.Data.Int.Repr public import Init.Omega import Init.Ext
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLE___redArg();
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLE___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLE___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLT___redArg();
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLT___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Time_Internal_Bounded_instOrd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_Bounded_instOrd___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Internal_Bounded_instOrd___redArg___closed__0 = (const lean_object*)&l_Std_Time_Internal_Bounded_instOrd___redArg___closed__0_value;
static const lean_closure_object l_Std_Time_Internal_Bounded_instOrd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Internal_Bounded_instOrd___redArg___closed__1 = (const lean_object*)&l_Std_Time_Internal_Bounded_instOrd___redArg___closed__1_value;
static const lean_closure_object l_Std_Time_Internal_Bounded_instOrd___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Internal_Bounded_instOrd___redArg___closed__1_value),((lean_object*)&l_Std_Time_Internal_Bounded_instOrd___redArg___closed__0_value)} };
static const lean_object* l_Std_Time_Internal_Bounded_instOrd___redArg___closed__2 = (const lean_object*)&l_Std_Time_Internal_Bounded_instOrd___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___redArg();
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Internal_Bounded_instRepr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Internal_Bounded_instRepr___redArg___closed__0 = (const lean_object*)&l_Std_Time_Internal_Bounded_instRepr___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___redArg();
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableEq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableLe___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableLe___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableLe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_ofInt_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_ofInt_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instInhabitedHAddIntCast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instInhabitedHAddIntCast___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_exact(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofInt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofInt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_eq(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_eq___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLE___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLE___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_Time_Internal_Bounded_instLE___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLE(lean_object* v_rel_5_, lean_object* v_n_6_, lean_object* v_m_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLE___boxed(lean_object* v_rel_9_, lean_object* v_n_10_, lean_object* v_m_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_Time_Internal_Bounded_instLE(v_rel_9_, v_n_10_, v_m_11_);
lean_dec(v_m_11_);
lean_dec(v_n_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLT___redArg(){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_box(0);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLT___redArg___boxed(lean_object* v___dummy_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Std_Time_Internal_Bounded_instLT___redArg();
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLT(lean_object* v_rel_17_, lean_object* v_n_18_, lean_object* v_m_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_box(0);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLT___boxed(lean_object* v_rel_21_, lean_object* v_n_22_, lean_object* v_m_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Time_Internal_Bounded_instLT(v_rel_21_, v_n_22_, v_m_23_);
lean_dec(v_m_23_);
lean_dec(v_n_22_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___redArg___lam__0(lean_object* v_x_25_){
_start:
{
lean_inc(v_x_25_);
return v_x_25_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___redArg___lam__0___boxed(lean_object* v_x_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Std_Time_Internal_Bounded_instOrd___redArg___lam__0(v_x_26_);
lean_dec(v_x_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___redArg(){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = ((lean_object*)(l_Std_Time_Internal_Bounded_instOrd___redArg___closed__2));
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___redArg___boxed(lean_object* v___dummy_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Std_Time_Internal_Bounded_instOrd___redArg();
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd(lean_object* v_rel_37_, lean_object* v_n_38_, lean_object* v_m_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = ((lean_object*)(l_Std_Time_Internal_Bounded_instOrd___redArg___closed__2));
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___boxed(lean_object* v_rel_41_, lean_object* v_n_42_, lean_object* v_m_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_Time_Internal_Bounded_instOrd(v_rel_41_, v_n_42_, v_m_43_);
lean_dec(v_m_43_);
lean_dec(v_n_42_);
return v_res_44_;
}
}
static lean_object* _init_l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_nat_to_int(v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0(lean_object* v_n_47_, lean_object* v___y_48_){
_start:
{
lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_49_ = lean_obj_once(&l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0, &l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0_once, _init_l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0);
v___x_50_ = lean_int_dec_lt(v_n_47_, v___x_49_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = l_Int_repr(v_n_47_);
v___x_52_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
else
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = l_Int_repr(v_n_47_);
v___x_54_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
v___x_55_ = l_Repr_addAppParen(v___x_54_, v___y_48_);
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___boxed(lean_object* v_n_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0(v_n_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec(v_n_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___redArg(){
_start:
{
lean_object* v___f_61_; 
v___f_61_ = ((lean_object*)(l_Std_Time_Internal_Bounded_instRepr___redArg___closed__0));
return v___f_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___redArg___boxed(lean_object* v___dummy_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Std_Time_Internal_Bounded_instRepr___redArg();
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr(lean_object* v_rel_64_, lean_object* v_m_65_, lean_object* v_n_66_){
_start:
{
lean_object* v___f_67_; 
v___f_67_ = ((lean_object*)(l_Std_Time_Internal_Bounded_instRepr___redArg___closed__0));
return v___f_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___boxed(lean_object* v_rel_68_, lean_object* v_m_69_, lean_object* v_n_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Std_Time_Internal_Bounded_instRepr(v_rel_68_, v_m_69_, v_n_70_);
lean_dec(v_n_70_);
lean_dec(v_m_69_);
return v_res_71_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableEq___redArg(lean_object* v_a_72_, lean_object* v_b_73_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = lean_int_dec_eq(v_a_72_, v_b_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableEq___redArg___boxed(lean_object* v_a_75_, lean_object* v_b_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_Std_Time_Internal_Bounded_instDecidableEq___redArg(v_a_75_, v_b_76_);
lean_dec(v_b_76_);
lean_dec(v_a_75_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableEq(lean_object* v_rel_79_, lean_object* v_n_80_, lean_object* v_m_81_, lean_object* v_a_82_, lean_object* v_b_83_){
_start:
{
uint8_t v___x_84_; 
v___x_84_ = lean_int_dec_eq(v_a_82_, v_b_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableEq___boxed(lean_object* v_rel_85_, lean_object* v_n_86_, lean_object* v_m_87_, lean_object* v_a_88_, lean_object* v_b_89_){
_start:
{
uint8_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = l_Std_Time_Internal_Bounded_instDecidableEq(v_rel_85_, v_n_86_, v_m_87_, v_a_88_, v_b_89_);
lean_dec(v_b_89_);
lean_dec(v_a_88_);
lean_dec(v_m_87_);
lean_dec(v_n_86_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableLe___redArg(lean_object* v_x_92_, lean_object* v_y_93_){
_start:
{
uint8_t v___x_94_; 
v___x_94_ = lean_int_dec_le(v_x_92_, v_y_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableLe___redArg___boxed(lean_object* v_x_95_, lean_object* v_y_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l_Std_Time_Internal_Bounded_instDecidableLe___redArg(v_x_95_, v_y_96_);
lean_dec(v_y_96_);
lean_dec(v_x_95_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableLe(lean_object* v_rel_99_, lean_object* v_a_100_, lean_object* v_b_101_, lean_object* v_x_102_, lean_object* v_y_103_){
_start:
{
uint8_t v___x_104_; 
v___x_104_ = lean_int_dec_le(v_x_102_, v_y_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableLe___boxed(lean_object* v_rel_105_, lean_object* v_a_106_, lean_object* v_b_107_, lean_object* v_x_108_, lean_object* v_y_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_Std_Time_Internal_Bounded_instDecidableLe(v_rel_105_, v_a_106_, v_b_107_, v_x_108_, v_y_109_);
lean_dec(v_y_109_);
lean_dec(v_x_108_);
lean_dec(v_b_107_);
lean_dec(v_a_106_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast___redArg(lean_object* v_b_112_){
_start:
{
lean_inc(v_b_112_);
return v_b_112_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast___redArg___boxed(lean_object* v_b_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Std_Time_Internal_Bounded_cast___redArg(v_b_113_);
lean_dec(v_b_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast(lean_object* v_rel_115_, lean_object* v_lo_u2081_116_, lean_object* v_lo_u2082_117_, lean_object* v_hi_u2081_118_, lean_object* v_hi_u2082_119_, lean_object* v_h_u2081_120_, lean_object* v_h_u2082_121_, lean_object* v_b_122_){
_start:
{
lean_inc(v_b_122_);
return v_b_122_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast___boxed(lean_object* v_rel_123_, lean_object* v_lo_u2081_124_, lean_object* v_lo_u2082_125_, lean_object* v_hi_u2081_126_, lean_object* v_hi_u2082_127_, lean_object* v_h_u2081_128_, lean_object* v_h_u2082_129_, lean_object* v_b_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Std_Time_Internal_Bounded_cast(v_rel_123_, v_lo_u2081_124_, v_lo_u2082_125_, v_hi_u2081_126_, v_hi_u2082_127_, v_h_u2081_128_, v_h_u2082_129_, v_b_130_);
lean_dec(v_b_130_);
lean_dec(v_hi_u2082_127_);
lean_dec(v_hi_u2081_126_);
lean_dec(v_lo_u2082_125_);
lean_dec(v_lo_u2081_124_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk___redArg(lean_object* v_val_132_){
_start:
{
lean_inc(v_val_132_);
return v_val_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk___redArg___boxed(lean_object* v_val_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Std_Time_Internal_Bounded_mk___redArg(v_val_133_);
lean_dec(v_val_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk(lean_object* v_lo_135_, lean_object* v_hi_136_, lean_object* v_rel_137_, lean_object* v_val_138_, lean_object* v_proof_139_){
_start:
{
lean_inc(v_val_138_);
return v_val_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk___boxed(lean_object* v_lo_140_, lean_object* v_hi_141_, lean_object* v_rel_142_, lean_object* v_val_143_, lean_object* v_proof_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Std_Time_Internal_Bounded_mk(v_lo_140_, v_hi_141_, v_rel_142_, v_val_143_, v_proof_144_);
lean_dec(v_val_143_);
lean_dec(v_hi_141_);
lean_dec(v_lo_140_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_ofInt_x3f___redArg(lean_object* v_lo_146_, lean_object* v_hi_147_, lean_object* v_inst_148_, lean_object* v_val_149_){
_start:
{
lean_object* v___x_150_; uint8_t v___x_151_; 
lean_inc_ref(v_inst_148_);
lean_inc(v_val_149_);
v___x_150_ = lean_apply_2(v_inst_148_, v_lo_146_, v_val_149_);
v___x_151_ = lean_unbox(v___x_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; 
lean_dec(v_val_149_);
lean_dec_ref(v_inst_148_);
lean_dec(v_hi_147_);
v___x_152_ = lean_box(0);
return v___x_152_;
}
else
{
lean_object* v___x_153_; uint8_t v___x_154_; 
lean_inc(v_val_149_);
v___x_153_ = lean_apply_2(v_inst_148_, v_val_149_, v_hi_147_);
v___x_154_ = lean_unbox(v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; 
lean_dec(v_val_149_);
v___x_155_ = lean_box(0);
return v___x_155_;
}
else
{
lean_object* v___x_156_; 
v___x_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_156_, 0, v_val_149_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_ofInt_x3f(lean_object* v_rel_157_, lean_object* v_lo_158_, lean_object* v_hi_159_, lean_object* v_inst_160_, lean_object* v_val_161_){
_start:
{
lean_object* v___x_162_; uint8_t v___x_163_; 
lean_inc_ref(v_inst_160_);
lean_inc(v_val_161_);
v___x_162_ = lean_apply_2(v_inst_160_, v_lo_158_, v_val_161_);
v___x_163_ = lean_unbox(v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; 
lean_dec(v_val_161_);
lean_dec_ref(v_inst_160_);
lean_dec(v_hi_159_);
v___x_164_ = lean_box(0);
return v___x_164_;
}
else
{
lean_object* v___x_165_; uint8_t v___x_166_; 
lean_inc(v_val_161_);
v___x_165_ = lean_apply_2(v_inst_160_, v_val_161_, v_hi_159_);
v___x_166_ = lean_unbox(v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; 
lean_dec(v_val_161_);
v___x_167_ = lean_box(0);
return v___x_167_;
}
else
{
lean_object* v___x_168_; 
v___x_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_168_, 0, v_val_161_);
return v___x_168_;
}
}
}
}
static lean_object* _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = lean_nat_to_int(v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg(lean_object* v_lo_171_, lean_object* v_hi_172_, lean_object* v_val_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v_range_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_174_ = lean_int_sub(v_hi_172_, v_lo_171_);
v___x_175_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v_range_176_ = lean_int_add(v___x_174_, v___x_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_int_sub(v_val_173_, v_lo_171_);
v___x_178_ = lean_int_emod(v___x_177_, v_range_176_);
lean_dec(v___x_177_);
v___x_179_ = lean_int_add(v___x_178_, v_range_176_);
lean_dec(v___x_178_);
v___x_180_ = lean_int_emod(v___x_179_, v_range_176_);
lean_dec(v_range_176_);
lean_dec(v___x_179_);
v___x_181_ = lean_int_add(v___x_180_, v_lo_171_);
lean_dec(v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___boxed(lean_object* v_lo_182_, lean_object* v_hi_183_, lean_object* v_val_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg(v_lo_182_, v_hi_183_, v_val_184_);
lean_dec(v_val_184_);
lean_dec(v_hi_183_);
lean_dec(v_lo_182_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping(lean_object* v_lo_186_, lean_object* v_hi_187_, lean_object* v_val_188_, lean_object* v_h_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v_range_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_190_ = lean_int_sub(v_hi_187_, v_lo_186_);
v___x_191_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v_range_192_ = lean_int_add(v___x_190_, v___x_191_);
lean_dec(v___x_190_);
v___x_193_ = lean_int_sub(v_val_188_, v_lo_186_);
v___x_194_ = lean_int_emod(v___x_193_, v_range_192_);
lean_dec(v___x_193_);
v___x_195_ = lean_int_add(v___x_194_, v_range_192_);
lean_dec(v___x_194_);
v___x_196_ = lean_int_emod(v___x_195_, v_range_192_);
lean_dec(v_range_192_);
lean_dec(v___x_195_);
v___x_197_ = lean_int_add(v___x_196_, v_lo_186_);
lean_dec(v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping___boxed(lean_object* v_lo_198_, lean_object* v_hi_199_, lean_object* v_val_200_, lean_object* v_h_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Std_Time_Internal_Bounded_LE_ofNatWrapping(v_lo_198_, v_hi_199_, v_val_200_, v_h_201_);
lean_dec(v_val_200_);
lean_dec(v_hi_199_);
lean_dec(v_lo_198_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(lean_object* v_lo_203_, lean_object* v_n_204_, lean_object* v_k_205_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v_range_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_206_ = lean_nat_to_int(v_k_205_);
v___x_207_ = lean_int_add(v_lo_203_, v___x_206_);
lean_dec(v___x_206_);
v___x_208_ = lean_nat_to_int(v_n_204_);
v___x_209_ = lean_int_sub(v___x_207_, v_lo_203_);
lean_dec(v___x_207_);
v___x_210_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v_range_211_ = lean_int_add(v___x_209_, v___x_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_int_sub(v___x_208_, v_lo_203_);
lean_dec(v___x_208_);
v___x_213_ = lean_int_emod(v___x_212_, v_range_211_);
lean_dec(v___x_212_);
v___x_214_ = lean_int_add(v___x_213_, v_range_211_);
lean_dec(v___x_213_);
v___x_215_ = lean_int_emod(v___x_214_, v_range_211_);
lean_dec(v_range_211_);
lean_dec(v___x_214_);
v___x_216_ = lean_int_add(v___x_215_, v_lo_203_);
lean_dec(v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast___boxed(lean_object* v_lo_217_, lean_object* v_n_218_, lean_object* v_k_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(v_lo_217_, v_n_218_, v_k_219_);
lean_dec(v_lo_217_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instInhabitedHAddIntCast(lean_object* v_lo_221_, lean_object* v_k_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v_range_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_223_ = lean_nat_to_int(v_k_222_);
v___x_224_ = lean_int_add(v_lo_221_, v___x_223_);
lean_dec(v___x_223_);
v___x_225_ = lean_int_sub(v___x_224_, v_lo_221_);
lean_dec(v___x_224_);
v___x_226_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v_range_227_ = lean_int_add(v___x_225_, v___x_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_int_sub(v_lo_221_, v_lo_221_);
v___x_229_ = lean_int_emod(v___x_228_, v_range_227_);
lean_dec(v___x_228_);
v___x_230_ = lean_int_add(v___x_229_, v_range_227_);
lean_dec(v___x_229_);
v___x_231_ = lean_int_emod(v___x_230_, v_range_227_);
lean_dec(v_range_227_);
lean_dec(v___x_230_);
v___x_232_ = lean_int_add(v___x_231_, v_lo_221_);
lean_dec(v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instInhabitedHAddIntCast___boxed(lean_object* v_lo_233_, lean_object* v_k_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Std_Time_Internal_Bounded_LE_instInhabitedHAddIntCast(v_lo_233_, v_k_234_);
lean_dec(v_lo_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk___redArg(lean_object* v_val_236_){
_start:
{
lean_inc(v_val_236_);
return v_val_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk___redArg___boxed(lean_object* v_val_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Std_Time_Internal_Bounded_LE_mk___redArg(v_val_237_);
lean_dec(v_val_237_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk(lean_object* v_lo_239_, lean_object* v_hi_240_, lean_object* v_val_241_, lean_object* v_proof_242_){
_start:
{
lean_inc(v_val_241_);
return v_val_241_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk___boxed(lean_object* v_lo_243_, lean_object* v_hi_244_, lean_object* v_val_245_, lean_object* v_proof_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Std_Time_Internal_Bounded_LE_mk(v_lo_243_, v_hi_244_, v_val_245_, v_proof_246_);
lean_dec(v_val_245_);
lean_dec(v_hi_244_);
lean_dec(v_lo_243_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_exact(lean_object* v_val_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = lean_nat_to_int(v_val_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofInt(lean_object* v_lo_250_, lean_object* v_hi_251_, lean_object* v_val_252_){
_start:
{
uint8_t v___x_253_; 
v___x_253_ = lean_int_dec_le(v_lo_250_, v_val_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
lean_dec(v_val_252_);
v___x_254_ = lean_box(0);
return v___x_254_;
}
else
{
uint8_t v___x_255_; 
v___x_255_ = lean_int_dec_le(v_val_252_, v_hi_251_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
lean_dec(v_val_252_);
v___x_256_ = lean_box(0);
return v___x_256_;
}
else
{
lean_object* v___x_257_; 
v___x_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_257_, 0, v_val_252_);
return v___x_257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofInt___boxed(lean_object* v_lo_258_, lean_object* v_hi_259_, lean_object* v_val_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_Time_Internal_Bounded_LE_ofInt(v_lo_258_, v_hi_259_, v_val_260_);
lean_dec(v_hi_259_);
lean_dec(v_lo_258_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat___redArg(lean_object* v_val_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lean_nat_to_int(v_val_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat(lean_object* v_hi_264_, lean_object* v_val_265_, lean_object* v_h_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lean_nat_to_int(v_val_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat___boxed(lean_object* v_hi_268_, lean_object* v_val_269_, lean_object* v_h_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Std_Time_Internal_Bounded_LE_ofNat(v_hi_268_, v_val_269_, v_h_270_);
lean_dec(v_hi_268_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x3f(lean_object* v_hi_272_, lean_object* v_val_273_){
_start:
{
uint8_t v___x_274_; 
v___x_274_ = lean_nat_dec_le(v_val_273_, v_hi_272_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
lean_dec(v_val_273_);
v___x_275_ = lean_box(0);
return v___x_275_;
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_nat_to_int(v_val_273_);
v___x_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x3f___boxed(lean_object* v_hi_278_, lean_object* v_val_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Std_Time_Internal_Bounded_LE_ofNat_x3f(v_hi_278_, v_val_279_);
lean_dec(v_hi_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27___redArg(lean_object* v_val_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = lean_nat_to_int(v_val_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27(lean_object* v_lo_283_, lean_object* v_hi_284_, lean_object* v_val_285_, lean_object* v_h_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_nat_to_int(v_val_285_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27___boxed(lean_object* v_lo_288_, lean_object* v_hi_289_, lean_object* v_val_290_, lean_object* v_h_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Std_Time_Internal_Bounded_LE_ofNat_x27(v_lo_288_, v_hi_289_, v_val_290_, v_h_291_);
lean_dec(v_hi_289_);
lean_dec(v_lo_288_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___redArg(lean_object* v_lo_293_, lean_object* v_hi_294_, lean_object* v_val_295_){
_start:
{
uint8_t v___x_296_; 
v___x_296_ = lean_int_dec_le(v_lo_293_, v_val_295_);
if (v___x_296_ == 0)
{
lean_inc(v_lo_293_);
return v_lo_293_;
}
else
{
uint8_t v___x_297_; 
v___x_297_ = lean_int_dec_le(v_val_295_, v_hi_294_);
if (v___x_297_ == 0)
{
lean_inc(v_hi_294_);
return v_hi_294_;
}
else
{
lean_inc(v_val_295_);
return v_val_295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___redArg___boxed(lean_object* v_lo_298_, lean_object* v_hi_299_, lean_object* v_val_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Std_Time_Internal_Bounded_LE_clip___redArg(v_lo_298_, v_hi_299_, v_val_300_);
lean_dec(v_val_300_);
lean_dec(v_hi_299_);
lean_dec(v_lo_298_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip(lean_object* v_lo_302_, lean_object* v_hi_303_, lean_object* v_val_304_, lean_object* v_h_305_){
_start:
{
uint8_t v___x_306_; 
v___x_306_ = lean_int_dec_le(v_lo_302_, v_val_304_);
if (v___x_306_ == 0)
{
lean_inc(v_lo_302_);
return v_lo_302_;
}
else
{
uint8_t v___x_307_; 
v___x_307_ = lean_int_dec_le(v_val_304_, v_hi_303_);
if (v___x_307_ == 0)
{
lean_inc(v_hi_303_);
return v_hi_303_;
}
else
{
lean_inc(v_val_304_);
return v_val_304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___boxed(lean_object* v_lo_308_, lean_object* v_hi_309_, lean_object* v_val_310_, lean_object* v_h_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_Time_Internal_Bounded_LE_clip(v_lo_308_, v_hi_309_, v_val_310_, v_h_311_);
lean_dec(v_val_310_);
lean_dec(v_hi_309_);
lean_dec(v_lo_308_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___redArg(lean_object* v_n_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Int_toNat(v_n_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___redArg___boxed(lean_object* v_n_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Std_Time_Internal_Bounded_LE_toNat___redArg(v_n_315_);
lean_dec(v_n_315_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat(lean_object* v_lo_317_, lean_object* v_hi_318_, lean_object* v_n_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Int_toNat(v_n_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___boxed(lean_object* v_lo_321_, lean_object* v_hi_322_, lean_object* v_n_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Std_Time_Internal_Bounded_LE_toNat(v_lo_321_, v_hi_322_, v_n_323_);
lean_dec(v_n_323_);
lean_dec(v_hi_322_);
lean_dec(v_lo_321_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg(lean_object* v_n_325_){
_start:
{
lean_object* v_intZero_326_; uint8_t v_isNeg_327_; lean_object* v_a_328_; 
v_intZero_326_ = lean_obj_once(&l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0, &l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0_once, _init_l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0);
v_isNeg_327_ = lean_int_dec_lt(v_n_325_, v_intZero_326_);
v_a_328_ = lean_nat_abs(v_n_325_);
return v_a_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg___boxed(lean_object* v_n_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg(v_n_329_);
lean_dec(v_n_329_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27(lean_object* v_lo_331_, lean_object* v_hi_332_, lean_object* v_n_333_, lean_object* v_h_334_){
_start:
{
lean_object* v_intZero_335_; uint8_t v_isNeg_336_; lean_object* v_a_337_; 
v_intZero_335_ = lean_obj_once(&l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0, &l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0_once, _init_l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0);
v_isNeg_336_ = lean_int_dec_lt(v_n_333_, v_intZero_335_);
v_a_337_ = lean_nat_abs(v_n_333_);
return v_a_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___boxed(lean_object* v_lo_338_, lean_object* v_hi_339_, lean_object* v_n_340_, lean_object* v_h_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_Time_Internal_Bounded_LE_toNat_x27(v_lo_338_, v_hi_339_, v_n_340_, v_h_341_);
lean_dec(v_n_340_);
lean_dec(v_hi_339_);
lean_dec(v_lo_338_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___redArg(lean_object* v_n_343_){
_start:
{
lean_inc(v_n_343_);
return v_n_343_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___redArg___boxed(lean_object* v_n_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Std_Time_Internal_Bounded_LE_toInt___redArg(v_n_344_);
lean_dec(v_n_344_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt(lean_object* v_lo_346_, lean_object* v_hi_347_, lean_object* v_n_348_){
_start:
{
lean_inc(v_n_348_);
return v_n_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___boxed(lean_object* v_lo_349_, lean_object* v_hi_350_, lean_object* v_n_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_Time_Internal_Bounded_LE_toInt(v_lo_349_, v_hi_350_, v_n_351_);
lean_dec(v_n_351_);
lean_dec(v_hi_350_);
lean_dec(v_lo_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___redArg(lean_object* v_n_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Int_toNat(v_n_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___redArg___boxed(lean_object* v_n_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Std_Time_Internal_Bounded_LE_toFin___redArg(v_n_355_);
lean_dec(v_n_355_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin(lean_object* v_lo_357_, lean_object* v_hi_358_, lean_object* v_n_359_, lean_object* v_h_u2080_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Int_toNat(v_n_359_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___boxed(lean_object* v_lo_362_, lean_object* v_hi_363_, lean_object* v_n_364_, lean_object* v_h_u2080_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Std_Time_Internal_Bounded_LE_toFin(v_lo_362_, v_hi_363_, v_n_364_, v_h_u2080_365_);
lean_dec(v_n_364_);
lean_dec(v_hi_363_);
lean_dec(v_lo_362_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin___redArg(lean_object* v_fin_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = lean_nat_to_int(v_fin_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin(lean_object* v_hi_369_, lean_object* v_fin_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_nat_to_int(v_fin_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin___boxed(lean_object* v_hi_372_, lean_object* v_fin_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Std_Time_Internal_Bounded_LE_ofFin(v_hi_372_, v_fin_373_);
lean_dec(v_hi_372_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27___redArg(lean_object* v_lo_375_, lean_object* v_fin_376_){
_start:
{
uint8_t v___x_377_; 
v___x_377_ = lean_nat_dec_le(v_lo_375_, v_fin_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
lean_dec(v_fin_376_);
v___x_378_ = lean_nat_to_int(v_lo_375_);
return v___x_378_;
}
else
{
lean_object* v___x_379_; 
lean_dec(v_lo_375_);
v___x_379_ = lean_nat_to_int(v_fin_376_);
return v___x_379_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27(lean_object* v_hi_380_, lean_object* v_lo_381_, lean_object* v_fin_382_, lean_object* v_h_383_){
_start:
{
uint8_t v___x_384_; 
v___x_384_ = lean_nat_dec_le(v_lo_381_, v_fin_382_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; 
lean_dec(v_fin_382_);
v___x_385_ = lean_nat_to_int(v_lo_381_);
return v___x_385_;
}
else
{
lean_object* v___x_386_; 
lean_dec(v_lo_381_);
v___x_386_ = lean_nat_to_int(v_fin_382_);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27___boxed(lean_object* v_hi_387_, lean_object* v_lo_388_, lean_object* v_fin_389_, lean_object* v_h_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Std_Time_Internal_Bounded_LE_ofFin_x27(v_hi_387_, v_lo_388_, v_fin_389_, v_h_390_);
lean_dec(v_hi_387_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___redArg(lean_object* v_b_392_, lean_object* v_i_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = lean_int_emod(v_b_392_, v_i_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___redArg___boxed(lean_object* v_b_395_, lean_object* v_i_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Std_Time_Internal_Bounded_LE_byEmod___redArg(v_b_395_, v_i_396_);
lean_dec(v_i_396_);
lean_dec(v_b_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod(lean_object* v_b_398_, lean_object* v_i_399_, lean_object* v_hi_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = lean_int_emod(v_b_398_, v_i_399_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___boxed(lean_object* v_b_402_, lean_object* v_i_403_, lean_object* v_hi_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_Time_Internal_Bounded_LE_byEmod(v_b_402_, v_i_403_, v_hi_404_);
lean_dec(v_i_403_);
lean_dec(v_b_402_);
return v_res_405_;
}
}
static lean_object* _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_406_; lean_object* v_intZero_407_; 
v_natZero_406_ = lean_unsigned_to_nat(0u);
v_intZero_407_ = lean_nat_to_int(v_natZero_406_);
return v_intZero_407_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg(lean_object* v_x_408_, lean_object* v_x_409_, lean_object* v_h__1_410_, lean_object* v_h__2_411_, lean_object* v_h__3_412_, lean_object* v_h__4_413_){
_start:
{
lean_object* v_intZero_414_; uint8_t v_isNeg_415_; 
v_intZero_414_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v_isNeg_415_ = lean_int_dec_lt(v_x_408_, v_intZero_414_);
if (v_isNeg_415_ == 0)
{
lean_object* v_a_416_; uint8_t v_isNeg_417_; 
lean_dec(v_h__4_413_);
lean_dec(v_h__3_412_);
v_a_416_ = lean_nat_abs(v_x_408_);
v_isNeg_417_ = lean_int_dec_lt(v_x_409_, v_intZero_414_);
if (v_isNeg_417_ == 0)
{
lean_object* v_a_418_; lean_object* v___x_419_; 
lean_dec(v_h__2_411_);
v_a_418_ = lean_nat_abs(v_x_409_);
v___x_419_ = lean_apply_2(v_h__1_410_, v_a_416_, v_a_418_);
return v___x_419_;
}
else
{
lean_object* v_abs_420_; lean_object* v_one_421_; lean_object* v_a_422_; lean_object* v___x_423_; 
lean_dec(v_h__1_410_);
v_abs_420_ = lean_nat_abs(v_x_409_);
v_one_421_ = lean_unsigned_to_nat(1u);
v_a_422_ = lean_nat_sub(v_abs_420_, v_one_421_);
lean_dec(v_abs_420_);
v___x_423_ = lean_apply_2(v_h__2_411_, v_a_416_, v_a_422_);
return v___x_423_;
}
}
else
{
lean_object* v_abs_424_; lean_object* v_one_425_; lean_object* v_a_426_; uint8_t v_isNeg_427_; 
lean_dec(v_h__2_411_);
lean_dec(v_h__1_410_);
v_abs_424_ = lean_nat_abs(v_x_408_);
v_one_425_ = lean_unsigned_to_nat(1u);
v_a_426_ = lean_nat_sub(v_abs_424_, v_one_425_);
lean_dec(v_abs_424_);
v_isNeg_427_ = lean_int_dec_lt(v_x_409_, v_intZero_414_);
if (v_isNeg_427_ == 0)
{
lean_object* v_a_428_; lean_object* v___x_429_; 
lean_dec(v_h__4_413_);
v_a_428_ = lean_nat_abs(v_x_409_);
v___x_429_ = lean_apply_2(v_h__3_412_, v_a_426_, v_a_428_);
return v___x_429_;
}
else
{
lean_object* v_abs_430_; lean_object* v_a_431_; lean_object* v___x_432_; 
lean_dec(v_h__3_412_);
v_abs_430_ = lean_nat_abs(v_x_409_);
v_a_431_ = lean_nat_sub(v_abs_430_, v_one_425_);
lean_dec(v_abs_430_);
v___x_432_ = lean_apply_2(v_h__4_413_, v_a_426_, v_a_431_);
return v___x_432_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___boxed(lean_object* v_x_433_, lean_object* v_x_434_, lean_object* v_h__1_435_, lean_object* v_h__2_436_, lean_object* v_h__3_437_, lean_object* v_h__4_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg(v_x_433_, v_x_434_, v_h__1_435_, v_h__2_436_, v_h__3_437_, v_h__4_438_);
lean_dec(v_x_434_);
lean_dec(v_x_433_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter(lean_object* v_motive_440_, lean_object* v_x_441_, lean_object* v_x_442_, lean_object* v_h__1_443_, lean_object* v_h__2_444_, lean_object* v_h__3_445_, lean_object* v_h__4_446_){
_start:
{
lean_object* v_intZero_447_; uint8_t v_isNeg_448_; 
v_intZero_447_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v_isNeg_448_ = lean_int_dec_lt(v_x_441_, v_intZero_447_);
if (v_isNeg_448_ == 0)
{
lean_object* v_a_449_; uint8_t v_isNeg_450_; 
lean_dec(v_h__4_446_);
lean_dec(v_h__3_445_);
v_a_449_ = lean_nat_abs(v_x_441_);
v_isNeg_450_ = lean_int_dec_lt(v_x_442_, v_intZero_447_);
if (v_isNeg_450_ == 0)
{
lean_object* v_a_451_; lean_object* v___x_452_; 
lean_dec(v_h__2_444_);
v_a_451_ = lean_nat_abs(v_x_442_);
v___x_452_ = lean_apply_2(v_h__1_443_, v_a_449_, v_a_451_);
return v___x_452_;
}
else
{
lean_object* v_abs_453_; lean_object* v_one_454_; lean_object* v_a_455_; lean_object* v___x_456_; 
lean_dec(v_h__1_443_);
v_abs_453_ = lean_nat_abs(v_x_442_);
v_one_454_ = lean_unsigned_to_nat(1u);
v_a_455_ = lean_nat_sub(v_abs_453_, v_one_454_);
lean_dec(v_abs_453_);
v___x_456_ = lean_apply_2(v_h__2_444_, v_a_449_, v_a_455_);
return v___x_456_;
}
}
else
{
lean_object* v_abs_457_; lean_object* v_one_458_; lean_object* v_a_459_; uint8_t v_isNeg_460_; 
lean_dec(v_h__2_444_);
lean_dec(v_h__1_443_);
v_abs_457_ = lean_nat_abs(v_x_441_);
v_one_458_ = lean_unsigned_to_nat(1u);
v_a_459_ = lean_nat_sub(v_abs_457_, v_one_458_);
lean_dec(v_abs_457_);
v_isNeg_460_ = lean_int_dec_lt(v_x_442_, v_intZero_447_);
if (v_isNeg_460_ == 0)
{
lean_object* v_a_461_; lean_object* v___x_462_; 
lean_dec(v_h__4_446_);
v_a_461_ = lean_nat_abs(v_x_442_);
v___x_462_ = lean_apply_2(v_h__3_445_, v_a_459_, v_a_461_);
return v___x_462_;
}
else
{
lean_object* v_abs_463_; lean_object* v_a_464_; lean_object* v___x_465_; 
lean_dec(v_h__3_445_);
v_abs_463_ = lean_nat_abs(v_x_442_);
v_a_464_ = lean_nat_sub(v_abs_463_, v_one_458_);
lean_dec(v_abs_463_);
v___x_465_ = lean_apply_2(v_h__4_446_, v_a_459_, v_a_464_);
return v___x_465_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___boxed(lean_object* v_motive_466_, lean_object* v_x_467_, lean_object* v_x_468_, lean_object* v_h__1_469_, lean_object* v_h__2_470_, lean_object* v_h__3_471_, lean_object* v_h__4_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter(v_motive_466_, v_x_467_, v_x_468_, v_h__1_469_, v_h__2_470_, v_h__3_471_, v_h__4_472_);
lean_dec(v_x_468_);
lean_dec(v_x_467_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___redArg(lean_object* v_b_474_, lean_object* v_i_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = lean_int_mod(v_b_474_, v_i_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___redArg___boxed(lean_object* v_b_477_, lean_object* v_i_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Std_Time_Internal_Bounded_LE_byMod___redArg(v_b_477_, v_i_478_);
lean_dec(v_i_478_);
lean_dec(v_b_477_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod(lean_object* v_b_480_, lean_object* v_i_481_, lean_object* v_hi_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = lean_int_mod(v_b_480_, v_i_481_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___boxed(lean_object* v_b_484_, lean_object* v_i_485_, lean_object* v_hi_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Std_Time_Internal_Bounded_LE_byMod(v_b_484_, v_i_485_, v_hi_486_);
lean_dec(v_i_485_);
lean_dec(v_b_484_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___redArg(lean_object* v_n_488_, lean_object* v_bounded_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = lean_int_sub(v_bounded_489_, v_n_488_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___redArg___boxed(lean_object* v_n_491_, lean_object* v_bounded_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_Time_Internal_Bounded_LE_truncate___redArg(v_n_491_, v_bounded_492_);
lean_dec(v_bounded_492_);
lean_dec(v_n_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate(lean_object* v_n_494_, lean_object* v_m_495_, lean_object* v_bounded_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = lean_int_sub(v_bounded_496_, v_n_494_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___boxed(lean_object* v_n_498_, lean_object* v_m_499_, lean_object* v_bounded_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Std_Time_Internal_Bounded_LE_truncate(v_n_498_, v_m_499_, v_bounded_500_);
lean_dec(v_bounded_500_);
lean_dec(v_m_499_);
lean_dec(v_n_498_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___redArg(lean_object* v_bounded_502_){
_start:
{
lean_inc(v_bounded_502_);
return v_bounded_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___redArg___boxed(lean_object* v_bounded_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Std_Time_Internal_Bounded_LE_truncateTop___redArg(v_bounded_503_);
lean_dec(v_bounded_503_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop(lean_object* v_n_505_, lean_object* v_m_506_, lean_object* v_j_507_, lean_object* v_bounded_508_, lean_object* v_h_509_){
_start:
{
lean_inc(v_bounded_508_);
return v_bounded_508_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___boxed(lean_object* v_n_510_, lean_object* v_m_511_, lean_object* v_j_512_, lean_object* v_bounded_513_, lean_object* v_h_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Std_Time_Internal_Bounded_LE_truncateTop(v_n_510_, v_m_511_, v_j_512_, v_bounded_513_, v_h_514_);
lean_dec(v_bounded_513_);
lean_dec(v_j_512_);
lean_dec(v_m_511_);
lean_dec(v_n_510_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg(lean_object* v_bounded_516_){
_start:
{
lean_inc(v_bounded_516_);
return v_bounded_516_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg___boxed(lean_object* v_bounded_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg(v_bounded_517_);
lean_dec(v_bounded_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom(lean_object* v_n_519_, lean_object* v_m_520_, lean_object* v_j_521_, lean_object* v_bounded_522_, lean_object* v_h_523_){
_start:
{
lean_inc(v_bounded_522_);
return v_bounded_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___boxed(lean_object* v_n_524_, lean_object* v_m_525_, lean_object* v_j_526_, lean_object* v_bounded_527_, lean_object* v_h_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Std_Time_Internal_Bounded_LE_truncateBottom(v_n_524_, v_m_525_, v_j_526_, v_bounded_527_, v_h_528_);
lean_dec(v_bounded_527_);
lean_dec(v_j_526_);
lean_dec(v_m_525_);
lean_dec(v_n_524_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___redArg(lean_object* v_bounded_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = lean_int_neg(v_bounded_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___redArg___boxed(lean_object* v_bounded_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_Time_Internal_Bounded_LE_neg___redArg(v_bounded_532_);
lean_dec(v_bounded_532_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg(lean_object* v_n_534_, lean_object* v_m_535_, lean_object* v_bounded_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = lean_int_neg(v_bounded_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___boxed(lean_object* v_n_538_, lean_object* v_m_539_, lean_object* v_bounded_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_Time_Internal_Bounded_LE_neg(v_n_538_, v_m_539_, v_bounded_540_);
lean_dec(v_bounded_540_);
lean_dec(v_m_539_);
lean_dec(v_n_538_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___redArg(lean_object* v_bounded_542_, lean_object* v_num_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = lean_int_add(v_bounded_542_, v_num_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___redArg___boxed(lean_object* v_bounded_545_, lean_object* v_num_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Std_Time_Internal_Bounded_LE_add___redArg(v_bounded_545_, v_num_546_);
lean_dec(v_num_546_);
lean_dec(v_bounded_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add(lean_object* v_n_548_, lean_object* v_m_549_, lean_object* v_bounded_550_, lean_object* v_num_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = lean_int_add(v_bounded_550_, v_num_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___boxed(lean_object* v_n_553_, lean_object* v_m_554_, lean_object* v_bounded_555_, lean_object* v_num_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Std_Time_Internal_Bounded_LE_add(v_n_553_, v_m_554_, v_bounded_555_, v_num_556_);
lean_dec(v_num_556_);
lean_dec(v_bounded_555_);
lean_dec(v_m_554_);
lean_dec(v_n_553_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___redArg(lean_object* v_num_558_, lean_object* v_bounded_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = lean_int_add(v_bounded_559_, v_num_558_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___redArg___boxed(lean_object* v_num_561_, lean_object* v_bounded_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Std_Time_Internal_Bounded_LE_addProven___redArg(v_num_561_, v_bounded_562_);
lean_dec(v_bounded_562_);
lean_dec(v_num_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven(lean_object* v_n_564_, lean_object* v_m_565_, lean_object* v_num_566_, lean_object* v_bounded_567_, lean_object* v_h_u2080_568_, lean_object* v_h_u2081_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = lean_int_add(v_bounded_567_, v_num_566_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___boxed(lean_object* v_n_571_, lean_object* v_m_572_, lean_object* v_num_573_, lean_object* v_bounded_574_, lean_object* v_h_u2080_575_, lean_object* v_h_u2081_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Std_Time_Internal_Bounded_LE_addProven(v_n_571_, v_m_572_, v_num_573_, v_bounded_574_, v_h_u2080_575_, v_h_u2081_576_);
lean_dec(v_bounded_574_);
lean_dec(v_num_573_);
lean_dec(v_m_572_);
lean_dec(v_n_571_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___redArg(lean_object* v_bounded_578_, lean_object* v_num_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = lean_int_add(v_bounded_578_, v_num_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___redArg___boxed(lean_object* v_bounded_581_, lean_object* v_num_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_Time_Internal_Bounded_LE_addTop___redArg(v_bounded_581_, v_num_582_);
lean_dec(v_num_582_);
lean_dec(v_bounded_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop(lean_object* v_n_584_, lean_object* v_m_585_, lean_object* v_bounded_586_, lean_object* v_num_587_, lean_object* v_h_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = lean_int_add(v_bounded_586_, v_num_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___boxed(lean_object* v_n_590_, lean_object* v_m_591_, lean_object* v_bounded_592_, lean_object* v_num_593_, lean_object* v_h_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Std_Time_Internal_Bounded_LE_addTop(v_n_590_, v_m_591_, v_bounded_592_, v_num_593_, v_h_594_);
lean_dec(v_num_593_);
lean_dec(v_bounded_592_);
lean_dec(v_m_591_);
lean_dec(v_n_590_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___redArg(lean_object* v_bounded_596_, lean_object* v_num_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = lean_int_sub(v_bounded_596_, v_num_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___redArg___boxed(lean_object* v_bounded_599_, lean_object* v_num_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_Time_Internal_Bounded_LE_subBottom___redArg(v_bounded_599_, v_num_600_);
lean_dec(v_num_600_);
lean_dec(v_bounded_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom(lean_object* v_n_602_, lean_object* v_m_603_, lean_object* v_bounded_604_, lean_object* v_num_605_, lean_object* v_h_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = lean_int_sub(v_bounded_604_, v_num_605_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___boxed(lean_object* v_n_608_, lean_object* v_m_609_, lean_object* v_bounded_610_, lean_object* v_num_611_, lean_object* v_h_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Std_Time_Internal_Bounded_LE_subBottom(v_n_608_, v_m_609_, v_bounded_610_, v_num_611_, v_h_612_);
lean_dec(v_num_611_);
lean_dec(v_bounded_610_);
lean_dec(v_m_609_);
lean_dec(v_n_608_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___redArg(lean_object* v_bounded_614_, lean_object* v_bounded_u2082_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = lean_int_add(v_bounded_614_, v_bounded_u2082_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___redArg___boxed(lean_object* v_bounded_617_, lean_object* v_bounded_u2082_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Std_Time_Internal_Bounded_LE_addBounds___redArg(v_bounded_617_, v_bounded_u2082_618_);
lean_dec(v_bounded_u2082_618_);
lean_dec(v_bounded_617_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds(lean_object* v_n_620_, lean_object* v_m_621_, lean_object* v_i_622_, lean_object* v_j_623_, lean_object* v_bounded_624_, lean_object* v_bounded_u2082_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = lean_int_add(v_bounded_624_, v_bounded_u2082_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___boxed(lean_object* v_n_627_, lean_object* v_m_628_, lean_object* v_i_629_, lean_object* v_j_630_, lean_object* v_bounded_631_, lean_object* v_bounded_u2082_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Std_Time_Internal_Bounded_LE_addBounds(v_n_627_, v_m_628_, v_i_629_, v_j_630_, v_bounded_631_, v_bounded_u2082_632_);
lean_dec(v_bounded_u2082_632_);
lean_dec(v_bounded_631_);
lean_dec(v_j_630_);
lean_dec(v_i_629_);
lean_dec(v_m_628_);
lean_dec(v_n_627_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___redArg(lean_object* v_bounded_634_, lean_object* v_num_635_){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_int_neg(v_num_635_);
v___x_637_ = lean_int_add(v_bounded_634_, v___x_636_);
lean_dec(v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___redArg___boxed(lean_object* v_bounded_638_, lean_object* v_num_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Std_Time_Internal_Bounded_LE_sub___redArg(v_bounded_638_, v_num_639_);
lean_dec(v_num_639_);
lean_dec(v_bounded_638_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub(lean_object* v_n_641_, lean_object* v_m_642_, lean_object* v_bounded_643_, lean_object* v_num_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_int_neg(v_num_644_);
v___x_646_ = lean_int_add(v_bounded_643_, v___x_645_);
lean_dec(v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___boxed(lean_object* v_n_647_, lean_object* v_m_648_, lean_object* v_bounded_649_, lean_object* v_num_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_Time_Internal_Bounded_LE_sub(v_n_647_, v_m_648_, v_bounded_649_, v_num_650_);
lean_dec(v_num_650_);
lean_dec(v_bounded_649_);
lean_dec(v_m_648_);
lean_dec(v_n_647_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___redArg(lean_object* v_bounded_652_, lean_object* v_bounded_u2082_653_){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_int_neg(v_bounded_u2082_653_);
v___x_655_ = lean_int_add(v_bounded_652_, v___x_654_);
lean_dec(v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___redArg___boxed(lean_object* v_bounded_656_, lean_object* v_bounded_u2082_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Std_Time_Internal_Bounded_LE_subBounds___redArg(v_bounded_656_, v_bounded_u2082_657_);
lean_dec(v_bounded_u2082_657_);
lean_dec(v_bounded_656_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds(lean_object* v_n_659_, lean_object* v_m_660_, lean_object* v_i_661_, lean_object* v_j_662_, lean_object* v_bounded_663_, lean_object* v_bounded_u2082_664_){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_int_neg(v_bounded_u2082_664_);
v___x_666_ = lean_int_add(v_bounded_663_, v___x_665_);
lean_dec(v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___boxed(lean_object* v_n_667_, lean_object* v_m_668_, lean_object* v_i_669_, lean_object* v_j_670_, lean_object* v_bounded_671_, lean_object* v_bounded_u2082_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_Time_Internal_Bounded_LE_subBounds(v_n_667_, v_m_668_, v_i_669_, v_j_670_, v_bounded_671_, v_bounded_u2082_672_);
lean_dec(v_bounded_u2082_672_);
lean_dec(v_bounded_671_);
lean_dec(v_j_670_);
lean_dec(v_i_669_);
lean_dec(v_m_668_);
lean_dec(v_n_667_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___redArg(lean_object* v_bounded_674_, lean_object* v_num_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = lean_int_emod(v_bounded_674_, v_num_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___redArg___boxed(lean_object* v_bounded_677_, lean_object* v_num_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Std_Time_Internal_Bounded_LE_emod___redArg(v_bounded_677_, v_num_678_);
lean_dec(v_num_678_);
lean_dec(v_bounded_677_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod(lean_object* v_n_680_, lean_object* v_num_681_, lean_object* v_bounded_682_, lean_object* v_num_683_, lean_object* v_hi_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = lean_int_emod(v_bounded_682_, v_num_683_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___boxed(lean_object* v_n_686_, lean_object* v_num_687_, lean_object* v_bounded_688_, lean_object* v_num_689_, lean_object* v_hi_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Std_Time_Internal_Bounded_LE_emod(v_n_686_, v_num_687_, v_bounded_688_, v_num_689_, v_hi_690_);
lean_dec(v_num_689_);
lean_dec(v_bounded_688_);
lean_dec(v_num_687_);
lean_dec(v_n_686_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___redArg(lean_object* v_bounded_692_, lean_object* v_num_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = lean_int_mod(v_bounded_692_, v_num_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___redArg___boxed(lean_object* v_bounded_695_, lean_object* v_num_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_Time_Internal_Bounded_LE_mod___redArg(v_bounded_695_, v_num_696_);
lean_dec(v_num_696_);
lean_dec(v_bounded_695_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod(lean_object* v_n_698_, lean_object* v_num_699_, lean_object* v_bounded_700_, lean_object* v_num_701_, lean_object* v_hi_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = lean_int_mod(v_bounded_700_, v_num_701_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___boxed(lean_object* v_n_704_, lean_object* v_num_705_, lean_object* v_bounded_706_, lean_object* v_num_707_, lean_object* v_hi_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Std_Time_Internal_Bounded_LE_mod(v_n_704_, v_num_705_, v_bounded_706_, v_num_707_, v_hi_708_);
lean_dec(v_num_707_);
lean_dec(v_bounded_706_);
lean_dec(v_num_705_);
lean_dec(v_n_704_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___redArg(lean_object* v_bounded_710_, lean_object* v_num_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = lean_int_mul(v_bounded_710_, v_num_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___redArg___boxed(lean_object* v_bounded_713_, lean_object* v_num_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Std_Time_Internal_Bounded_LE_mul__pos___redArg(v_bounded_713_, v_num_714_);
lean_dec(v_num_714_);
lean_dec(v_bounded_713_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos(lean_object* v_n_716_, lean_object* v_m_717_, lean_object* v_bounded_718_, lean_object* v_num_719_, lean_object* v_h_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = lean_int_mul(v_bounded_718_, v_num_719_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___boxed(lean_object* v_n_722_, lean_object* v_m_723_, lean_object* v_bounded_724_, lean_object* v_num_725_, lean_object* v_h_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Std_Time_Internal_Bounded_LE_mul__pos(v_n_722_, v_m_723_, v_bounded_724_, v_num_725_, v_h_726_);
lean_dec(v_num_725_);
lean_dec(v_bounded_724_);
lean_dec(v_m_723_);
lean_dec(v_n_722_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___redArg(lean_object* v_bounded_728_, lean_object* v_num_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = lean_int_mul(v_bounded_728_, v_num_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___redArg___boxed(lean_object* v_bounded_731_, lean_object* v_num_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Std_Time_Internal_Bounded_LE_mul__neg___redArg(v_bounded_731_, v_num_732_);
lean_dec(v_num_732_);
lean_dec(v_bounded_731_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg(lean_object* v_n_734_, lean_object* v_m_735_, lean_object* v_bounded_736_, lean_object* v_num_737_, lean_object* v_h_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = lean_int_mul(v_bounded_736_, v_num_737_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___boxed(lean_object* v_n_740_, lean_object* v_m_741_, lean_object* v_bounded_742_, lean_object* v_num_743_, lean_object* v_h_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Std_Time_Internal_Bounded_LE_mul__neg(v_n_740_, v_m_741_, v_bounded_742_, v_num_743_, v_h_744_);
lean_dec(v_num_743_);
lean_dec(v_bounded_742_);
lean_dec(v_m_741_);
lean_dec(v_n_740_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___redArg(lean_object* v_bounded_746_, lean_object* v_num_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = lean_int_ediv(v_bounded_746_, v_num_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___redArg___boxed(lean_object* v_bounded_749_, lean_object* v_num_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Std_Time_Internal_Bounded_LE_ediv___redArg(v_bounded_749_, v_num_750_);
lean_dec(v_num_750_);
lean_dec(v_bounded_749_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv(lean_object* v_n_752_, lean_object* v_m_753_, lean_object* v_bounded_754_, lean_object* v_num_755_, lean_object* v_h_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = lean_int_ediv(v_bounded_754_, v_num_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___boxed(lean_object* v_n_758_, lean_object* v_m_759_, lean_object* v_bounded_760_, lean_object* v_num_761_, lean_object* v_h_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std_Time_Internal_Bounded_LE_ediv(v_n_758_, v_m_759_, v_bounded_760_, v_num_761_, v_h_762_);
lean_dec(v_num_761_);
lean_dec(v_bounded_760_);
lean_dec(v_m_759_);
lean_dec(v_n_758_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_eq(lean_object* v_n_764_){
_start:
{
lean_inc(v_n_764_);
return v_n_764_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_eq___boxed(lean_object* v_n_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Std_Time_Internal_Bounded_LE_eq(v_n_765_);
lean_dec(v_n_765_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___redArg(lean_object* v_bounded_767_){
_start:
{
lean_inc(v_bounded_767_);
return v_bounded_767_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___redArg___boxed(lean_object* v_bounded_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Std_Time_Internal_Bounded_LE_expand___redArg(v_bounded_768_);
lean_dec(v_bounded_768_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand(lean_object* v_lo_770_, lean_object* v_hi_771_, lean_object* v_nhi_772_, lean_object* v_nlo_773_, lean_object* v_bounded_774_, lean_object* v_h_775_, lean_object* v_h_u2081_776_){
_start:
{
lean_inc(v_bounded_774_);
return v_bounded_774_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___boxed(lean_object* v_lo_777_, lean_object* v_hi_778_, lean_object* v_nhi_779_, lean_object* v_nlo_780_, lean_object* v_bounded_781_, lean_object* v_h_782_, lean_object* v_h_u2081_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_Time_Internal_Bounded_LE_expand(v_lo_777_, v_hi_778_, v_nhi_779_, v_nlo_780_, v_bounded_781_, v_h_782_, v_h_u2081_783_);
lean_dec(v_bounded_781_);
lean_dec(v_nlo_780_);
lean_dec(v_nhi_779_);
lean_dec(v_hi_778_);
lean_dec(v_lo_777_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___redArg(lean_object* v_bounded_785_){
_start:
{
lean_inc(v_bounded_785_);
return v_bounded_785_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___redArg___boxed(lean_object* v_bounded_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Std_Time_Internal_Bounded_LE_expandTop___redArg(v_bounded_786_);
lean_dec(v_bounded_786_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop(lean_object* v_lo_788_, lean_object* v_hi_789_, lean_object* v_nhi_790_, lean_object* v_bounded_791_, lean_object* v_h_792_){
_start:
{
lean_inc(v_bounded_791_);
return v_bounded_791_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___boxed(lean_object* v_lo_793_, lean_object* v_hi_794_, lean_object* v_nhi_795_, lean_object* v_bounded_796_, lean_object* v_h_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Std_Time_Internal_Bounded_LE_expandTop(v_lo_793_, v_hi_794_, v_nhi_795_, v_bounded_796_, v_h_797_);
lean_dec(v_bounded_796_);
lean_dec(v_nhi_795_);
lean_dec(v_hi_794_);
lean_dec(v_lo_793_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___redArg(lean_object* v_bounded_799_){
_start:
{
lean_inc(v_bounded_799_);
return v_bounded_799_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___redArg___boxed(lean_object* v_bounded_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Std_Time_Internal_Bounded_LE_expandBottom___redArg(v_bounded_800_);
lean_dec(v_bounded_800_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom(lean_object* v_lo_802_, lean_object* v_hi_803_, lean_object* v_nlo_804_, lean_object* v_bounded_805_, lean_object* v_h_806_){
_start:
{
lean_inc(v_bounded_805_);
return v_bounded_805_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___boxed(lean_object* v_lo_807_, lean_object* v_hi_808_, lean_object* v_nlo_809_, lean_object* v_bounded_810_, lean_object* v_h_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Std_Time_Internal_Bounded_LE_expandBottom(v_lo_807_, v_hi_808_, v_nlo_809_, v_bounded_810_, v_h_811_);
lean_dec(v_bounded_810_);
lean_dec(v_nlo_809_);
lean_dec(v_hi_808_);
lean_dec(v_lo_807_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___redArg(lean_object* v_bounded_813_){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v___x_815_ = lean_int_add(v_bounded_813_, v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___redArg___boxed(lean_object* v_bounded_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_Time_Internal_Bounded_LE_succ___redArg(v_bounded_816_);
lean_dec(v_bounded_816_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ(lean_object* v_lo_818_, lean_object* v_hi_819_, lean_object* v_bounded_820_, lean_object* v_h_821_){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v___x_823_ = lean_int_add(v_bounded_820_, v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___boxed(lean_object* v_lo_824_, lean_object* v_hi_825_, lean_object* v_bounded_826_, lean_object* v_h_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Std_Time_Internal_Bounded_LE_succ(v_lo_824_, v_hi_825_, v_bounded_826_, v_h_827_);
lean_dec(v_bounded_826_);
lean_dec(v_hi_825_);
lean_dec(v_lo_824_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___redArg(lean_object* v_bo_829_){
_start:
{
lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_830_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v___x_831_ = lean_int_dec_le(v___x_830_, v_bo_829_);
if (v___x_831_ == 0)
{
lean_object* v_r_832_; 
v_r_832_ = lean_int_neg(v_bo_829_);
return v_r_832_;
}
else
{
lean_inc(v_bo_829_);
return v_bo_829_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___redArg___boxed(lean_object* v_bo_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Std_Time_Internal_Bounded_LE_abs___redArg(v_bo_833_);
lean_dec(v_bo_833_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs(lean_object* v_i_835_, lean_object* v_bo_836_){
_start:
{
lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_837_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v___x_838_ = lean_int_dec_le(v___x_837_, v_bo_836_);
if (v___x_838_ == 0)
{
lean_object* v_r_839_; 
v_r_839_ = lean_int_neg(v_bo_836_);
return v_r_839_;
}
else
{
lean_inc(v_bo_836_);
return v_bo_836_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___boxed(lean_object* v_i_840_, lean_object* v_bo_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_Time_Internal_Bounded_LE_abs(v_i_840_, v_bo_841_);
lean_dec(v_bo_841_);
lean_dec(v_i_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___redArg(lean_object* v_bounded_843_, lean_object* v_val_844_){
_start:
{
uint8_t v___x_845_; 
v___x_845_ = lean_int_dec_le(v_bounded_843_, v_val_844_);
if (v___x_845_ == 0)
{
lean_inc(v_bounded_843_);
return v_bounded_843_;
}
else
{
lean_inc(v_val_844_);
return v_val_844_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___redArg___boxed(lean_object* v_bounded_846_, lean_object* v_val_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Std_Time_Internal_Bounded_LE_max___redArg(v_bounded_846_, v_val_847_);
lean_dec(v_val_847_);
lean_dec(v_bounded_846_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max(lean_object* v_n_849_, lean_object* v_m_850_, lean_object* v_bounded_851_, lean_object* v_val_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_Time_Internal_Bounded_LE_max___redArg(v_bounded_851_, v_val_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___boxed(lean_object* v_n_854_, lean_object* v_m_855_, lean_object* v_bounded_856_, lean_object* v_val_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Std_Time_Internal_Bounded_LE_max(v_n_854_, v_m_855_, v_bounded_856_, v_val_857_);
lean_dec(v_val_857_);
lean_dec(v_bounded_856_);
lean_dec(v_m_855_);
lean_dec(v_n_854_);
return v_res_858_;
}
}
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Repr(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Internal_Bounded(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Internal_Bounded(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Repr(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Internal_Bounded(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Internal_Bounded(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Internal_Bounded(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Internal_Bounded(builtin);
}
#ifdef __cplusplus
}
#endif
