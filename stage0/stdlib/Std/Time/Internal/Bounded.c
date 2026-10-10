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
lean_object* l_Std_Time_Internal_Bounded_instLE___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT void l_Std_Time_Internal_Bounded_instLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l_Std_Time_Internal_Bounded_instLE___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLE___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Std_Time_Internal_Bounded_instLE___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLE(lean_object* v_rel_6_, lean_object* v_n_7_, lean_object* v_m_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLE___boxed(lean_object* v_rel_10_, lean_object* v_n_11_, lean_object* v_m_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Std_Time_Internal_Bounded_instLE(v_rel_10_, v_n_11_, v_m_12_);
lean_dec(v_m_12_);
lean_dec(v_n_11_);
return v_res_13_;
}
}
lean_object* l_Std_Time_Internal_Bounded_instLT___redArg(){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_box(0);
return v___x_15_;
}
}
LEAN_EXPORT void l_Std_Time_Internal_Bounded_instLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_16_;
v_res_16_ = l_Std_Time_Internal_Bounded_instLT___redArg();
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLT___redArg___boxed(lean_object* v___dummy_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Std_Time_Internal_Bounded_instLT___redArg();
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLT(lean_object* v_rel_19_, lean_object* v_n_20_, lean_object* v_m_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_box(0);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLT___boxed(lean_object* v_rel_23_, lean_object* v_n_24_, lean_object* v_m_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Time_Internal_Bounded_instLT(v_rel_23_, v_n_24_, v_m_25_);
lean_dec(v_m_25_);
lean_dec(v_n_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___redArg___lam__0(lean_object* v_x_27_){
_start:
{
lean_inc(v_x_27_);
return v_x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___redArg___lam__0___boxed(lean_object* v_x_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_Time_Internal_Bounded_instOrd___redArg___lam__0(v_x_28_);
lean_dec(v_x_28_);
return v_res_29_;
}
}
lean_object* l_Std_Time_Internal_Bounded_instOrd___redArg(){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = ((lean_object*)(l_Std_Time_Internal_Bounded_instOrd___redArg___closed__2));
return v___x_36_;
}
}
LEAN_EXPORT void l_Std_Time_Internal_Bounded_instOrd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_37_;
v_res_37_ = l_Std_Time_Internal_Bounded_instOrd___redArg();
stack->m_obj
 = v_res_37_;
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___redArg___boxed(lean_object* v___dummy_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Std_Time_Internal_Bounded_instOrd___redArg();
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd(lean_object* v_rel_40_, lean_object* v_n_41_, lean_object* v_m_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = ((lean_object*)(l_Std_Time_Internal_Bounded_instOrd___redArg___closed__2));
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___boxed(lean_object* v_rel_44_, lean_object* v_n_45_, lean_object* v_m_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Std_Time_Internal_Bounded_instOrd(v_rel_44_, v_n_45_, v_m_46_);
lean_dec(v_m_46_);
lean_dec(v_n_45_);
return v_res_47_;
}
}
static lean_object* _init_l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_unsigned_to_nat(0u);
v___x_49_ = lean_nat_to_int(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0(lean_object* v_n_50_, lean_object* v___y_51_){
_start:
{
lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_52_ = lean_obj_once(&l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0, &l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0_once, _init_l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0);
v___x_53_ = lean_int_dec_lt(v_n_50_, v___x_52_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = l_Int_repr(v_n_50_);
v___x_55_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
return v___x_55_;
}
else
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = l_Int_repr(v_n_50_);
v___x_57_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
v___x_58_ = l_Repr_addAppParen(v___x_57_, v___y_51_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___boxed(lean_object* v_n_59_, lean_object* v___y_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0(v_n_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec(v_n_59_);
return v_res_61_;
}
}
lean_object* l_Std_Time_Internal_Bounded_instRepr___redArg(){
_start:
{
lean_object* v___f_64_; 
v___f_64_ = ((lean_object*)(l_Std_Time_Internal_Bounded_instRepr___redArg___closed__0));
return v___f_64_;
}
}
LEAN_EXPORT void l_Std_Time_Internal_Bounded_instRepr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_65_;
v_res_65_ = l_Std_Time_Internal_Bounded_instRepr___redArg();
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___redArg___boxed(lean_object* v___dummy_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Std_Time_Internal_Bounded_instRepr___redArg();
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr(lean_object* v_rel_68_, lean_object* v_m_69_, lean_object* v_n_70_){
_start:
{
lean_object* v___f_71_; 
v___f_71_ = ((lean_object*)(l_Std_Time_Internal_Bounded_instRepr___redArg___closed__0));
return v___f_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___boxed(lean_object* v_rel_72_, lean_object* v_m_73_, lean_object* v_n_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Std_Time_Internal_Bounded_instRepr(v_rel_72_, v_m_73_, v_n_74_);
lean_dec(v_n_74_);
lean_dec(v_m_73_);
return v_res_75_;
}
}
uint8_t l_Std_Time_Internal_Bounded_instDecidableEq___redArg(lean_object* v_a_76_, lean_object* v_b_77_){
_start:
{
uint8_t v___x_78_; 
v___x_78_ = lean_int_dec_eq(v_a_76_, v_b_77_);
return v___x_78_;
}
}
LEAN_EXPORT void l_Std_Time_Internal_Bounded_instDecidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_76_ = stack[0].m_obj;
lean_object* v_b_77_ = stack[1].m_obj;
uint8_t v_res_79_;
v_res_79_ = l_Std_Time_Internal_Bounded_instDecidableEq___redArg(v_a_76_, v_b_77_);
stack->m_num = v_res_79_;
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableEq___redArg___boxed(lean_object* v_a_80_, lean_object* v_b_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Std_Time_Internal_Bounded_instDecidableEq___redArg(v_a_80_, v_b_81_);
lean_dec(v_b_81_);
lean_dec(v_a_80_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
uint8_t l_Std_Time_Internal_Bounded_instDecidableEq(lean_object* v_rel_84_, lean_object* v_n_85_, lean_object* v_m_86_, lean_object* v_a_87_, lean_object* v_b_88_){
_start:
{
uint8_t v___x_89_; 
v___x_89_ = lean_int_dec_eq(v_a_87_, v_b_88_);
return v___x_89_;
}
}
LEAN_EXPORT void l_Std_Time_Internal_Bounded_instDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_85_ = stack[1].m_obj;
lean_object* v_m_86_ = stack[2].m_obj;
lean_object* v_a_87_ = stack[3].m_obj;
lean_object* v_b_88_ = stack[4].m_obj;
uint8_t v_res_90_;
v_res_90_ = l_Std_Time_Internal_Bounded_instDecidableEq(lean_box(0), v_n_85_, v_m_86_, v_a_87_, v_b_88_);
stack->m_num = v_res_90_;
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableEq___boxed(lean_object* v_rel_91_, lean_object* v_n_92_, lean_object* v_m_93_, lean_object* v_a_94_, lean_object* v_b_95_){
_start:
{
uint8_t v_res_96_; lean_object* v_r_97_; 
v_res_96_ = l_Std_Time_Internal_Bounded_instDecidableEq(v_rel_91_, v_n_92_, v_m_93_, v_a_94_, v_b_95_);
lean_dec(v_b_95_);
lean_dec(v_a_94_);
lean_dec(v_m_93_);
lean_dec(v_n_92_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
uint8_t l_Std_Time_Internal_Bounded_instDecidableLe___redArg(lean_object* v_x_98_, lean_object* v_y_99_){
_start:
{
uint8_t v___x_100_; 
v___x_100_ = lean_int_dec_le(v_x_98_, v_y_99_);
return v___x_100_;
}
}
LEAN_EXPORT void l_Std_Time_Internal_Bounded_instDecidableLe___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_98_ = stack[0].m_obj;
lean_object* v_y_99_ = stack[1].m_obj;
uint8_t v_res_101_;
v_res_101_ = l_Std_Time_Internal_Bounded_instDecidableLe___redArg(v_x_98_, v_y_99_);
stack->m_num = v_res_101_;
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableLe___redArg___boxed(lean_object* v_x_102_, lean_object* v_y_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Std_Time_Internal_Bounded_instDecidableLe___redArg(v_x_102_, v_y_103_);
lean_dec(v_y_103_);
lean_dec(v_x_102_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
uint8_t l_Std_Time_Internal_Bounded_instDecidableLe(lean_object* v_rel_106_, lean_object* v_a_107_, lean_object* v_b_108_, lean_object* v_x_109_, lean_object* v_y_110_){
_start:
{
uint8_t v___x_111_; 
v___x_111_ = lean_int_dec_le(v_x_109_, v_y_110_);
return v___x_111_;
}
}
LEAN_EXPORT void l_Std_Time_Internal_Bounded_instDecidableLe_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_107_ = stack[1].m_obj;
lean_object* v_b_108_ = stack[2].m_obj;
lean_object* v_x_109_ = stack[3].m_obj;
lean_object* v_y_110_ = stack[4].m_obj;
uint8_t v_res_112_;
v_res_112_ = l_Std_Time_Internal_Bounded_instDecidableLe(lean_box(0), v_a_107_, v_b_108_, v_x_109_, v_y_110_);
stack->m_num = v_res_112_;
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableLe___boxed(lean_object* v_rel_113_, lean_object* v_a_114_, lean_object* v_b_115_, lean_object* v_x_116_, lean_object* v_y_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_Std_Time_Internal_Bounded_instDecidableLe(v_rel_113_, v_a_114_, v_b_115_, v_x_116_, v_y_117_);
lean_dec(v_y_117_);
lean_dec(v_x_116_);
lean_dec(v_b_115_);
lean_dec(v_a_114_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast___redArg(lean_object* v_b_120_){
_start:
{
lean_inc(v_b_120_);
return v_b_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast___redArg___boxed(lean_object* v_b_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Std_Time_Internal_Bounded_cast___redArg(v_b_121_);
lean_dec(v_b_121_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast(lean_object* v_rel_123_, lean_object* v_lo_u2081_124_, lean_object* v_lo_u2082_125_, lean_object* v_hi_u2081_126_, lean_object* v_hi_u2082_127_, lean_object* v_h_u2081_128_, lean_object* v_h_u2082_129_, lean_object* v_b_130_){
_start:
{
lean_inc(v_b_130_);
return v_b_130_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast___boxed(lean_object* v_rel_131_, lean_object* v_lo_u2081_132_, lean_object* v_lo_u2082_133_, lean_object* v_hi_u2081_134_, lean_object* v_hi_u2082_135_, lean_object* v_h_u2081_136_, lean_object* v_h_u2082_137_, lean_object* v_b_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Std_Time_Internal_Bounded_cast(v_rel_131_, v_lo_u2081_132_, v_lo_u2082_133_, v_hi_u2081_134_, v_hi_u2082_135_, v_h_u2081_136_, v_h_u2082_137_, v_b_138_);
lean_dec(v_b_138_);
lean_dec(v_hi_u2082_135_);
lean_dec(v_hi_u2081_134_);
lean_dec(v_lo_u2082_133_);
lean_dec(v_lo_u2081_132_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk___redArg(lean_object* v_val_140_){
_start:
{
lean_inc(v_val_140_);
return v_val_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk___redArg___boxed(lean_object* v_val_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Std_Time_Internal_Bounded_mk___redArg(v_val_141_);
lean_dec(v_val_141_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk(lean_object* v_lo_143_, lean_object* v_hi_144_, lean_object* v_rel_145_, lean_object* v_val_146_, lean_object* v_proof_147_){
_start:
{
lean_inc(v_val_146_);
return v_val_146_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk___boxed(lean_object* v_lo_148_, lean_object* v_hi_149_, lean_object* v_rel_150_, lean_object* v_val_151_, lean_object* v_proof_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Std_Time_Internal_Bounded_mk(v_lo_148_, v_hi_149_, v_rel_150_, v_val_151_, v_proof_152_);
lean_dec(v_val_151_);
lean_dec(v_hi_149_);
lean_dec(v_lo_148_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_ofInt_x3f___redArg(lean_object* v_lo_154_, lean_object* v_hi_155_, lean_object* v_inst_156_, lean_object* v_val_157_){
_start:
{
lean_object* v___x_158_; uint8_t v___x_159_; 
lean_inc_ref(v_inst_156_);
lean_inc(v_val_157_);
v___x_158_ = lean_apply_2(v_inst_156_, v_lo_154_, v_val_157_);
v___x_159_ = lean_unbox(v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; 
lean_dec(v_val_157_);
lean_dec_ref(v_inst_156_);
lean_dec(v_hi_155_);
v___x_160_ = lean_box(0);
return v___x_160_;
}
else
{
lean_object* v___x_161_; uint8_t v___x_162_; 
lean_inc(v_val_157_);
v___x_161_ = lean_apply_2(v_inst_156_, v_val_157_, v_hi_155_);
v___x_162_ = lean_unbox(v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; 
lean_dec(v_val_157_);
v___x_163_ = lean_box(0);
return v___x_163_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_164_, 0, v_val_157_);
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_ofInt_x3f(lean_object* v_rel_165_, lean_object* v_lo_166_, lean_object* v_hi_167_, lean_object* v_inst_168_, lean_object* v_val_169_){
_start:
{
lean_object* v___x_170_; uint8_t v___x_171_; 
lean_inc_ref(v_inst_168_);
lean_inc(v_val_169_);
v___x_170_ = lean_apply_2(v_inst_168_, v_lo_166_, v_val_169_);
v___x_171_ = lean_unbox(v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; 
lean_dec(v_val_169_);
lean_dec_ref(v_inst_168_);
lean_dec(v_hi_167_);
v___x_172_ = lean_box(0);
return v___x_172_;
}
else
{
lean_object* v___x_173_; uint8_t v___x_174_; 
lean_inc(v_val_169_);
v___x_173_ = lean_apply_2(v_inst_168_, v_val_169_, v_hi_167_);
v___x_174_ = lean_unbox(v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
lean_dec(v_val_169_);
v___x_175_ = lean_box(0);
return v___x_175_;
}
else
{
lean_object* v___x_176_; 
v___x_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_176_, 0, v_val_169_);
return v___x_176_;
}
}
}
}
static lean_object* _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = lean_nat_to_int(v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg(lean_object* v_lo_179_, lean_object* v_hi_180_, lean_object* v_val_181_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v_range_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_182_ = lean_int_sub(v_hi_180_, v_lo_179_);
v___x_183_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v_range_184_ = lean_int_add(v___x_182_, v___x_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_int_sub(v_val_181_, v_lo_179_);
v___x_186_ = lean_int_emod(v___x_185_, v_range_184_);
lean_dec(v___x_185_);
v___x_187_ = lean_int_add(v___x_186_, v_range_184_);
lean_dec(v___x_186_);
v___x_188_ = lean_int_emod(v___x_187_, v_range_184_);
lean_dec(v_range_184_);
lean_dec(v___x_187_);
v___x_189_ = lean_int_add(v___x_188_, v_lo_179_);
lean_dec(v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___boxed(lean_object* v_lo_190_, lean_object* v_hi_191_, lean_object* v_val_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg(v_lo_190_, v_hi_191_, v_val_192_);
lean_dec(v_val_192_);
lean_dec(v_hi_191_);
lean_dec(v_lo_190_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping(lean_object* v_lo_194_, lean_object* v_hi_195_, lean_object* v_val_196_, lean_object* v_h_197_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v_range_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_198_ = lean_int_sub(v_hi_195_, v_lo_194_);
v___x_199_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v_range_200_ = lean_int_add(v___x_198_, v___x_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_int_sub(v_val_196_, v_lo_194_);
v___x_202_ = lean_int_emod(v___x_201_, v_range_200_);
lean_dec(v___x_201_);
v___x_203_ = lean_int_add(v___x_202_, v_range_200_);
lean_dec(v___x_202_);
v___x_204_ = lean_int_emod(v___x_203_, v_range_200_);
lean_dec(v_range_200_);
lean_dec(v___x_203_);
v___x_205_ = lean_int_add(v___x_204_, v_lo_194_);
lean_dec(v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping___boxed(lean_object* v_lo_206_, lean_object* v_hi_207_, lean_object* v_val_208_, lean_object* v_h_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_Time_Internal_Bounded_LE_ofNatWrapping(v_lo_206_, v_hi_207_, v_val_208_, v_h_209_);
lean_dec(v_val_208_);
lean_dec(v_hi_207_);
lean_dec(v_lo_206_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(lean_object* v_lo_211_, lean_object* v_n_212_, lean_object* v_k_213_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v_range_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_214_ = lean_nat_to_int(v_k_213_);
v___x_215_ = lean_int_add(v_lo_211_, v___x_214_);
lean_dec(v___x_214_);
v___x_216_ = lean_nat_to_int(v_n_212_);
v___x_217_ = lean_int_sub(v___x_215_, v_lo_211_);
lean_dec(v___x_215_);
v___x_218_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v_range_219_ = lean_int_add(v___x_217_, v___x_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_int_sub(v___x_216_, v_lo_211_);
lean_dec(v___x_216_);
v___x_221_ = lean_int_emod(v___x_220_, v_range_219_);
lean_dec(v___x_220_);
v___x_222_ = lean_int_add(v___x_221_, v_range_219_);
lean_dec(v___x_221_);
v___x_223_ = lean_int_emod(v___x_222_, v_range_219_);
lean_dec(v_range_219_);
lean_dec(v___x_222_);
v___x_224_ = lean_int_add(v___x_223_, v_lo_211_);
lean_dec(v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast___boxed(lean_object* v_lo_225_, lean_object* v_n_226_, lean_object* v_k_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(v_lo_225_, v_n_226_, v_k_227_);
lean_dec(v_lo_225_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instInhabitedHAddIntCast(lean_object* v_lo_229_, lean_object* v_k_230_){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v_range_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_231_ = lean_nat_to_int(v_k_230_);
v___x_232_ = lean_int_add(v_lo_229_, v___x_231_);
lean_dec(v___x_231_);
v___x_233_ = lean_int_sub(v___x_232_, v_lo_229_);
lean_dec(v___x_232_);
v___x_234_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v_range_235_ = lean_int_add(v___x_233_, v___x_234_);
lean_dec(v___x_233_);
v___x_236_ = lean_int_sub(v_lo_229_, v_lo_229_);
v___x_237_ = lean_int_emod(v___x_236_, v_range_235_);
lean_dec(v___x_236_);
v___x_238_ = lean_int_add(v___x_237_, v_range_235_);
lean_dec(v___x_237_);
v___x_239_ = lean_int_emod(v___x_238_, v_range_235_);
lean_dec(v_range_235_);
lean_dec(v___x_238_);
v___x_240_ = lean_int_add(v___x_239_, v_lo_229_);
lean_dec(v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instInhabitedHAddIntCast___boxed(lean_object* v_lo_241_, lean_object* v_k_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Std_Time_Internal_Bounded_LE_instInhabitedHAddIntCast(v_lo_241_, v_k_242_);
lean_dec(v_lo_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk___redArg(lean_object* v_val_244_){
_start:
{
lean_inc(v_val_244_);
return v_val_244_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk___redArg___boxed(lean_object* v_val_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Std_Time_Internal_Bounded_LE_mk___redArg(v_val_245_);
lean_dec(v_val_245_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk(lean_object* v_lo_247_, lean_object* v_hi_248_, lean_object* v_val_249_, lean_object* v_proof_250_){
_start:
{
lean_inc(v_val_249_);
return v_val_249_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk___boxed(lean_object* v_lo_251_, lean_object* v_hi_252_, lean_object* v_val_253_, lean_object* v_proof_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Std_Time_Internal_Bounded_LE_mk(v_lo_251_, v_hi_252_, v_val_253_, v_proof_254_);
lean_dec(v_val_253_);
lean_dec(v_hi_252_);
lean_dec(v_lo_251_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_exact(lean_object* v_val_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_nat_to_int(v_val_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofInt(lean_object* v_lo_258_, lean_object* v_hi_259_, lean_object* v_val_260_){
_start:
{
uint8_t v___x_261_; 
v___x_261_ = lean_int_dec_le(v_lo_258_, v_val_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
lean_dec(v_val_260_);
v___x_262_ = lean_box(0);
return v___x_262_;
}
else
{
uint8_t v___x_263_; 
v___x_263_ = lean_int_dec_le(v_val_260_, v_hi_259_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
lean_dec(v_val_260_);
v___x_264_ = lean_box(0);
return v___x_264_;
}
else
{
lean_object* v___x_265_; 
v___x_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_265_, 0, v_val_260_);
return v___x_265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofInt___boxed(lean_object* v_lo_266_, lean_object* v_hi_267_, lean_object* v_val_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Std_Time_Internal_Bounded_LE_ofInt(v_lo_266_, v_hi_267_, v_val_268_);
lean_dec(v_hi_267_);
lean_dec(v_lo_266_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat___redArg(lean_object* v_val_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = lean_nat_to_int(v_val_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat(lean_object* v_hi_272_, lean_object* v_val_273_, lean_object* v_h_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = lean_nat_to_int(v_val_273_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat___boxed(lean_object* v_hi_276_, lean_object* v_val_277_, lean_object* v_h_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Std_Time_Internal_Bounded_LE_ofNat(v_hi_276_, v_val_277_, v_h_278_);
lean_dec(v_hi_276_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x3f(lean_object* v_hi_280_, lean_object* v_val_281_){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = lean_nat_dec_le(v_val_281_, v_hi_280_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; 
lean_dec(v_val_281_);
v___x_283_ = lean_box(0);
return v___x_283_;
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_nat_to_int(v_val_281_);
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x3f___boxed(lean_object* v_hi_286_, lean_object* v_val_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Std_Time_Internal_Bounded_LE_ofNat_x3f(v_hi_286_, v_val_287_);
lean_dec(v_hi_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27___redArg(lean_object* v_val_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lean_nat_to_int(v_val_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27(lean_object* v_lo_291_, lean_object* v_hi_292_, lean_object* v_val_293_, lean_object* v_h_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = lean_nat_to_int(v_val_293_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27___boxed(lean_object* v_lo_296_, lean_object* v_hi_297_, lean_object* v_val_298_, lean_object* v_h_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_Time_Internal_Bounded_LE_ofNat_x27(v_lo_296_, v_hi_297_, v_val_298_, v_h_299_);
lean_dec(v_hi_297_);
lean_dec(v_lo_296_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___redArg(lean_object* v_lo_301_, lean_object* v_hi_302_, lean_object* v_val_303_){
_start:
{
uint8_t v___x_304_; 
v___x_304_ = lean_int_dec_le(v_lo_301_, v_val_303_);
if (v___x_304_ == 0)
{
lean_inc(v_lo_301_);
return v_lo_301_;
}
else
{
uint8_t v___x_305_; 
v___x_305_ = lean_int_dec_le(v_val_303_, v_hi_302_);
if (v___x_305_ == 0)
{
lean_inc(v_hi_302_);
return v_hi_302_;
}
else
{
lean_inc(v_val_303_);
return v_val_303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___redArg___boxed(lean_object* v_lo_306_, lean_object* v_hi_307_, lean_object* v_val_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_Time_Internal_Bounded_LE_clip___redArg(v_lo_306_, v_hi_307_, v_val_308_);
lean_dec(v_val_308_);
lean_dec(v_hi_307_);
lean_dec(v_lo_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip(lean_object* v_lo_310_, lean_object* v_hi_311_, lean_object* v_val_312_, lean_object* v_h_313_){
_start:
{
uint8_t v___x_314_; 
v___x_314_ = lean_int_dec_le(v_lo_310_, v_val_312_);
if (v___x_314_ == 0)
{
lean_inc(v_lo_310_);
return v_lo_310_;
}
else
{
uint8_t v___x_315_; 
v___x_315_ = lean_int_dec_le(v_val_312_, v_hi_311_);
if (v___x_315_ == 0)
{
lean_inc(v_hi_311_);
return v_hi_311_;
}
else
{
lean_inc(v_val_312_);
return v_val_312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___boxed(lean_object* v_lo_316_, lean_object* v_hi_317_, lean_object* v_val_318_, lean_object* v_h_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Std_Time_Internal_Bounded_LE_clip(v_lo_316_, v_hi_317_, v_val_318_, v_h_319_);
lean_dec(v_val_318_);
lean_dec(v_hi_317_);
lean_dec(v_lo_316_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___redArg(lean_object* v_n_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Int_toNat(v_n_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___redArg___boxed(lean_object* v_n_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Std_Time_Internal_Bounded_LE_toNat___redArg(v_n_323_);
lean_dec(v_n_323_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat(lean_object* v_lo_325_, lean_object* v_hi_326_, lean_object* v_n_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Int_toNat(v_n_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___boxed(lean_object* v_lo_329_, lean_object* v_hi_330_, lean_object* v_n_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_Time_Internal_Bounded_LE_toNat(v_lo_329_, v_hi_330_, v_n_331_);
lean_dec(v_n_331_);
lean_dec(v_hi_330_);
lean_dec(v_lo_329_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg(lean_object* v_n_333_){
_start:
{
lean_object* v_intZero_334_; uint8_t v_isNeg_335_; lean_object* v_a_336_; 
v_intZero_334_ = lean_obj_once(&l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0, &l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0_once, _init_l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0);
v_isNeg_335_ = lean_int_dec_lt(v_n_333_, v_intZero_334_);
v_a_336_ = lean_nat_abs(v_n_333_);
return v_a_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg___boxed(lean_object* v_n_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg(v_n_337_);
lean_dec(v_n_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27(lean_object* v_lo_339_, lean_object* v_hi_340_, lean_object* v_n_341_, lean_object* v_h_342_){
_start:
{
lean_object* v_intZero_343_; uint8_t v_isNeg_344_; lean_object* v_a_345_; 
v_intZero_343_ = lean_obj_once(&l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0, &l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0_once, _init_l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0);
v_isNeg_344_ = lean_int_dec_lt(v_n_341_, v_intZero_343_);
v_a_345_ = lean_nat_abs(v_n_341_);
return v_a_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___boxed(lean_object* v_lo_346_, lean_object* v_hi_347_, lean_object* v_n_348_, lean_object* v_h_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_Time_Internal_Bounded_LE_toNat_x27(v_lo_346_, v_hi_347_, v_n_348_, v_h_349_);
lean_dec(v_n_348_);
lean_dec(v_hi_347_);
lean_dec(v_lo_346_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___redArg(lean_object* v_n_351_){
_start:
{
lean_inc(v_n_351_);
return v_n_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___redArg___boxed(lean_object* v_n_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_Time_Internal_Bounded_LE_toInt___redArg(v_n_352_);
lean_dec(v_n_352_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt(lean_object* v_lo_354_, lean_object* v_hi_355_, lean_object* v_n_356_){
_start:
{
lean_inc(v_n_356_);
return v_n_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___boxed(lean_object* v_lo_357_, lean_object* v_hi_358_, lean_object* v_n_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Std_Time_Internal_Bounded_LE_toInt(v_lo_357_, v_hi_358_, v_n_359_);
lean_dec(v_n_359_);
lean_dec(v_hi_358_);
lean_dec(v_lo_357_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___redArg(lean_object* v_n_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Int_toNat(v_n_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___redArg___boxed(lean_object* v_n_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Std_Time_Internal_Bounded_LE_toFin___redArg(v_n_363_);
lean_dec(v_n_363_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin(lean_object* v_lo_365_, lean_object* v_hi_366_, lean_object* v_n_367_, lean_object* v_h_u2080_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Int_toNat(v_n_367_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___boxed(lean_object* v_lo_370_, lean_object* v_hi_371_, lean_object* v_n_372_, lean_object* v_h_u2080_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Std_Time_Internal_Bounded_LE_toFin(v_lo_370_, v_hi_371_, v_n_372_, v_h_u2080_373_);
lean_dec(v_n_372_);
lean_dec(v_hi_371_);
lean_dec(v_lo_370_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin___redArg(lean_object* v_fin_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = lean_nat_to_int(v_fin_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin(lean_object* v_hi_377_, lean_object* v_fin_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = lean_nat_to_int(v_fin_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin___boxed(lean_object* v_hi_380_, lean_object* v_fin_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Std_Time_Internal_Bounded_LE_ofFin(v_hi_380_, v_fin_381_);
lean_dec(v_hi_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27___redArg(lean_object* v_lo_383_, lean_object* v_fin_384_){
_start:
{
uint8_t v___x_385_; 
v___x_385_ = lean_nat_dec_le(v_lo_383_, v_fin_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
lean_dec(v_fin_384_);
v___x_386_ = lean_nat_to_int(v_lo_383_);
return v___x_386_;
}
else
{
lean_object* v___x_387_; 
lean_dec(v_lo_383_);
v___x_387_ = lean_nat_to_int(v_fin_384_);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27(lean_object* v_hi_388_, lean_object* v_lo_389_, lean_object* v_fin_390_, lean_object* v_h_391_){
_start:
{
uint8_t v___x_392_; 
v___x_392_ = lean_nat_dec_le(v_lo_389_, v_fin_390_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
lean_dec(v_fin_390_);
v___x_393_ = lean_nat_to_int(v_lo_389_);
return v___x_393_;
}
else
{
lean_object* v___x_394_; 
lean_dec(v_lo_389_);
v___x_394_ = lean_nat_to_int(v_fin_390_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27___boxed(lean_object* v_hi_395_, lean_object* v_lo_396_, lean_object* v_fin_397_, lean_object* v_h_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Std_Time_Internal_Bounded_LE_ofFin_x27(v_hi_395_, v_lo_396_, v_fin_397_, v_h_398_);
lean_dec(v_hi_395_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___redArg(lean_object* v_b_400_, lean_object* v_i_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = lean_int_emod(v_b_400_, v_i_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___redArg___boxed(lean_object* v_b_403_, lean_object* v_i_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_Time_Internal_Bounded_LE_byEmod___redArg(v_b_403_, v_i_404_);
lean_dec(v_i_404_);
lean_dec(v_b_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod(lean_object* v_b_406_, lean_object* v_i_407_, lean_object* v_hi_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = lean_int_emod(v_b_406_, v_i_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___boxed(lean_object* v_b_410_, lean_object* v_i_411_, lean_object* v_hi_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Std_Time_Internal_Bounded_LE_byEmod(v_b_410_, v_i_411_, v_hi_412_);
lean_dec(v_i_411_);
lean_dec(v_b_410_);
return v_res_413_;
}
}
static lean_object* _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_414_; lean_object* v_intZero_415_; 
v_natZero_414_ = lean_unsigned_to_nat(0u);
v_intZero_415_ = lean_nat_to_int(v_natZero_414_);
return v_intZero_415_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg(lean_object* v_x_416_, lean_object* v_x_417_, lean_object* v_h__1_418_, lean_object* v_h__2_419_, lean_object* v_h__3_420_, lean_object* v_h__4_421_){
_start:
{
lean_object* v_intZero_422_; uint8_t v_isNeg_423_; 
v_intZero_422_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v_isNeg_423_ = lean_int_dec_lt(v_x_416_, v_intZero_422_);
if (v_isNeg_423_ == 0)
{
lean_object* v_a_424_; uint8_t v_isNeg_425_; 
lean_dec(v_h__4_421_);
lean_dec(v_h__3_420_);
v_a_424_ = lean_nat_abs(v_x_416_);
v_isNeg_425_ = lean_int_dec_lt(v_x_417_, v_intZero_422_);
if (v_isNeg_425_ == 0)
{
lean_object* v_a_426_; lean_object* v___x_427_; 
lean_dec(v_h__2_419_);
v_a_426_ = lean_nat_abs(v_x_417_);
v___x_427_ = lean_apply_2(v_h__1_418_, v_a_424_, v_a_426_);
return v___x_427_;
}
else
{
lean_object* v_abs_428_; lean_object* v_one_429_; lean_object* v_a_430_; lean_object* v___x_431_; 
lean_dec(v_h__1_418_);
v_abs_428_ = lean_nat_abs(v_x_417_);
v_one_429_ = lean_unsigned_to_nat(1u);
v_a_430_ = lean_nat_sub(v_abs_428_, v_one_429_);
lean_dec(v_abs_428_);
v___x_431_ = lean_apply_2(v_h__2_419_, v_a_424_, v_a_430_);
return v___x_431_;
}
}
else
{
lean_object* v_abs_432_; lean_object* v_one_433_; lean_object* v_a_434_; uint8_t v_isNeg_435_; 
lean_dec(v_h__2_419_);
lean_dec(v_h__1_418_);
v_abs_432_ = lean_nat_abs(v_x_416_);
v_one_433_ = lean_unsigned_to_nat(1u);
v_a_434_ = lean_nat_sub(v_abs_432_, v_one_433_);
lean_dec(v_abs_432_);
v_isNeg_435_ = lean_int_dec_lt(v_x_417_, v_intZero_422_);
if (v_isNeg_435_ == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; 
lean_dec(v_h__4_421_);
v_a_436_ = lean_nat_abs(v_x_417_);
v___x_437_ = lean_apply_2(v_h__3_420_, v_a_434_, v_a_436_);
return v___x_437_;
}
else
{
lean_object* v_abs_438_; lean_object* v_a_439_; lean_object* v___x_440_; 
lean_dec(v_h__3_420_);
v_abs_438_ = lean_nat_abs(v_x_417_);
v_a_439_ = lean_nat_sub(v_abs_438_, v_one_433_);
lean_dec(v_abs_438_);
v___x_440_ = lean_apply_2(v_h__4_421_, v_a_434_, v_a_439_);
return v___x_440_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___boxed(lean_object* v_x_441_, lean_object* v_x_442_, lean_object* v_h__1_443_, lean_object* v_h__2_444_, lean_object* v_h__3_445_, lean_object* v_h__4_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg(v_x_441_, v_x_442_, v_h__1_443_, v_h__2_444_, v_h__3_445_, v_h__4_446_);
lean_dec(v_x_442_);
lean_dec(v_x_441_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter(lean_object* v_motive_448_, lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v_h__1_451_, lean_object* v_h__2_452_, lean_object* v_h__3_453_, lean_object* v_h__4_454_){
_start:
{
lean_object* v_intZero_455_; uint8_t v_isNeg_456_; 
v_intZero_455_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v_isNeg_456_ = lean_int_dec_lt(v_x_449_, v_intZero_455_);
if (v_isNeg_456_ == 0)
{
lean_object* v_a_457_; uint8_t v_isNeg_458_; 
lean_dec(v_h__4_454_);
lean_dec(v_h__3_453_);
v_a_457_ = lean_nat_abs(v_x_449_);
v_isNeg_458_ = lean_int_dec_lt(v_x_450_, v_intZero_455_);
if (v_isNeg_458_ == 0)
{
lean_object* v_a_459_; lean_object* v___x_460_; 
lean_dec(v_h__2_452_);
v_a_459_ = lean_nat_abs(v_x_450_);
v___x_460_ = lean_apply_2(v_h__1_451_, v_a_457_, v_a_459_);
return v___x_460_;
}
else
{
lean_object* v_abs_461_; lean_object* v_one_462_; lean_object* v_a_463_; lean_object* v___x_464_; 
lean_dec(v_h__1_451_);
v_abs_461_ = lean_nat_abs(v_x_450_);
v_one_462_ = lean_unsigned_to_nat(1u);
v_a_463_ = lean_nat_sub(v_abs_461_, v_one_462_);
lean_dec(v_abs_461_);
v___x_464_ = lean_apply_2(v_h__2_452_, v_a_457_, v_a_463_);
return v___x_464_;
}
}
else
{
lean_object* v_abs_465_; lean_object* v_one_466_; lean_object* v_a_467_; uint8_t v_isNeg_468_; 
lean_dec(v_h__2_452_);
lean_dec(v_h__1_451_);
v_abs_465_ = lean_nat_abs(v_x_449_);
v_one_466_ = lean_unsigned_to_nat(1u);
v_a_467_ = lean_nat_sub(v_abs_465_, v_one_466_);
lean_dec(v_abs_465_);
v_isNeg_468_ = lean_int_dec_lt(v_x_450_, v_intZero_455_);
if (v_isNeg_468_ == 0)
{
lean_object* v_a_469_; lean_object* v___x_470_; 
lean_dec(v_h__4_454_);
v_a_469_ = lean_nat_abs(v_x_450_);
v___x_470_ = lean_apply_2(v_h__3_453_, v_a_467_, v_a_469_);
return v___x_470_;
}
else
{
lean_object* v_abs_471_; lean_object* v_a_472_; lean_object* v___x_473_; 
lean_dec(v_h__3_453_);
v_abs_471_ = lean_nat_abs(v_x_450_);
v_a_472_ = lean_nat_sub(v_abs_471_, v_one_466_);
lean_dec(v_abs_471_);
v___x_473_ = lean_apply_2(v_h__4_454_, v_a_467_, v_a_472_);
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___boxed(lean_object* v_motive_474_, lean_object* v_x_475_, lean_object* v_x_476_, lean_object* v_h__1_477_, lean_object* v_h__2_478_, lean_object* v_h__3_479_, lean_object* v_h__4_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter(v_motive_474_, v_x_475_, v_x_476_, v_h__1_477_, v_h__2_478_, v_h__3_479_, v_h__4_480_);
lean_dec(v_x_476_);
lean_dec(v_x_475_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___redArg(lean_object* v_b_482_, lean_object* v_i_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = lean_int_mod(v_b_482_, v_i_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___redArg___boxed(lean_object* v_b_485_, lean_object* v_i_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Std_Time_Internal_Bounded_LE_byMod___redArg(v_b_485_, v_i_486_);
lean_dec(v_i_486_);
lean_dec(v_b_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod(lean_object* v_b_488_, lean_object* v_i_489_, lean_object* v_hi_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = lean_int_mod(v_b_488_, v_i_489_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___boxed(lean_object* v_b_492_, lean_object* v_i_493_, lean_object* v_hi_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Std_Time_Internal_Bounded_LE_byMod(v_b_492_, v_i_493_, v_hi_494_);
lean_dec(v_i_493_);
lean_dec(v_b_492_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___redArg(lean_object* v_n_496_, lean_object* v_bounded_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = lean_int_sub(v_bounded_497_, v_n_496_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___redArg___boxed(lean_object* v_n_499_, lean_object* v_bounded_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Std_Time_Internal_Bounded_LE_truncate___redArg(v_n_499_, v_bounded_500_);
lean_dec(v_bounded_500_);
lean_dec(v_n_499_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate(lean_object* v_n_502_, lean_object* v_m_503_, lean_object* v_bounded_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = lean_int_sub(v_bounded_504_, v_n_502_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___boxed(lean_object* v_n_506_, lean_object* v_m_507_, lean_object* v_bounded_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Std_Time_Internal_Bounded_LE_truncate(v_n_506_, v_m_507_, v_bounded_508_);
lean_dec(v_bounded_508_);
lean_dec(v_m_507_);
lean_dec(v_n_506_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___redArg(lean_object* v_bounded_510_){
_start:
{
lean_inc(v_bounded_510_);
return v_bounded_510_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___redArg___boxed(lean_object* v_bounded_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Std_Time_Internal_Bounded_LE_truncateTop___redArg(v_bounded_511_);
lean_dec(v_bounded_511_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop(lean_object* v_n_513_, lean_object* v_m_514_, lean_object* v_j_515_, lean_object* v_bounded_516_, lean_object* v_h_517_){
_start:
{
lean_inc(v_bounded_516_);
return v_bounded_516_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___boxed(lean_object* v_n_518_, lean_object* v_m_519_, lean_object* v_j_520_, lean_object* v_bounded_521_, lean_object* v_h_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Std_Time_Internal_Bounded_LE_truncateTop(v_n_518_, v_m_519_, v_j_520_, v_bounded_521_, v_h_522_);
lean_dec(v_bounded_521_);
lean_dec(v_j_520_);
lean_dec(v_m_519_);
lean_dec(v_n_518_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg(lean_object* v_bounded_524_){
_start:
{
lean_inc(v_bounded_524_);
return v_bounded_524_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg___boxed(lean_object* v_bounded_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg(v_bounded_525_);
lean_dec(v_bounded_525_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom(lean_object* v_n_527_, lean_object* v_m_528_, lean_object* v_j_529_, lean_object* v_bounded_530_, lean_object* v_h_531_){
_start:
{
lean_inc(v_bounded_530_);
return v_bounded_530_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___boxed(lean_object* v_n_532_, lean_object* v_m_533_, lean_object* v_j_534_, lean_object* v_bounded_535_, lean_object* v_h_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_Time_Internal_Bounded_LE_truncateBottom(v_n_532_, v_m_533_, v_j_534_, v_bounded_535_, v_h_536_);
lean_dec(v_bounded_535_);
lean_dec(v_j_534_);
lean_dec(v_m_533_);
lean_dec(v_n_532_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___redArg(lean_object* v_bounded_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = lean_int_neg(v_bounded_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___redArg___boxed(lean_object* v_bounded_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_Time_Internal_Bounded_LE_neg___redArg(v_bounded_540_);
lean_dec(v_bounded_540_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg(lean_object* v_n_542_, lean_object* v_m_543_, lean_object* v_bounded_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = lean_int_neg(v_bounded_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___boxed(lean_object* v_n_546_, lean_object* v_m_547_, lean_object* v_bounded_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Std_Time_Internal_Bounded_LE_neg(v_n_546_, v_m_547_, v_bounded_548_);
lean_dec(v_bounded_548_);
lean_dec(v_m_547_);
lean_dec(v_n_546_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___redArg(lean_object* v_bounded_550_, lean_object* v_num_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = lean_int_add(v_bounded_550_, v_num_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___redArg___boxed(lean_object* v_bounded_553_, lean_object* v_num_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Std_Time_Internal_Bounded_LE_add___redArg(v_bounded_553_, v_num_554_);
lean_dec(v_num_554_);
lean_dec(v_bounded_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add(lean_object* v_n_556_, lean_object* v_m_557_, lean_object* v_bounded_558_, lean_object* v_num_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = lean_int_add(v_bounded_558_, v_num_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___boxed(lean_object* v_n_561_, lean_object* v_m_562_, lean_object* v_bounded_563_, lean_object* v_num_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Std_Time_Internal_Bounded_LE_add(v_n_561_, v_m_562_, v_bounded_563_, v_num_564_);
lean_dec(v_num_564_);
lean_dec(v_bounded_563_);
lean_dec(v_m_562_);
lean_dec(v_n_561_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___redArg(lean_object* v_num_566_, lean_object* v_bounded_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = lean_int_add(v_bounded_567_, v_num_566_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___redArg___boxed(lean_object* v_num_569_, lean_object* v_bounded_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Std_Time_Internal_Bounded_LE_addProven___redArg(v_num_569_, v_bounded_570_);
lean_dec(v_bounded_570_);
lean_dec(v_num_569_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven(lean_object* v_n_572_, lean_object* v_m_573_, lean_object* v_num_574_, lean_object* v_bounded_575_, lean_object* v_h_u2080_576_, lean_object* v_h_u2081_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = lean_int_add(v_bounded_575_, v_num_574_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___boxed(lean_object* v_n_579_, lean_object* v_m_580_, lean_object* v_num_581_, lean_object* v_bounded_582_, lean_object* v_h_u2080_583_, lean_object* v_h_u2081_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_Time_Internal_Bounded_LE_addProven(v_n_579_, v_m_580_, v_num_581_, v_bounded_582_, v_h_u2080_583_, v_h_u2081_584_);
lean_dec(v_bounded_582_);
lean_dec(v_num_581_);
lean_dec(v_m_580_);
lean_dec(v_n_579_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___redArg(lean_object* v_bounded_586_, lean_object* v_num_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = lean_int_add(v_bounded_586_, v_num_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___redArg___boxed(lean_object* v_bounded_589_, lean_object* v_num_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Std_Time_Internal_Bounded_LE_addTop___redArg(v_bounded_589_, v_num_590_);
lean_dec(v_num_590_);
lean_dec(v_bounded_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop(lean_object* v_n_592_, lean_object* v_m_593_, lean_object* v_bounded_594_, lean_object* v_num_595_, lean_object* v_h_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = lean_int_add(v_bounded_594_, v_num_595_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___boxed(lean_object* v_n_598_, lean_object* v_m_599_, lean_object* v_bounded_600_, lean_object* v_num_601_, lean_object* v_h_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Std_Time_Internal_Bounded_LE_addTop(v_n_598_, v_m_599_, v_bounded_600_, v_num_601_, v_h_602_);
lean_dec(v_num_601_);
lean_dec(v_bounded_600_);
lean_dec(v_m_599_);
lean_dec(v_n_598_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___redArg(lean_object* v_bounded_604_, lean_object* v_num_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = lean_int_sub(v_bounded_604_, v_num_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___redArg___boxed(lean_object* v_bounded_607_, lean_object* v_num_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Std_Time_Internal_Bounded_LE_subBottom___redArg(v_bounded_607_, v_num_608_);
lean_dec(v_num_608_);
lean_dec(v_bounded_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom(lean_object* v_n_610_, lean_object* v_m_611_, lean_object* v_bounded_612_, lean_object* v_num_613_, lean_object* v_h_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_int_sub(v_bounded_612_, v_num_613_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___boxed(lean_object* v_n_616_, lean_object* v_m_617_, lean_object* v_bounded_618_, lean_object* v_num_619_, lean_object* v_h_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_Time_Internal_Bounded_LE_subBottom(v_n_616_, v_m_617_, v_bounded_618_, v_num_619_, v_h_620_);
lean_dec(v_num_619_);
lean_dec(v_bounded_618_);
lean_dec(v_m_617_);
lean_dec(v_n_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___redArg(lean_object* v_bounded_622_, lean_object* v_bounded_u2082_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = lean_int_add(v_bounded_622_, v_bounded_u2082_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___redArg___boxed(lean_object* v_bounded_625_, lean_object* v_bounded_u2082_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Std_Time_Internal_Bounded_LE_addBounds___redArg(v_bounded_625_, v_bounded_u2082_626_);
lean_dec(v_bounded_u2082_626_);
lean_dec(v_bounded_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds(lean_object* v_n_628_, lean_object* v_m_629_, lean_object* v_i_630_, lean_object* v_j_631_, lean_object* v_bounded_632_, lean_object* v_bounded_u2082_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = lean_int_add(v_bounded_632_, v_bounded_u2082_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___boxed(lean_object* v_n_635_, lean_object* v_m_636_, lean_object* v_i_637_, lean_object* v_j_638_, lean_object* v_bounded_639_, lean_object* v_bounded_u2082_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Std_Time_Internal_Bounded_LE_addBounds(v_n_635_, v_m_636_, v_i_637_, v_j_638_, v_bounded_639_, v_bounded_u2082_640_);
lean_dec(v_bounded_u2082_640_);
lean_dec(v_bounded_639_);
lean_dec(v_j_638_);
lean_dec(v_i_637_);
lean_dec(v_m_636_);
lean_dec(v_n_635_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___redArg(lean_object* v_bounded_642_, lean_object* v_num_643_){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_int_neg(v_num_643_);
v___x_645_ = lean_int_add(v_bounded_642_, v___x_644_);
lean_dec(v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___redArg___boxed(lean_object* v_bounded_646_, lean_object* v_num_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Std_Time_Internal_Bounded_LE_sub___redArg(v_bounded_646_, v_num_647_);
lean_dec(v_num_647_);
lean_dec(v_bounded_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub(lean_object* v_n_649_, lean_object* v_m_650_, lean_object* v_bounded_651_, lean_object* v_num_652_){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_int_neg(v_num_652_);
v___x_654_ = lean_int_add(v_bounded_651_, v___x_653_);
lean_dec(v___x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___boxed(lean_object* v_n_655_, lean_object* v_m_656_, lean_object* v_bounded_657_, lean_object* v_num_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_Time_Internal_Bounded_LE_sub(v_n_655_, v_m_656_, v_bounded_657_, v_num_658_);
lean_dec(v_num_658_);
lean_dec(v_bounded_657_);
lean_dec(v_m_656_);
lean_dec(v_n_655_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___redArg(lean_object* v_bounded_660_, lean_object* v_bounded_u2082_661_){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_int_neg(v_bounded_u2082_661_);
v___x_663_ = lean_int_add(v_bounded_660_, v___x_662_);
lean_dec(v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___redArg___boxed(lean_object* v_bounded_664_, lean_object* v_bounded_u2082_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Std_Time_Internal_Bounded_LE_subBounds___redArg(v_bounded_664_, v_bounded_u2082_665_);
lean_dec(v_bounded_u2082_665_);
lean_dec(v_bounded_664_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds(lean_object* v_n_667_, lean_object* v_m_668_, lean_object* v_i_669_, lean_object* v_j_670_, lean_object* v_bounded_671_, lean_object* v_bounded_u2082_672_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_int_neg(v_bounded_u2082_672_);
v___x_674_ = lean_int_add(v_bounded_671_, v___x_673_);
lean_dec(v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___boxed(lean_object* v_n_675_, lean_object* v_m_676_, lean_object* v_i_677_, lean_object* v_j_678_, lean_object* v_bounded_679_, lean_object* v_bounded_u2082_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Std_Time_Internal_Bounded_LE_subBounds(v_n_675_, v_m_676_, v_i_677_, v_j_678_, v_bounded_679_, v_bounded_u2082_680_);
lean_dec(v_bounded_u2082_680_);
lean_dec(v_bounded_679_);
lean_dec(v_j_678_);
lean_dec(v_i_677_);
lean_dec(v_m_676_);
lean_dec(v_n_675_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___redArg(lean_object* v_bounded_682_, lean_object* v_num_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = lean_int_emod(v_bounded_682_, v_num_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___redArg___boxed(lean_object* v_bounded_685_, lean_object* v_num_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Std_Time_Internal_Bounded_LE_emod___redArg(v_bounded_685_, v_num_686_);
lean_dec(v_num_686_);
lean_dec(v_bounded_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod(lean_object* v_n_688_, lean_object* v_num_689_, lean_object* v_bounded_690_, lean_object* v_num_691_, lean_object* v_hi_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = lean_int_emod(v_bounded_690_, v_num_691_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___boxed(lean_object* v_n_694_, lean_object* v_num_695_, lean_object* v_bounded_696_, lean_object* v_num_697_, lean_object* v_hi_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Std_Time_Internal_Bounded_LE_emod(v_n_694_, v_num_695_, v_bounded_696_, v_num_697_, v_hi_698_);
lean_dec(v_num_697_);
lean_dec(v_bounded_696_);
lean_dec(v_num_695_);
lean_dec(v_n_694_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___redArg(lean_object* v_bounded_700_, lean_object* v_num_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = lean_int_mod(v_bounded_700_, v_num_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___redArg___boxed(lean_object* v_bounded_703_, lean_object* v_num_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Std_Time_Internal_Bounded_LE_mod___redArg(v_bounded_703_, v_num_704_);
lean_dec(v_num_704_);
lean_dec(v_bounded_703_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod(lean_object* v_n_706_, lean_object* v_num_707_, lean_object* v_bounded_708_, lean_object* v_num_709_, lean_object* v_hi_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = lean_int_mod(v_bounded_708_, v_num_709_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___boxed(lean_object* v_n_712_, lean_object* v_num_713_, lean_object* v_bounded_714_, lean_object* v_num_715_, lean_object* v_hi_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Std_Time_Internal_Bounded_LE_mod(v_n_712_, v_num_713_, v_bounded_714_, v_num_715_, v_hi_716_);
lean_dec(v_num_715_);
lean_dec(v_bounded_714_);
lean_dec(v_num_713_);
lean_dec(v_n_712_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___redArg(lean_object* v_bounded_718_, lean_object* v_num_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = lean_int_mul(v_bounded_718_, v_num_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___redArg___boxed(lean_object* v_bounded_721_, lean_object* v_num_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Std_Time_Internal_Bounded_LE_mul__pos___redArg(v_bounded_721_, v_num_722_);
lean_dec(v_num_722_);
lean_dec(v_bounded_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos(lean_object* v_n_724_, lean_object* v_m_725_, lean_object* v_bounded_726_, lean_object* v_num_727_, lean_object* v_h_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = lean_int_mul(v_bounded_726_, v_num_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___boxed(lean_object* v_n_730_, lean_object* v_m_731_, lean_object* v_bounded_732_, lean_object* v_num_733_, lean_object* v_h_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_Time_Internal_Bounded_LE_mul__pos(v_n_730_, v_m_731_, v_bounded_732_, v_num_733_, v_h_734_);
lean_dec(v_num_733_);
lean_dec(v_bounded_732_);
lean_dec(v_m_731_);
lean_dec(v_n_730_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___redArg(lean_object* v_bounded_736_, lean_object* v_num_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = lean_int_mul(v_bounded_736_, v_num_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___redArg___boxed(lean_object* v_bounded_739_, lean_object* v_num_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Std_Time_Internal_Bounded_LE_mul__neg___redArg(v_bounded_739_, v_num_740_);
lean_dec(v_num_740_);
lean_dec(v_bounded_739_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg(lean_object* v_n_742_, lean_object* v_m_743_, lean_object* v_bounded_744_, lean_object* v_num_745_, lean_object* v_h_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = lean_int_mul(v_bounded_744_, v_num_745_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___boxed(lean_object* v_n_748_, lean_object* v_m_749_, lean_object* v_bounded_750_, lean_object* v_num_751_, lean_object* v_h_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Std_Time_Internal_Bounded_LE_mul__neg(v_n_748_, v_m_749_, v_bounded_750_, v_num_751_, v_h_752_);
lean_dec(v_num_751_);
lean_dec(v_bounded_750_);
lean_dec(v_m_749_);
lean_dec(v_n_748_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___redArg(lean_object* v_bounded_754_, lean_object* v_num_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = lean_int_ediv(v_bounded_754_, v_num_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___redArg___boxed(lean_object* v_bounded_757_, lean_object* v_num_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Std_Time_Internal_Bounded_LE_ediv___redArg(v_bounded_757_, v_num_758_);
lean_dec(v_num_758_);
lean_dec(v_bounded_757_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv(lean_object* v_n_760_, lean_object* v_m_761_, lean_object* v_bounded_762_, lean_object* v_num_763_, lean_object* v_h_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = lean_int_ediv(v_bounded_762_, v_num_763_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___boxed(lean_object* v_n_766_, lean_object* v_m_767_, lean_object* v_bounded_768_, lean_object* v_num_769_, lean_object* v_h_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Std_Time_Internal_Bounded_LE_ediv(v_n_766_, v_m_767_, v_bounded_768_, v_num_769_, v_h_770_);
lean_dec(v_num_769_);
lean_dec(v_bounded_768_);
lean_dec(v_m_767_);
lean_dec(v_n_766_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_eq(lean_object* v_n_772_){
_start:
{
lean_inc(v_n_772_);
return v_n_772_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_eq___boxed(lean_object* v_n_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Std_Time_Internal_Bounded_LE_eq(v_n_773_);
lean_dec(v_n_773_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___redArg(lean_object* v_bounded_775_){
_start:
{
lean_inc(v_bounded_775_);
return v_bounded_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___redArg___boxed(lean_object* v_bounded_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Std_Time_Internal_Bounded_LE_expand___redArg(v_bounded_776_);
lean_dec(v_bounded_776_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand(lean_object* v_lo_778_, lean_object* v_hi_779_, lean_object* v_nhi_780_, lean_object* v_nlo_781_, lean_object* v_bounded_782_, lean_object* v_h_783_, lean_object* v_h_u2081_784_){
_start:
{
lean_inc(v_bounded_782_);
return v_bounded_782_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___boxed(lean_object* v_lo_785_, lean_object* v_hi_786_, lean_object* v_nhi_787_, lean_object* v_nlo_788_, lean_object* v_bounded_789_, lean_object* v_h_790_, lean_object* v_h_u2081_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Std_Time_Internal_Bounded_LE_expand(v_lo_785_, v_hi_786_, v_nhi_787_, v_nlo_788_, v_bounded_789_, v_h_790_, v_h_u2081_791_);
lean_dec(v_bounded_789_);
lean_dec(v_nlo_788_);
lean_dec(v_nhi_787_);
lean_dec(v_hi_786_);
lean_dec(v_lo_785_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___redArg(lean_object* v_bounded_793_){
_start:
{
lean_inc(v_bounded_793_);
return v_bounded_793_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___redArg___boxed(lean_object* v_bounded_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Std_Time_Internal_Bounded_LE_expandTop___redArg(v_bounded_794_);
lean_dec(v_bounded_794_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop(lean_object* v_lo_796_, lean_object* v_hi_797_, lean_object* v_nhi_798_, lean_object* v_bounded_799_, lean_object* v_h_800_){
_start:
{
lean_inc(v_bounded_799_);
return v_bounded_799_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___boxed(lean_object* v_lo_801_, lean_object* v_hi_802_, lean_object* v_nhi_803_, lean_object* v_bounded_804_, lean_object* v_h_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_Time_Internal_Bounded_LE_expandTop(v_lo_801_, v_hi_802_, v_nhi_803_, v_bounded_804_, v_h_805_);
lean_dec(v_bounded_804_);
lean_dec(v_nhi_803_);
lean_dec(v_hi_802_);
lean_dec(v_lo_801_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___redArg(lean_object* v_bounded_807_){
_start:
{
lean_inc(v_bounded_807_);
return v_bounded_807_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___redArg___boxed(lean_object* v_bounded_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Std_Time_Internal_Bounded_LE_expandBottom___redArg(v_bounded_808_);
lean_dec(v_bounded_808_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom(lean_object* v_lo_810_, lean_object* v_hi_811_, lean_object* v_nlo_812_, lean_object* v_bounded_813_, lean_object* v_h_814_){
_start:
{
lean_inc(v_bounded_813_);
return v_bounded_813_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___boxed(lean_object* v_lo_815_, lean_object* v_hi_816_, lean_object* v_nlo_817_, lean_object* v_bounded_818_, lean_object* v_h_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Std_Time_Internal_Bounded_LE_expandBottom(v_lo_815_, v_hi_816_, v_nlo_817_, v_bounded_818_, v_h_819_);
lean_dec(v_bounded_818_);
lean_dec(v_nlo_817_);
lean_dec(v_hi_816_);
lean_dec(v_lo_815_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___redArg(lean_object* v_bounded_821_){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v___x_823_ = lean_int_add(v_bounded_821_, v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___redArg___boxed(lean_object* v_bounded_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Std_Time_Internal_Bounded_LE_succ___redArg(v_bounded_824_);
lean_dec(v_bounded_824_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ(lean_object* v_lo_826_, lean_object* v_hi_827_, lean_object* v_bounded_828_, lean_object* v_h_829_){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v___x_831_ = lean_int_add(v_bounded_828_, v___x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___boxed(lean_object* v_lo_832_, lean_object* v_hi_833_, lean_object* v_bounded_834_, lean_object* v_h_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Std_Time_Internal_Bounded_LE_succ(v_lo_832_, v_hi_833_, v_bounded_834_, v_h_835_);
lean_dec(v_bounded_834_);
lean_dec(v_hi_833_);
lean_dec(v_lo_832_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___redArg(lean_object* v_bo_837_){
_start:
{
lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_838_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v___x_839_ = lean_int_dec_le(v___x_838_, v_bo_837_);
if (v___x_839_ == 0)
{
lean_object* v_r_840_; 
v_r_840_ = lean_int_neg(v_bo_837_);
return v_r_840_;
}
else
{
lean_inc(v_bo_837_);
return v_bo_837_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___redArg___boxed(lean_object* v_bo_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_Time_Internal_Bounded_LE_abs___redArg(v_bo_841_);
lean_dec(v_bo_841_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs(lean_object* v_i_843_, lean_object* v_bo_844_){
_start:
{
lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_845_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v___x_846_ = lean_int_dec_le(v___x_845_, v_bo_844_);
if (v___x_846_ == 0)
{
lean_object* v_r_847_; 
v_r_847_ = lean_int_neg(v_bo_844_);
return v_r_847_;
}
else
{
lean_inc(v_bo_844_);
return v_bo_844_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___boxed(lean_object* v_i_848_, lean_object* v_bo_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Std_Time_Internal_Bounded_LE_abs(v_i_848_, v_bo_849_);
lean_dec(v_bo_849_);
lean_dec(v_i_848_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___redArg(lean_object* v_bounded_851_, lean_object* v_val_852_){
_start:
{
uint8_t v___x_853_; 
v___x_853_ = lean_int_dec_le(v_bounded_851_, v_val_852_);
if (v___x_853_ == 0)
{
lean_inc(v_bounded_851_);
return v_bounded_851_;
}
else
{
lean_inc(v_val_852_);
return v_val_852_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___redArg___boxed(lean_object* v_bounded_854_, lean_object* v_val_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_Time_Internal_Bounded_LE_max___redArg(v_bounded_854_, v_val_855_);
lean_dec(v_val_855_);
lean_dec(v_bounded_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max(lean_object* v_n_857_, lean_object* v_m_858_, lean_object* v_bounded_859_, lean_object* v_val_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Std_Time_Internal_Bounded_LE_max___redArg(v_bounded_859_, v_val_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___boxed(lean_object* v_n_862_, lean_object* v_m_863_, lean_object* v_bounded_864_, lean_object* v_val_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Std_Time_Internal_Bounded_LE_max(v_n_862_, v_m_863_, v_bounded_864_, v_val_865_);
lean_dec(v_val_865_);
lean_dec(v_bounded_864_);
lean_dec(v_m_863_);
lean_dec(v_n_862_);
return v_res_866_;
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
