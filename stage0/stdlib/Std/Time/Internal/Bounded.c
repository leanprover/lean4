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
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_nonneg(lean_object*);
lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLE___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLT___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Time_Internal_Bounded_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_Bounded_instOrd___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Internal_Bounded_instOrd___closed__0 = (const lean_object*)&l_Std_Time_Internal_Bounded_instOrd___closed__0_value;
static const lean_closure_object l_Std_Time_Internal_Bounded_instOrd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Internal_Bounded_instOrd___closed__1 = (const lean_object*)&l_Std_Time_Internal_Bounded_instOrd___closed__1_value;
static const lean_closure_object l_Std_Time_Internal_Bounded_instOrd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Internal_Bounded_instOrd___closed__1_value),((lean_object*)&l_Std_Time_Internal_Bounded_instOrd___closed__0_value)} };
static const lean_object* l_Std_Time_Internal_Bounded_instOrd___closed__2 = (const lean_object*)&l_Std_Time_Internal_Bounded_instOrd___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Internal_Bounded_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_Bounded_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Internal_Bounded_instRepr___closed__0 = (const lean_object*)&l_Std_Time_Internal_Bounded_instRepr___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableEq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableLe___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableLe___aux__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableLe___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableLe___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLE(lean_object* v_rel_1_, lean_object* v_n_2_, lean_object* v_m_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLE___boxed(lean_object* v_rel_5_, lean_object* v_n_6_, lean_object* v_m_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Std_Time_Internal_Bounded_instLE(v_rel_5_, v_n_6_, v_m_7_);
lean_dec(v_m_7_);
lean_dec(v_n_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLT(lean_object* v_rel_9_, lean_object* v_n_10_, lean_object* v_m_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_box(0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instLT___boxed(lean_object* v_rel_13_, lean_object* v_n_14_, lean_object* v_m_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Std_Time_Internal_Bounded_instLT(v_rel_13_, v_n_14_, v_m_15_);
lean_dec(v_m_15_);
lean_dec(v_n_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___lam__0(lean_object* v_x_17_){
_start:
{
lean_inc(v_x_17_);
return v_x_17_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___lam__0___boxed(lean_object* v_x_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Std_Time_Internal_Bounded_instOrd___lam__0(v_x_18_);
lean_dec(v_x_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd(lean_object* v_rel_25_, lean_object* v_n_26_, lean_object* v_m_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = ((lean_object*)(l_Std_Time_Internal_Bounded_instOrd___closed__2));
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instOrd___boxed(lean_object* v_rel_29_, lean_object* v_n_30_, lean_object* v_m_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Std_Time_Internal_Bounded_instOrd(v_rel_29_, v_n_30_, v_m_31_);
lean_dec(v_m_31_);
lean_dec(v_n_30_);
return v_res_32_;
}
}
static lean_object* _init_l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = lean_nat_to_int(v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___lam__0(lean_object* v_n_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = lean_obj_once(&l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0, &l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0_once, _init_l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0);
v___x_38_ = lean_int_dec_lt(v_n_35_, v___x_37_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = l_Int_repr(v_n_35_);
v___x_40_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
return v___x_40_;
}
else
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = l_Int_repr(v_n_35_);
v___x_42_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
v___x_43_ = l_Repr_addAppParen(v___x_42_, v___y_36_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___lam__0___boxed(lean_object* v_n_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Std_Time_Internal_Bounded_instRepr___lam__0(v_n_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec(v_n_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr(lean_object* v_rel_48_, lean_object* v_m_49_, lean_object* v_n_50_){
_start:
{
lean_object* v___f_51_; 
v___f_51_ = ((lean_object*)(l_Std_Time_Internal_Bounded_instRepr___closed__0));
return v___f_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instRepr___boxed(lean_object* v_rel_52_, lean_object* v_m_53_, lean_object* v_n_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Std_Time_Internal_Bounded_instRepr(v_rel_52_, v_m_53_, v_n_54_);
lean_dec(v_n_54_);
lean_dec(v_m_53_);
return v_res_55_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableEq___redArg(lean_object* v_a_56_, lean_object* v_b_57_){
_start:
{
uint8_t v___x_58_; 
v___x_58_ = lean_int_dec_eq(v_a_56_, v_b_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableEq___redArg___boxed(lean_object* v_a_59_, lean_object* v_b_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l_Std_Time_Internal_Bounded_instDecidableEq___redArg(v_a_59_, v_b_60_);
lean_dec(v_b_60_);
lean_dec(v_a_59_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableEq(lean_object* v_rel_63_, lean_object* v_n_64_, lean_object* v_m_65_, lean_object* v_a_66_, lean_object* v_b_67_){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = lean_int_dec_eq(v_a_66_, v_b_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableEq___boxed(lean_object* v_rel_69_, lean_object* v_n_70_, lean_object* v_m_71_, lean_object* v_a_72_, lean_object* v_b_73_){
_start:
{
uint8_t v_res_74_; lean_object* v_r_75_; 
v_res_74_ = l_Std_Time_Internal_Bounded_instDecidableEq(v_rel_69_, v_n_70_, v_m_71_, v_a_72_, v_b_73_);
lean_dec(v_b_73_);
lean_dec(v_a_72_);
lean_dec(v_m_71_);
lean_dec(v_n_70_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableLe___aux__1___redArg(lean_object* v_x_76_, lean_object* v_y_77_){
_start:
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = lean_int_sub(v_y_77_, v_x_76_);
v___x_79_ = lean_int_dec_nonneg(v___x_78_);
lean_dec(v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableLe___aux__1___redArg___boxed(lean_object* v_x_80_, lean_object* v_y_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Std_Time_Internal_Bounded_instDecidableLe___aux__1___redArg(v_x_80_, v_y_81_);
lean_dec(v_y_81_);
lean_dec(v_x_80_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableLe___aux__1(lean_object* v_rel_84_, lean_object* v_a_85_, lean_object* v_b_86_, lean_object* v_x_87_, lean_object* v_y_88_){
_start:
{
uint8_t v___x_89_; 
v___x_89_ = l_Std_Time_Internal_Bounded_instDecidableLe___aux__1___redArg(v_x_87_, v_y_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableLe___aux__1___boxed(lean_object* v_rel_90_, lean_object* v_a_91_, lean_object* v_b_92_, lean_object* v_x_93_, lean_object* v_y_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_Std_Time_Internal_Bounded_instDecidableLe___aux__1(v_rel_90_, v_a_91_, v_b_92_, v_x_93_, v_y_94_);
lean_dec(v_y_94_);
lean_dec(v_x_93_);
lean_dec(v_b_92_);
lean_dec(v_a_91_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableLe___redArg(lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
uint8_t v___x_99_; 
v___x_99_ = l_Std_Time_Internal_Bounded_instDecidableLe___aux__1___redArg(v___y_97_, v___y_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableLe___redArg___boxed(lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_Std_Time_Internal_Bounded_instDecidableLe___redArg(v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec(v___y_100_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableLe(lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
uint8_t v___x_109_; 
v___x_109_ = l_Std_Time_Internal_Bounded_instDecidableLe___aux__1___redArg(v___y_107_, v___y_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableLe___boxed(lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
uint8_t v_res_115_; lean_object* v_r_116_; 
v_res_115_ = l_Std_Time_Internal_Bounded_instDecidableLe(v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec(v___y_113_);
lean_dec(v___y_112_);
lean_dec(v___y_111_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast___redArg(lean_object* v_b_117_){
_start:
{
lean_inc(v_b_117_);
return v_b_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast___redArg___boxed(lean_object* v_b_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Std_Time_Internal_Bounded_cast___redArg(v_b_118_);
lean_dec(v_b_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast(lean_object* v_rel_120_, lean_object* v_lo_u2081_121_, lean_object* v_lo_u2082_122_, lean_object* v_hi_u2081_123_, lean_object* v_hi_u2082_124_, lean_object* v_h_u2081_125_, lean_object* v_h_u2082_126_, lean_object* v_b_127_){
_start:
{
lean_inc(v_b_127_);
return v_b_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast___boxed(lean_object* v_rel_128_, lean_object* v_lo_u2081_129_, lean_object* v_lo_u2082_130_, lean_object* v_hi_u2081_131_, lean_object* v_hi_u2082_132_, lean_object* v_h_u2081_133_, lean_object* v_h_u2082_134_, lean_object* v_b_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Std_Time_Internal_Bounded_cast(v_rel_128_, v_lo_u2081_129_, v_lo_u2082_130_, v_hi_u2081_131_, v_hi_u2082_132_, v_h_u2081_133_, v_h_u2082_134_, v_b_135_);
lean_dec(v_b_135_);
lean_dec(v_hi_u2082_132_);
lean_dec(v_hi_u2081_131_);
lean_dec(v_lo_u2082_130_);
lean_dec(v_lo_u2081_129_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk___redArg(lean_object* v_val_137_){
_start:
{
lean_inc(v_val_137_);
return v_val_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk___redArg___boxed(lean_object* v_val_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Std_Time_Internal_Bounded_mk___redArg(v_val_138_);
lean_dec(v_val_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk(lean_object* v_lo_140_, lean_object* v_hi_141_, lean_object* v_rel_142_, lean_object* v_val_143_, lean_object* v_proof_144_){
_start:
{
lean_inc(v_val_143_);
return v_val_143_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk___boxed(lean_object* v_lo_145_, lean_object* v_hi_146_, lean_object* v_rel_147_, lean_object* v_val_148_, lean_object* v_proof_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Std_Time_Internal_Bounded_mk(v_lo_145_, v_hi_146_, v_rel_147_, v_val_148_, v_proof_149_);
lean_dec(v_val_148_);
lean_dec(v_hi_146_);
lean_dec(v_lo_145_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_ofInt_x3f___redArg(lean_object* v_lo_151_, lean_object* v_hi_152_, lean_object* v_inst_153_, lean_object* v_val_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
lean_inc_ref(v_inst_153_);
lean_inc_n(v_val_154_, 2);
v___x_155_ = lean_apply_2(v_inst_153_, v_val_154_, v_hi_152_);
v___x_156_ = lean_apply_2(v_inst_153_, v_lo_151_, v_val_154_);
v___x_157_ = lean_unbox(v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; 
lean_dec(v_val_154_);
v___x_158_ = lean_box(0);
return v___x_158_;
}
else
{
uint8_t v___x_159_; 
v___x_159_ = lean_unbox(v___x_155_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; 
lean_dec(v_val_154_);
v___x_160_ = lean_box(0);
return v___x_160_;
}
else
{
lean_object* v___x_161_; 
v___x_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_161_, 0, v_val_154_);
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_ofInt_x3f(lean_object* v_rel_162_, lean_object* v_lo_163_, lean_object* v_hi_164_, lean_object* v_inst_165_, lean_object* v_val_166_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
lean_inc_ref(v_inst_165_);
lean_inc_n(v_val_166_, 2);
v___x_167_ = lean_apply_2(v_inst_165_, v_val_166_, v_hi_164_);
v___x_168_ = lean_apply_2(v_inst_165_, v_lo_163_, v_val_166_);
v___x_169_ = lean_unbox(v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
lean_dec(v_val_166_);
v___x_170_ = lean_box(0);
return v___x_170_;
}
else
{
uint8_t v___x_171_; 
v___x_171_ = lean_unbox(v___x_167_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; 
lean_dec(v_val_166_);
v___x_172_ = lean_box(0);
return v___x_172_;
}
else
{
lean_object* v___x_173_; 
v___x_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_173_, 0, v_val_166_);
return v___x_173_;
}
}
}
}
static lean_object* _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_nat_to_int(v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg(lean_object* v_lo_176_, lean_object* v_hi_177_, lean_object* v_val_178_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v_range_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_179_ = lean_int_sub(v_hi_177_, v_lo_176_);
v___x_180_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v_range_181_ = lean_int_add(v___x_179_, v___x_180_);
lean_dec(v___x_179_);
v___x_182_ = lean_int_sub(v_val_178_, v_lo_176_);
v___x_183_ = lean_int_emod(v___x_182_, v_range_181_);
lean_dec(v___x_182_);
v___x_184_ = lean_int_add(v___x_183_, v_range_181_);
lean_dec(v___x_183_);
v___x_185_ = lean_int_emod(v___x_184_, v_range_181_);
lean_dec(v_range_181_);
lean_dec(v___x_184_);
v___x_186_ = lean_int_add(v___x_185_, v_lo_176_);
lean_dec(v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___boxed(lean_object* v_lo_187_, lean_object* v_hi_188_, lean_object* v_val_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg(v_lo_187_, v_hi_188_, v_val_189_);
lean_dec(v_val_189_);
lean_dec(v_hi_188_);
lean_dec(v_lo_187_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping(lean_object* v_lo_191_, lean_object* v_hi_192_, lean_object* v_val_193_, lean_object* v_h_194_){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v_range_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_195_ = lean_int_sub(v_hi_192_, v_lo_191_);
v___x_196_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v_range_197_ = lean_int_add(v___x_195_, v___x_196_);
lean_dec(v___x_195_);
v___x_198_ = lean_int_sub(v_val_193_, v_lo_191_);
v___x_199_ = lean_int_emod(v___x_198_, v_range_197_);
lean_dec(v___x_198_);
v___x_200_ = lean_int_add(v___x_199_, v_range_197_);
lean_dec(v___x_199_);
v___x_201_ = lean_int_emod(v___x_200_, v_range_197_);
lean_dec(v_range_197_);
lean_dec(v___x_200_);
v___x_202_ = lean_int_add(v___x_201_, v_lo_191_);
lean_dec(v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping___boxed(lean_object* v_lo_203_, lean_object* v_hi_204_, lean_object* v_val_205_, lean_object* v_h_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_Time_Internal_Bounded_LE_ofNatWrapping(v_lo_203_, v_hi_204_, v_val_205_, v_h_206_);
lean_dec(v_val_205_);
lean_dec(v_hi_204_);
lean_dec(v_lo_203_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(lean_object* v_lo_208_, lean_object* v_n_209_, lean_object* v_k_210_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v_range_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_211_ = lean_nat_to_int(v_k_210_);
v___x_212_ = lean_int_add(v_lo_208_, v___x_211_);
lean_dec(v___x_211_);
v___x_213_ = lean_nat_to_int(v_n_209_);
v___x_214_ = lean_int_sub(v___x_212_, v_lo_208_);
lean_dec(v___x_212_);
v___x_215_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v_range_216_ = lean_int_add(v___x_214_, v___x_215_);
lean_dec(v___x_214_);
v___x_217_ = lean_int_sub(v___x_213_, v_lo_208_);
lean_dec(v___x_213_);
v___x_218_ = lean_int_emod(v___x_217_, v_range_216_);
lean_dec(v___x_217_);
v___x_219_ = lean_int_add(v___x_218_, v_range_216_);
lean_dec(v___x_218_);
v___x_220_ = lean_int_emod(v___x_219_, v_range_216_);
lean_dec(v_range_216_);
lean_dec(v___x_219_);
v___x_221_ = lean_int_add(v___x_220_, v_lo_208_);
lean_dec(v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast___boxed(lean_object* v_lo_222_, lean_object* v_n_223_, lean_object* v_k_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(v_lo_222_, v_n_223_, v_k_224_);
lean_dec(v_lo_222_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instInhabitedHAddIntCast(lean_object* v_lo_226_, lean_object* v_k_227_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v_range_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_228_ = lean_nat_to_int(v_k_227_);
v___x_229_ = lean_int_add(v_lo_226_, v___x_228_);
lean_dec(v___x_228_);
v___x_230_ = lean_int_sub(v___x_229_, v_lo_226_);
lean_dec(v___x_229_);
v___x_231_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v_range_232_ = lean_int_add(v___x_230_, v___x_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_int_sub(v_lo_226_, v_lo_226_);
v___x_234_ = lean_int_emod(v___x_233_, v_range_232_);
lean_dec(v___x_233_);
v___x_235_ = lean_int_add(v___x_234_, v_range_232_);
lean_dec(v___x_234_);
v___x_236_ = lean_int_emod(v___x_235_, v_range_232_);
lean_dec(v_range_232_);
lean_dec(v___x_235_);
v___x_237_ = lean_int_add(v___x_236_, v_lo_226_);
lean_dec(v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instInhabitedHAddIntCast___boxed(lean_object* v_lo_238_, lean_object* v_k_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Std_Time_Internal_Bounded_LE_instInhabitedHAddIntCast(v_lo_238_, v_k_239_);
lean_dec(v_lo_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk___redArg(lean_object* v_val_241_){
_start:
{
lean_inc(v_val_241_);
return v_val_241_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk___redArg___boxed(lean_object* v_val_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Std_Time_Internal_Bounded_LE_mk___redArg(v_val_242_);
lean_dec(v_val_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk(lean_object* v_lo_244_, lean_object* v_hi_245_, lean_object* v_val_246_, lean_object* v_proof_247_){
_start:
{
lean_inc(v_val_246_);
return v_val_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk___boxed(lean_object* v_lo_248_, lean_object* v_hi_249_, lean_object* v_val_250_, lean_object* v_proof_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Std_Time_Internal_Bounded_LE_mk(v_lo_248_, v_hi_249_, v_val_250_, v_proof_251_);
lean_dec(v_val_250_);
lean_dec(v_hi_249_);
lean_dec(v_lo_248_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_exact(lean_object* v_val_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_nat_to_int(v_val_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofInt(lean_object* v_lo_255_, lean_object* v_hi_256_, lean_object* v_val_257_){
_start:
{
uint8_t v___x_258_; 
v___x_258_ = lean_int_dec_le(v_lo_255_, v_val_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
lean_dec(v_val_257_);
v___x_259_ = lean_box(0);
return v___x_259_;
}
else
{
uint8_t v___x_260_; 
v___x_260_ = lean_int_dec_le(v_val_257_, v_hi_256_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
lean_dec(v_val_257_);
v___x_261_ = lean_box(0);
return v___x_261_;
}
else
{
lean_object* v___x_262_; 
v___x_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_262_, 0, v_val_257_);
return v___x_262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofInt___boxed(lean_object* v_lo_263_, lean_object* v_hi_264_, lean_object* v_val_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Std_Time_Internal_Bounded_LE_ofInt(v_lo_263_, v_hi_264_, v_val_265_);
lean_dec(v_hi_264_);
lean_dec(v_lo_263_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat___redArg(lean_object* v_val_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_nat_to_int(v_val_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat(lean_object* v_hi_269_, lean_object* v_val_270_, lean_object* v_h_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lean_nat_to_int(v_val_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat___boxed(lean_object* v_hi_273_, lean_object* v_val_274_, lean_object* v_h_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Std_Time_Internal_Bounded_LE_ofNat(v_hi_273_, v_val_274_, v_h_275_);
lean_dec(v_hi_273_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x3f(lean_object* v_hi_277_, lean_object* v_val_278_){
_start:
{
uint8_t v___x_279_; 
v___x_279_ = lean_nat_dec_le(v_val_278_, v_hi_277_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
lean_dec(v_val_278_);
v___x_280_ = lean_box(0);
return v___x_280_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_nat_to_int(v_val_278_);
v___x_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x3f___boxed(lean_object* v_hi_283_, lean_object* v_val_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Std_Time_Internal_Bounded_LE_ofNat_x3f(v_hi_283_, v_val_284_);
lean_dec(v_hi_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27___redArg(lean_object* v_val_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_nat_to_int(v_val_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27(lean_object* v_lo_288_, lean_object* v_hi_289_, lean_object* v_val_290_, lean_object* v_h_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = lean_nat_to_int(v_val_290_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27___boxed(lean_object* v_lo_293_, lean_object* v_hi_294_, lean_object* v_val_295_, lean_object* v_h_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Std_Time_Internal_Bounded_LE_ofNat_x27(v_lo_293_, v_hi_294_, v_val_295_, v_h_296_);
lean_dec(v_hi_294_);
lean_dec(v_lo_293_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___redArg(lean_object* v_lo_298_, lean_object* v_hi_299_, lean_object* v_val_300_){
_start:
{
uint8_t v___x_301_; 
v___x_301_ = lean_int_dec_le(v_lo_298_, v_val_300_);
if (v___x_301_ == 0)
{
lean_inc(v_lo_298_);
return v_lo_298_;
}
else
{
uint8_t v___x_302_; 
v___x_302_ = lean_int_dec_le(v_val_300_, v_hi_299_);
if (v___x_302_ == 0)
{
lean_inc(v_hi_299_);
return v_hi_299_;
}
else
{
lean_inc(v_val_300_);
return v_val_300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___redArg___boxed(lean_object* v_lo_303_, lean_object* v_hi_304_, lean_object* v_val_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Std_Time_Internal_Bounded_LE_clip___redArg(v_lo_303_, v_hi_304_, v_val_305_);
lean_dec(v_val_305_);
lean_dec(v_hi_304_);
lean_dec(v_lo_303_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip(lean_object* v_lo_307_, lean_object* v_hi_308_, lean_object* v_val_309_, lean_object* v_h_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = lean_int_dec_le(v_lo_307_, v_val_309_);
if (v___x_311_ == 0)
{
lean_inc(v_lo_307_);
return v_lo_307_;
}
else
{
uint8_t v___x_312_; 
v___x_312_ = lean_int_dec_le(v_val_309_, v_hi_308_);
if (v___x_312_ == 0)
{
lean_inc(v_hi_308_);
return v_hi_308_;
}
else
{
lean_inc(v_val_309_);
return v_val_309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___boxed(lean_object* v_lo_313_, lean_object* v_hi_314_, lean_object* v_val_315_, lean_object* v_h_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Std_Time_Internal_Bounded_LE_clip(v_lo_313_, v_hi_314_, v_val_315_, v_h_316_);
lean_dec(v_val_315_);
lean_dec(v_hi_314_);
lean_dec(v_lo_313_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___redArg(lean_object* v_n_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Int_toNat(v_n_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___redArg___boxed(lean_object* v_n_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Std_Time_Internal_Bounded_LE_toNat___redArg(v_n_320_);
lean_dec(v_n_320_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat(lean_object* v_lo_322_, lean_object* v_hi_323_, lean_object* v_n_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Int_toNat(v_n_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___boxed(lean_object* v_lo_326_, lean_object* v_hi_327_, lean_object* v_n_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Std_Time_Internal_Bounded_LE_toNat(v_lo_326_, v_hi_327_, v_n_328_);
lean_dec(v_n_328_);
lean_dec(v_hi_327_);
lean_dec(v_lo_326_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg(lean_object* v_n_330_){
_start:
{
lean_object* v_intZero_331_; uint8_t v_isNeg_332_; lean_object* v_a_333_; 
v_intZero_331_ = lean_obj_once(&l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0, &l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0_once, _init_l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0);
v_isNeg_332_ = lean_int_dec_lt(v_n_330_, v_intZero_331_);
v_a_333_ = lean_nat_abs(v_n_330_);
return v_a_333_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg___boxed(lean_object* v_n_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg(v_n_334_);
lean_dec(v_n_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27(lean_object* v_lo_336_, lean_object* v_hi_337_, lean_object* v_n_338_, lean_object* v_h_339_){
_start:
{
lean_object* v_intZero_340_; uint8_t v_isNeg_341_; lean_object* v_a_342_; 
v_intZero_340_ = lean_obj_once(&l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0, &l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0_once, _init_l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0);
v_isNeg_341_ = lean_int_dec_lt(v_n_338_, v_intZero_340_);
v_a_342_ = lean_nat_abs(v_n_338_);
return v_a_342_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___boxed(lean_object* v_lo_343_, lean_object* v_hi_344_, lean_object* v_n_345_, lean_object* v_h_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Std_Time_Internal_Bounded_LE_toNat_x27(v_lo_343_, v_hi_344_, v_n_345_, v_h_346_);
lean_dec(v_n_345_);
lean_dec(v_hi_344_);
lean_dec(v_lo_343_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___redArg(lean_object* v_n_348_){
_start:
{
lean_inc(v_n_348_);
return v_n_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___redArg___boxed(lean_object* v_n_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_Time_Internal_Bounded_LE_toInt___redArg(v_n_349_);
lean_dec(v_n_349_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt(lean_object* v_lo_351_, lean_object* v_hi_352_, lean_object* v_n_353_){
_start:
{
lean_inc(v_n_353_);
return v_n_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___boxed(lean_object* v_lo_354_, lean_object* v_hi_355_, lean_object* v_n_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Std_Time_Internal_Bounded_LE_toInt(v_lo_354_, v_hi_355_, v_n_356_);
lean_dec(v_n_356_);
lean_dec(v_hi_355_);
lean_dec(v_lo_354_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___redArg(lean_object* v_n_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Int_toNat(v_n_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___redArg___boxed(lean_object* v_n_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_Time_Internal_Bounded_LE_toFin___redArg(v_n_360_);
lean_dec(v_n_360_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin(lean_object* v_lo_362_, lean_object* v_hi_363_, lean_object* v_n_364_, lean_object* v_h_u2080_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Int_toNat(v_n_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___boxed(lean_object* v_lo_367_, lean_object* v_hi_368_, lean_object* v_n_369_, lean_object* v_h_u2080_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Std_Time_Internal_Bounded_LE_toFin(v_lo_367_, v_hi_368_, v_n_369_, v_h_u2080_370_);
lean_dec(v_n_369_);
lean_dec(v_hi_368_);
lean_dec(v_lo_367_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin___redArg(lean_object* v_fin_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = lean_nat_to_int(v_fin_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin(lean_object* v_hi_374_, lean_object* v_fin_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = lean_nat_to_int(v_fin_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin___boxed(lean_object* v_hi_377_, lean_object* v_fin_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Std_Time_Internal_Bounded_LE_ofFin(v_hi_377_, v_fin_378_);
lean_dec(v_hi_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27___redArg(lean_object* v_lo_380_, lean_object* v_fin_381_){
_start:
{
uint8_t v___x_382_; 
v___x_382_ = lean_nat_dec_le(v_lo_380_, v_fin_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
lean_dec(v_fin_381_);
v___x_383_ = lean_nat_to_int(v_lo_380_);
return v___x_383_;
}
else
{
lean_object* v___x_384_; 
lean_dec(v_lo_380_);
v___x_384_ = lean_nat_to_int(v_fin_381_);
return v___x_384_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27(lean_object* v_hi_385_, lean_object* v_lo_386_, lean_object* v_fin_387_, lean_object* v_h_388_){
_start:
{
uint8_t v___x_389_; 
v___x_389_ = lean_nat_dec_le(v_lo_386_, v_fin_387_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; 
lean_dec(v_fin_387_);
v___x_390_ = lean_nat_to_int(v_lo_386_);
return v___x_390_;
}
else
{
lean_object* v___x_391_; 
lean_dec(v_lo_386_);
v___x_391_ = lean_nat_to_int(v_fin_387_);
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27___boxed(lean_object* v_hi_392_, lean_object* v_lo_393_, lean_object* v_fin_394_, lean_object* v_h_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Std_Time_Internal_Bounded_LE_ofFin_x27(v_hi_392_, v_lo_393_, v_fin_394_, v_h_395_);
lean_dec(v_hi_392_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___redArg(lean_object* v_b_397_, lean_object* v_i_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = lean_int_emod(v_b_397_, v_i_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___redArg___boxed(lean_object* v_b_400_, lean_object* v_i_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Std_Time_Internal_Bounded_LE_byEmod___redArg(v_b_400_, v_i_401_);
lean_dec(v_i_401_);
lean_dec(v_b_400_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod(lean_object* v_b_403_, lean_object* v_i_404_, lean_object* v_hi_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = lean_int_emod(v_b_403_, v_i_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___boxed(lean_object* v_b_407_, lean_object* v_i_408_, lean_object* v_hi_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Std_Time_Internal_Bounded_LE_byEmod(v_b_407_, v_i_408_, v_hi_409_);
lean_dec(v_i_408_);
lean_dec(v_b_407_);
return v_res_410_;
}
}
static lean_object* _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_411_; lean_object* v_intZero_412_; 
v_natZero_411_ = lean_unsigned_to_nat(0u);
v_intZero_412_ = lean_nat_to_int(v_natZero_411_);
return v_intZero_412_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg(lean_object* v_x_413_, lean_object* v_x_414_, lean_object* v_h__1_415_, lean_object* v_h__2_416_, lean_object* v_h__3_417_, lean_object* v_h__4_418_){
_start:
{
lean_object* v_intZero_419_; uint8_t v_isNeg_420_; 
v_intZero_419_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v_isNeg_420_ = lean_int_dec_lt(v_x_413_, v_intZero_419_);
if (v_isNeg_420_ == 0)
{
lean_object* v_a_421_; uint8_t v_isNeg_422_; 
lean_dec(v_h__4_418_);
lean_dec(v_h__3_417_);
v_a_421_ = lean_nat_abs(v_x_413_);
v_isNeg_422_ = lean_int_dec_lt(v_x_414_, v_intZero_419_);
if (v_isNeg_422_ == 0)
{
lean_object* v_a_423_; lean_object* v___x_424_; 
lean_dec(v_h__2_416_);
v_a_423_ = lean_nat_abs(v_x_414_);
v___x_424_ = lean_apply_2(v_h__1_415_, v_a_421_, v_a_423_);
return v___x_424_;
}
else
{
lean_object* v_abs_425_; lean_object* v_one_426_; lean_object* v_a_427_; lean_object* v___x_428_; 
lean_dec(v_h__1_415_);
v_abs_425_ = lean_nat_abs(v_x_414_);
v_one_426_ = lean_unsigned_to_nat(1u);
v_a_427_ = lean_nat_sub(v_abs_425_, v_one_426_);
lean_dec(v_abs_425_);
v___x_428_ = lean_apply_2(v_h__2_416_, v_a_421_, v_a_427_);
return v___x_428_;
}
}
else
{
lean_object* v_abs_429_; lean_object* v_one_430_; lean_object* v_a_431_; uint8_t v_isNeg_432_; 
lean_dec(v_h__2_416_);
lean_dec(v_h__1_415_);
v_abs_429_ = lean_nat_abs(v_x_413_);
v_one_430_ = lean_unsigned_to_nat(1u);
v_a_431_ = lean_nat_sub(v_abs_429_, v_one_430_);
lean_dec(v_abs_429_);
v_isNeg_432_ = lean_int_dec_lt(v_x_414_, v_intZero_419_);
if (v_isNeg_432_ == 0)
{
lean_object* v_a_433_; lean_object* v___x_434_; 
lean_dec(v_h__4_418_);
v_a_433_ = lean_nat_abs(v_x_414_);
v___x_434_ = lean_apply_2(v_h__3_417_, v_a_431_, v_a_433_);
return v___x_434_;
}
else
{
lean_object* v_abs_435_; lean_object* v_a_436_; lean_object* v___x_437_; 
lean_dec(v_h__3_417_);
v_abs_435_ = lean_nat_abs(v_x_414_);
v_a_436_ = lean_nat_sub(v_abs_435_, v_one_430_);
lean_dec(v_abs_435_);
v___x_437_ = lean_apply_2(v_h__4_418_, v_a_431_, v_a_436_);
return v___x_437_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___boxed(lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v_h__1_440_, lean_object* v_h__2_441_, lean_object* v_h__3_442_, lean_object* v_h__4_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg(v_x_438_, v_x_439_, v_h__1_440_, v_h__2_441_, v_h__3_442_, v_h__4_443_);
lean_dec(v_x_439_);
lean_dec(v_x_438_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter(lean_object* v_motive_445_, lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v_h__1_448_, lean_object* v_h__2_449_, lean_object* v_h__3_450_, lean_object* v_h__4_451_){
_start:
{
lean_object* v_intZero_452_; uint8_t v_isNeg_453_; 
v_intZero_452_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v_isNeg_453_ = lean_int_dec_lt(v_x_446_, v_intZero_452_);
if (v_isNeg_453_ == 0)
{
lean_object* v_a_454_; uint8_t v_isNeg_455_; 
lean_dec(v_h__4_451_);
lean_dec(v_h__3_450_);
v_a_454_ = lean_nat_abs(v_x_446_);
v_isNeg_455_ = lean_int_dec_lt(v_x_447_, v_intZero_452_);
if (v_isNeg_455_ == 0)
{
lean_object* v_a_456_; lean_object* v___x_457_; 
lean_dec(v_h__2_449_);
v_a_456_ = lean_nat_abs(v_x_447_);
v___x_457_ = lean_apply_2(v_h__1_448_, v_a_454_, v_a_456_);
return v___x_457_;
}
else
{
lean_object* v_abs_458_; lean_object* v_one_459_; lean_object* v_a_460_; lean_object* v___x_461_; 
lean_dec(v_h__1_448_);
v_abs_458_ = lean_nat_abs(v_x_447_);
v_one_459_ = lean_unsigned_to_nat(1u);
v_a_460_ = lean_nat_sub(v_abs_458_, v_one_459_);
lean_dec(v_abs_458_);
v___x_461_ = lean_apply_2(v_h__2_449_, v_a_454_, v_a_460_);
return v___x_461_;
}
}
else
{
lean_object* v_abs_462_; lean_object* v_one_463_; lean_object* v_a_464_; uint8_t v_isNeg_465_; 
lean_dec(v_h__2_449_);
lean_dec(v_h__1_448_);
v_abs_462_ = lean_nat_abs(v_x_446_);
v_one_463_ = lean_unsigned_to_nat(1u);
v_a_464_ = lean_nat_sub(v_abs_462_, v_one_463_);
lean_dec(v_abs_462_);
v_isNeg_465_ = lean_int_dec_lt(v_x_447_, v_intZero_452_);
if (v_isNeg_465_ == 0)
{
lean_object* v_a_466_; lean_object* v___x_467_; 
lean_dec(v_h__4_451_);
v_a_466_ = lean_nat_abs(v_x_447_);
v___x_467_ = lean_apply_2(v_h__3_450_, v_a_464_, v_a_466_);
return v___x_467_;
}
else
{
lean_object* v_abs_468_; lean_object* v_a_469_; lean_object* v___x_470_; 
lean_dec(v_h__3_450_);
v_abs_468_ = lean_nat_abs(v_x_447_);
v_a_469_ = lean_nat_sub(v_abs_468_, v_one_463_);
lean_dec(v_abs_468_);
v___x_470_ = lean_apply_2(v_h__4_451_, v_a_464_, v_a_469_);
return v___x_470_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___boxed(lean_object* v_motive_471_, lean_object* v_x_472_, lean_object* v_x_473_, lean_object* v_h__1_474_, lean_object* v_h__2_475_, lean_object* v_h__3_476_, lean_object* v_h__4_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter(v_motive_471_, v_x_472_, v_x_473_, v_h__1_474_, v_h__2_475_, v_h__3_476_, v_h__4_477_);
lean_dec(v_x_473_);
lean_dec(v_x_472_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___redArg(lean_object* v_b_479_, lean_object* v_i_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = lean_int_mod(v_b_479_, v_i_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___redArg___boxed(lean_object* v_b_482_, lean_object* v_i_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Std_Time_Internal_Bounded_LE_byMod___redArg(v_b_482_, v_i_483_);
lean_dec(v_i_483_);
lean_dec(v_b_482_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod(lean_object* v_b_485_, lean_object* v_i_486_, lean_object* v_hi_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = lean_int_mod(v_b_485_, v_i_486_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___boxed(lean_object* v_b_489_, lean_object* v_i_490_, lean_object* v_hi_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_Time_Internal_Bounded_LE_byMod(v_b_489_, v_i_490_, v_hi_491_);
lean_dec(v_i_490_);
lean_dec(v_b_489_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___redArg(lean_object* v_n_493_, lean_object* v_bounded_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_int_sub(v_bounded_494_, v_n_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___redArg___boxed(lean_object* v_n_496_, lean_object* v_bounded_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_Time_Internal_Bounded_LE_truncate___redArg(v_n_496_, v_bounded_497_);
lean_dec(v_bounded_497_);
lean_dec(v_n_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate(lean_object* v_n_499_, lean_object* v_m_500_, lean_object* v_bounded_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = lean_int_sub(v_bounded_501_, v_n_499_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___boxed(lean_object* v_n_503_, lean_object* v_m_504_, lean_object* v_bounded_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Std_Time_Internal_Bounded_LE_truncate(v_n_503_, v_m_504_, v_bounded_505_);
lean_dec(v_bounded_505_);
lean_dec(v_m_504_);
lean_dec(v_n_503_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___redArg(lean_object* v_bounded_507_){
_start:
{
lean_inc(v_bounded_507_);
return v_bounded_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___redArg___boxed(lean_object* v_bounded_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Std_Time_Internal_Bounded_LE_truncateTop___redArg(v_bounded_508_);
lean_dec(v_bounded_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop(lean_object* v_n_510_, lean_object* v_m_511_, lean_object* v_j_512_, lean_object* v_bounded_513_, lean_object* v_h_514_){
_start:
{
lean_inc(v_bounded_513_);
return v_bounded_513_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___boxed(lean_object* v_n_515_, lean_object* v_m_516_, lean_object* v_j_517_, lean_object* v_bounded_518_, lean_object* v_h_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Std_Time_Internal_Bounded_LE_truncateTop(v_n_515_, v_m_516_, v_j_517_, v_bounded_518_, v_h_519_);
lean_dec(v_bounded_518_);
lean_dec(v_j_517_);
lean_dec(v_m_516_);
lean_dec(v_n_515_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg(lean_object* v_bounded_521_){
_start:
{
lean_inc(v_bounded_521_);
return v_bounded_521_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg___boxed(lean_object* v_bounded_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg(v_bounded_522_);
lean_dec(v_bounded_522_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom(lean_object* v_n_524_, lean_object* v_m_525_, lean_object* v_j_526_, lean_object* v_bounded_527_, lean_object* v_h_528_){
_start:
{
lean_inc(v_bounded_527_);
return v_bounded_527_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___boxed(lean_object* v_n_529_, lean_object* v_m_530_, lean_object* v_j_531_, lean_object* v_bounded_532_, lean_object* v_h_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_Time_Internal_Bounded_LE_truncateBottom(v_n_529_, v_m_530_, v_j_531_, v_bounded_532_, v_h_533_);
lean_dec(v_bounded_532_);
lean_dec(v_j_531_);
lean_dec(v_m_530_);
lean_dec(v_n_529_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___redArg(lean_object* v_bounded_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = lean_int_neg(v_bounded_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___redArg___boxed(lean_object* v_bounded_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_Time_Internal_Bounded_LE_neg___redArg(v_bounded_537_);
lean_dec(v_bounded_537_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg(lean_object* v_n_539_, lean_object* v_m_540_, lean_object* v_bounded_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = lean_int_neg(v_bounded_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___boxed(lean_object* v_n_543_, lean_object* v_m_544_, lean_object* v_bounded_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Std_Time_Internal_Bounded_LE_neg(v_n_543_, v_m_544_, v_bounded_545_);
lean_dec(v_bounded_545_);
lean_dec(v_m_544_);
lean_dec(v_n_543_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___redArg(lean_object* v_bounded_547_, lean_object* v_num_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = lean_int_add(v_bounded_547_, v_num_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___redArg___boxed(lean_object* v_bounded_550_, lean_object* v_num_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Std_Time_Internal_Bounded_LE_add___redArg(v_bounded_550_, v_num_551_);
lean_dec(v_num_551_);
lean_dec(v_bounded_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add(lean_object* v_n_553_, lean_object* v_m_554_, lean_object* v_bounded_555_, lean_object* v_num_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = lean_int_add(v_bounded_555_, v_num_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___boxed(lean_object* v_n_558_, lean_object* v_m_559_, lean_object* v_bounded_560_, lean_object* v_num_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Std_Time_Internal_Bounded_LE_add(v_n_558_, v_m_559_, v_bounded_560_, v_num_561_);
lean_dec(v_num_561_);
lean_dec(v_bounded_560_);
lean_dec(v_m_559_);
lean_dec(v_n_558_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___redArg(lean_object* v_num_563_, lean_object* v_bounded_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = lean_int_add(v_bounded_564_, v_num_563_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___redArg___boxed(lean_object* v_num_566_, lean_object* v_bounded_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Std_Time_Internal_Bounded_LE_addProven___redArg(v_num_566_, v_bounded_567_);
lean_dec(v_bounded_567_);
lean_dec(v_num_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven(lean_object* v_n_569_, lean_object* v_m_570_, lean_object* v_num_571_, lean_object* v_bounded_572_, lean_object* v_h_u2080_573_, lean_object* v_h_u2081_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = lean_int_add(v_bounded_572_, v_num_571_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___boxed(lean_object* v_n_576_, lean_object* v_m_577_, lean_object* v_num_578_, lean_object* v_bounded_579_, lean_object* v_h_u2080_580_, lean_object* v_h_u2081_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Std_Time_Internal_Bounded_LE_addProven(v_n_576_, v_m_577_, v_num_578_, v_bounded_579_, v_h_u2080_580_, v_h_u2081_581_);
lean_dec(v_bounded_579_);
lean_dec(v_num_578_);
lean_dec(v_m_577_);
lean_dec(v_n_576_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___redArg(lean_object* v_bounded_583_, lean_object* v_num_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = lean_int_add(v_bounded_583_, v_num_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___redArg___boxed(lean_object* v_bounded_586_, lean_object* v_num_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Std_Time_Internal_Bounded_LE_addTop___redArg(v_bounded_586_, v_num_587_);
lean_dec(v_num_587_);
lean_dec(v_bounded_586_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop(lean_object* v_n_589_, lean_object* v_m_590_, lean_object* v_bounded_591_, lean_object* v_num_592_, lean_object* v_h_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = lean_int_add(v_bounded_591_, v_num_592_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___boxed(lean_object* v_n_595_, lean_object* v_m_596_, lean_object* v_bounded_597_, lean_object* v_num_598_, lean_object* v_h_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Std_Time_Internal_Bounded_LE_addTop(v_n_595_, v_m_596_, v_bounded_597_, v_num_598_, v_h_599_);
lean_dec(v_num_598_);
lean_dec(v_bounded_597_);
lean_dec(v_m_596_);
lean_dec(v_n_595_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___redArg(lean_object* v_bounded_601_, lean_object* v_num_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = lean_int_sub(v_bounded_601_, v_num_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___redArg___boxed(lean_object* v_bounded_604_, lean_object* v_num_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Std_Time_Internal_Bounded_LE_subBottom___redArg(v_bounded_604_, v_num_605_);
lean_dec(v_num_605_);
lean_dec(v_bounded_604_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom(lean_object* v_n_607_, lean_object* v_m_608_, lean_object* v_bounded_609_, lean_object* v_num_610_, lean_object* v_h_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = lean_int_sub(v_bounded_609_, v_num_610_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___boxed(lean_object* v_n_613_, lean_object* v_m_614_, lean_object* v_bounded_615_, lean_object* v_num_616_, lean_object* v_h_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Std_Time_Internal_Bounded_LE_subBottom(v_n_613_, v_m_614_, v_bounded_615_, v_num_616_, v_h_617_);
lean_dec(v_num_616_);
lean_dec(v_bounded_615_);
lean_dec(v_m_614_);
lean_dec(v_n_613_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___redArg(lean_object* v_bounded_619_, lean_object* v_bounded_u2082_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = lean_int_add(v_bounded_619_, v_bounded_u2082_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___redArg___boxed(lean_object* v_bounded_622_, lean_object* v_bounded_u2082_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Std_Time_Internal_Bounded_LE_addBounds___redArg(v_bounded_622_, v_bounded_u2082_623_);
lean_dec(v_bounded_u2082_623_);
lean_dec(v_bounded_622_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds(lean_object* v_n_625_, lean_object* v_m_626_, lean_object* v_i_627_, lean_object* v_j_628_, lean_object* v_bounded_629_, lean_object* v_bounded_u2082_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = lean_int_add(v_bounded_629_, v_bounded_u2082_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___boxed(lean_object* v_n_632_, lean_object* v_m_633_, lean_object* v_i_634_, lean_object* v_j_635_, lean_object* v_bounded_636_, lean_object* v_bounded_u2082_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Std_Time_Internal_Bounded_LE_addBounds(v_n_632_, v_m_633_, v_i_634_, v_j_635_, v_bounded_636_, v_bounded_u2082_637_);
lean_dec(v_bounded_u2082_637_);
lean_dec(v_bounded_636_);
lean_dec(v_j_635_);
lean_dec(v_i_634_);
lean_dec(v_m_633_);
lean_dec(v_n_632_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___redArg(lean_object* v_bounded_639_, lean_object* v_num_640_){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_int_neg(v_num_640_);
v___x_642_ = lean_int_add(v_bounded_639_, v___x_641_);
lean_dec(v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___redArg___boxed(lean_object* v_bounded_643_, lean_object* v_num_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Std_Time_Internal_Bounded_LE_sub___redArg(v_bounded_643_, v_num_644_);
lean_dec(v_num_644_);
lean_dec(v_bounded_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub(lean_object* v_n_646_, lean_object* v_m_647_, lean_object* v_bounded_648_, lean_object* v_num_649_){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_int_neg(v_num_649_);
v___x_651_ = lean_int_add(v_bounded_648_, v___x_650_);
lean_dec(v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___boxed(lean_object* v_n_652_, lean_object* v_m_653_, lean_object* v_bounded_654_, lean_object* v_num_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Std_Time_Internal_Bounded_LE_sub(v_n_652_, v_m_653_, v_bounded_654_, v_num_655_);
lean_dec(v_num_655_);
lean_dec(v_bounded_654_);
lean_dec(v_m_653_);
lean_dec(v_n_652_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___redArg(lean_object* v_bounded_657_, lean_object* v_bounded_u2082_658_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_int_neg(v_bounded_u2082_658_);
v___x_660_ = lean_int_add(v_bounded_657_, v___x_659_);
lean_dec(v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___redArg___boxed(lean_object* v_bounded_661_, lean_object* v_bounded_u2082_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Std_Time_Internal_Bounded_LE_subBounds___redArg(v_bounded_661_, v_bounded_u2082_662_);
lean_dec(v_bounded_u2082_662_);
lean_dec(v_bounded_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds(lean_object* v_n_664_, lean_object* v_m_665_, lean_object* v_i_666_, lean_object* v_j_667_, lean_object* v_bounded_668_, lean_object* v_bounded_u2082_669_){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_int_neg(v_bounded_u2082_669_);
v___x_671_ = lean_int_add(v_bounded_668_, v___x_670_);
lean_dec(v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___boxed(lean_object* v_n_672_, lean_object* v_m_673_, lean_object* v_i_674_, lean_object* v_j_675_, lean_object* v_bounded_676_, lean_object* v_bounded_u2082_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Std_Time_Internal_Bounded_LE_subBounds(v_n_672_, v_m_673_, v_i_674_, v_j_675_, v_bounded_676_, v_bounded_u2082_677_);
lean_dec(v_bounded_u2082_677_);
lean_dec(v_bounded_676_);
lean_dec(v_j_675_);
lean_dec(v_i_674_);
lean_dec(v_m_673_);
lean_dec(v_n_672_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___redArg(lean_object* v_bounded_679_, lean_object* v_num_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = lean_int_emod(v_bounded_679_, v_num_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___redArg___boxed(lean_object* v_bounded_682_, lean_object* v_num_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Std_Time_Internal_Bounded_LE_emod___redArg(v_bounded_682_, v_num_683_);
lean_dec(v_num_683_);
lean_dec(v_bounded_682_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod(lean_object* v_n_685_, lean_object* v_num_686_, lean_object* v_bounded_687_, lean_object* v_num_688_, lean_object* v_hi_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = lean_int_emod(v_bounded_687_, v_num_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___boxed(lean_object* v_n_691_, lean_object* v_num_692_, lean_object* v_bounded_693_, lean_object* v_num_694_, lean_object* v_hi_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Std_Time_Internal_Bounded_LE_emod(v_n_691_, v_num_692_, v_bounded_693_, v_num_694_, v_hi_695_);
lean_dec(v_num_694_);
lean_dec(v_bounded_693_);
lean_dec(v_num_692_);
lean_dec(v_n_691_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___redArg(lean_object* v_bounded_697_, lean_object* v_num_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = lean_int_mod(v_bounded_697_, v_num_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___redArg___boxed(lean_object* v_bounded_700_, lean_object* v_num_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Std_Time_Internal_Bounded_LE_mod___redArg(v_bounded_700_, v_num_701_);
lean_dec(v_num_701_);
lean_dec(v_bounded_700_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod(lean_object* v_n_703_, lean_object* v_num_704_, lean_object* v_bounded_705_, lean_object* v_num_706_, lean_object* v_hi_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = lean_int_mod(v_bounded_705_, v_num_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___boxed(lean_object* v_n_709_, lean_object* v_num_710_, lean_object* v_bounded_711_, lean_object* v_num_712_, lean_object* v_hi_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Std_Time_Internal_Bounded_LE_mod(v_n_709_, v_num_710_, v_bounded_711_, v_num_712_, v_hi_713_);
lean_dec(v_num_712_);
lean_dec(v_bounded_711_);
lean_dec(v_num_710_);
lean_dec(v_n_709_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___redArg(lean_object* v_bounded_715_, lean_object* v_num_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = lean_int_mul(v_bounded_715_, v_num_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___redArg___boxed(lean_object* v_bounded_718_, lean_object* v_num_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_Time_Internal_Bounded_LE_mul__pos___redArg(v_bounded_718_, v_num_719_);
lean_dec(v_num_719_);
lean_dec(v_bounded_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos(lean_object* v_n_721_, lean_object* v_m_722_, lean_object* v_bounded_723_, lean_object* v_num_724_, lean_object* v_h_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = lean_int_mul(v_bounded_723_, v_num_724_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___boxed(lean_object* v_n_727_, lean_object* v_m_728_, lean_object* v_bounded_729_, lean_object* v_num_730_, lean_object* v_h_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Std_Time_Internal_Bounded_LE_mul__pos(v_n_727_, v_m_728_, v_bounded_729_, v_num_730_, v_h_731_);
lean_dec(v_num_730_);
lean_dec(v_bounded_729_);
lean_dec(v_m_728_);
lean_dec(v_n_727_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___redArg(lean_object* v_bounded_733_, lean_object* v_num_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = lean_int_mul(v_bounded_733_, v_num_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___redArg___boxed(lean_object* v_bounded_736_, lean_object* v_num_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Std_Time_Internal_Bounded_LE_mul__neg___redArg(v_bounded_736_, v_num_737_);
lean_dec(v_num_737_);
lean_dec(v_bounded_736_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg(lean_object* v_n_739_, lean_object* v_m_740_, lean_object* v_bounded_741_, lean_object* v_num_742_, lean_object* v_h_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = lean_int_mul(v_bounded_741_, v_num_742_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___boxed(lean_object* v_n_745_, lean_object* v_m_746_, lean_object* v_bounded_747_, lean_object* v_num_748_, lean_object* v_h_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Std_Time_Internal_Bounded_LE_mul__neg(v_n_745_, v_m_746_, v_bounded_747_, v_num_748_, v_h_749_);
lean_dec(v_num_748_);
lean_dec(v_bounded_747_);
lean_dec(v_m_746_);
lean_dec(v_n_745_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___redArg(lean_object* v_bounded_751_, lean_object* v_num_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = lean_int_ediv(v_bounded_751_, v_num_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___redArg___boxed(lean_object* v_bounded_754_, lean_object* v_num_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_Time_Internal_Bounded_LE_ediv___redArg(v_bounded_754_, v_num_755_);
lean_dec(v_num_755_);
lean_dec(v_bounded_754_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv(lean_object* v_n_757_, lean_object* v_m_758_, lean_object* v_bounded_759_, lean_object* v_num_760_, lean_object* v_h_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = lean_int_ediv(v_bounded_759_, v_num_760_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___boxed(lean_object* v_n_763_, lean_object* v_m_764_, lean_object* v_bounded_765_, lean_object* v_num_766_, lean_object* v_h_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_Time_Internal_Bounded_LE_ediv(v_n_763_, v_m_764_, v_bounded_765_, v_num_766_, v_h_767_);
lean_dec(v_num_766_);
lean_dec(v_bounded_765_);
lean_dec(v_m_764_);
lean_dec(v_n_763_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_eq(lean_object* v_n_769_){
_start:
{
lean_inc(v_n_769_);
return v_n_769_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_eq___boxed(lean_object* v_n_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Std_Time_Internal_Bounded_LE_eq(v_n_770_);
lean_dec(v_n_770_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___redArg(lean_object* v_bounded_772_){
_start:
{
lean_inc(v_bounded_772_);
return v_bounded_772_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___redArg___boxed(lean_object* v_bounded_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Std_Time_Internal_Bounded_LE_expand___redArg(v_bounded_773_);
lean_dec(v_bounded_773_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand(lean_object* v_lo_775_, lean_object* v_hi_776_, lean_object* v_nhi_777_, lean_object* v_nlo_778_, lean_object* v_bounded_779_, lean_object* v_h_780_, lean_object* v_h_u2081_781_){
_start:
{
lean_inc(v_bounded_779_);
return v_bounded_779_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___boxed(lean_object* v_lo_782_, lean_object* v_hi_783_, lean_object* v_nhi_784_, lean_object* v_nlo_785_, lean_object* v_bounded_786_, lean_object* v_h_787_, lean_object* v_h_u2081_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Std_Time_Internal_Bounded_LE_expand(v_lo_782_, v_hi_783_, v_nhi_784_, v_nlo_785_, v_bounded_786_, v_h_787_, v_h_u2081_788_);
lean_dec(v_bounded_786_);
lean_dec(v_nlo_785_);
lean_dec(v_nhi_784_);
lean_dec(v_hi_783_);
lean_dec(v_lo_782_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___redArg(lean_object* v_bounded_790_){
_start:
{
lean_inc(v_bounded_790_);
return v_bounded_790_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___redArg___boxed(lean_object* v_bounded_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Std_Time_Internal_Bounded_LE_expandTop___redArg(v_bounded_791_);
lean_dec(v_bounded_791_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop(lean_object* v_lo_793_, lean_object* v_hi_794_, lean_object* v_nhi_795_, lean_object* v_bounded_796_, lean_object* v_h_797_){
_start:
{
lean_inc(v_bounded_796_);
return v_bounded_796_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___boxed(lean_object* v_lo_798_, lean_object* v_hi_799_, lean_object* v_nhi_800_, lean_object* v_bounded_801_, lean_object* v_h_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Std_Time_Internal_Bounded_LE_expandTop(v_lo_798_, v_hi_799_, v_nhi_800_, v_bounded_801_, v_h_802_);
lean_dec(v_bounded_801_);
lean_dec(v_nhi_800_);
lean_dec(v_hi_799_);
lean_dec(v_lo_798_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___redArg(lean_object* v_bounded_804_){
_start:
{
lean_inc(v_bounded_804_);
return v_bounded_804_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___redArg___boxed(lean_object* v_bounded_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_Time_Internal_Bounded_LE_expandBottom___redArg(v_bounded_805_);
lean_dec(v_bounded_805_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom(lean_object* v_lo_807_, lean_object* v_hi_808_, lean_object* v_nlo_809_, lean_object* v_bounded_810_, lean_object* v_h_811_){
_start:
{
lean_inc(v_bounded_810_);
return v_bounded_810_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___boxed(lean_object* v_lo_812_, lean_object* v_hi_813_, lean_object* v_nlo_814_, lean_object* v_bounded_815_, lean_object* v_h_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_Time_Internal_Bounded_LE_expandBottom(v_lo_812_, v_hi_813_, v_nlo_814_, v_bounded_815_, v_h_816_);
lean_dec(v_bounded_815_);
lean_dec(v_nlo_814_);
lean_dec(v_hi_813_);
lean_dec(v_lo_812_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___redArg(lean_object* v_bounded_818_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v___x_820_ = lean_int_add(v_bounded_818_, v___x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___redArg___boxed(lean_object* v_bounded_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_Time_Internal_Bounded_LE_succ___redArg(v_bounded_821_);
lean_dec(v_bounded_821_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ(lean_object* v_lo_823_, lean_object* v_hi_824_, lean_object* v_bounded_825_, lean_object* v_h_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v___x_828_ = lean_int_add(v_bounded_825_, v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___boxed(lean_object* v_lo_829_, lean_object* v_hi_830_, lean_object* v_bounded_831_, lean_object* v_h_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Std_Time_Internal_Bounded_LE_succ(v_lo_829_, v_hi_830_, v_bounded_831_, v_h_832_);
lean_dec(v_bounded_831_);
lean_dec(v_hi_830_);
lean_dec(v_lo_829_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___redArg(lean_object* v_bo_834_){
_start:
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v___x_836_ = lean_int_dec_le(v___x_835_, v_bo_834_);
if (v___x_836_ == 0)
{
lean_object* v_r_837_; 
v_r_837_ = lean_int_neg(v_bo_834_);
return v_r_837_;
}
else
{
lean_inc(v_bo_834_);
return v_bo_834_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___redArg___boxed(lean_object* v_bo_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Std_Time_Internal_Bounded_LE_abs___redArg(v_bo_838_);
lean_dec(v_bo_838_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs(lean_object* v_i_840_, lean_object* v_bo_841_){
_start:
{
lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_842_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v___x_843_ = lean_int_dec_le(v___x_842_, v_bo_841_);
if (v___x_843_ == 0)
{
lean_object* v_r_844_; 
v_r_844_ = lean_int_neg(v_bo_841_);
return v_r_844_;
}
else
{
lean_inc(v_bo_841_);
return v_bo_841_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___boxed(lean_object* v_i_845_, lean_object* v_bo_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Std_Time_Internal_Bounded_LE_abs(v_i_845_, v_bo_846_);
lean_dec(v_bo_846_);
lean_dec(v_i_845_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___redArg(lean_object* v_bounded_848_, lean_object* v_val_849_){
_start:
{
uint8_t v___x_850_; 
v___x_850_ = lean_int_dec_le(v_bounded_848_, v_val_849_);
if (v___x_850_ == 0)
{
lean_inc(v_bounded_848_);
return v_bounded_848_;
}
else
{
lean_inc(v_val_849_);
return v_val_849_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___redArg___boxed(lean_object* v_bounded_851_, lean_object* v_val_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Std_Time_Internal_Bounded_LE_max___redArg(v_bounded_851_, v_val_852_);
lean_dec(v_val_852_);
lean_dec(v_bounded_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max(lean_object* v_n_854_, lean_object* v_m_855_, lean_object* v_bounded_856_, lean_object* v_val_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Std_Time_Internal_Bounded_LE_max___redArg(v_bounded_856_, v_val_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___boxed(lean_object* v_n_859_, lean_object* v_m_860_, lean_object* v_bounded_861_, lean_object* v_val_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Std_Time_Internal_Bounded_LE_max(v_n_859_, v_m_860_, v_bounded_861_, v_val_862_);
lean_dec(v_val_862_);
lean_dec(v_bounded_861_);
lean_dec(v_m_860_);
lean_dec(v_n_859_);
return v_res_863_;
}
}
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Repr(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Internal_Bounded(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
