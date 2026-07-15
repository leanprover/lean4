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
lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableLe___redArg(lean_object* v_x_76_, lean_object* v_y_77_){
_start:
{
uint8_t v___x_78_; 
v___x_78_ = lean_int_dec_le(v_x_76_, v_y_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableLe___redArg___boxed(lean_object* v_x_79_, lean_object* v_y_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Std_Time_Internal_Bounded_instDecidableLe___redArg(v_x_79_, v_y_80_);
lean_dec(v_y_80_);
lean_dec(v_x_79_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_Bounded_instDecidableLe(lean_object* v_rel_83_, lean_object* v_a_84_, lean_object* v_b_85_, lean_object* v_x_86_, lean_object* v_y_87_){
_start:
{
uint8_t v___x_88_; 
v___x_88_ = lean_int_dec_le(v_x_86_, v_y_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_instDecidableLe___boxed(lean_object* v_rel_89_, lean_object* v_a_90_, lean_object* v_b_91_, lean_object* v_x_92_, lean_object* v_y_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Std_Time_Internal_Bounded_instDecidableLe(v_rel_89_, v_a_90_, v_b_91_, v_x_92_, v_y_93_);
lean_dec(v_y_93_);
lean_dec(v_x_92_);
lean_dec(v_b_91_);
lean_dec(v_a_90_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast___redArg(lean_object* v_b_96_){
_start:
{
lean_inc(v_b_96_);
return v_b_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast___redArg___boxed(lean_object* v_b_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Std_Time_Internal_Bounded_cast___redArg(v_b_97_);
lean_dec(v_b_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast(lean_object* v_rel_99_, lean_object* v_lo_u2081_100_, lean_object* v_lo_u2082_101_, lean_object* v_hi_u2081_102_, lean_object* v_hi_u2082_103_, lean_object* v_h_u2081_104_, lean_object* v_h_u2082_105_, lean_object* v_b_106_){
_start:
{
lean_inc(v_b_106_);
return v_b_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_cast___boxed(lean_object* v_rel_107_, lean_object* v_lo_u2081_108_, lean_object* v_lo_u2082_109_, lean_object* v_hi_u2081_110_, lean_object* v_hi_u2082_111_, lean_object* v_h_u2081_112_, lean_object* v_h_u2082_113_, lean_object* v_b_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Std_Time_Internal_Bounded_cast(v_rel_107_, v_lo_u2081_108_, v_lo_u2082_109_, v_hi_u2081_110_, v_hi_u2082_111_, v_h_u2081_112_, v_h_u2082_113_, v_b_114_);
lean_dec(v_b_114_);
lean_dec(v_hi_u2082_111_);
lean_dec(v_hi_u2081_110_);
lean_dec(v_lo_u2082_109_);
lean_dec(v_lo_u2081_108_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk___redArg(lean_object* v_val_116_){
_start:
{
lean_inc(v_val_116_);
return v_val_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk___redArg___boxed(lean_object* v_val_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Std_Time_Internal_Bounded_mk___redArg(v_val_117_);
lean_dec(v_val_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk(lean_object* v_lo_119_, lean_object* v_hi_120_, lean_object* v_rel_121_, lean_object* v_val_122_, lean_object* v_proof_123_){
_start:
{
lean_inc(v_val_122_);
return v_val_122_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_mk___boxed(lean_object* v_lo_124_, lean_object* v_hi_125_, lean_object* v_rel_126_, lean_object* v_val_127_, lean_object* v_proof_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Std_Time_Internal_Bounded_mk(v_lo_124_, v_hi_125_, v_rel_126_, v_val_127_, v_proof_128_);
lean_dec(v_val_127_);
lean_dec(v_hi_125_);
lean_dec(v_lo_124_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_ofInt_x3f___redArg(lean_object* v_lo_130_, lean_object* v_hi_131_, lean_object* v_inst_132_, lean_object* v_val_133_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
lean_inc_ref(v_inst_132_);
lean_inc_n(v_val_133_, 2);
v___x_134_ = lean_apply_2(v_inst_132_, v_val_133_, v_hi_131_);
v___x_135_ = lean_apply_2(v_inst_132_, v_lo_130_, v_val_133_);
v___x_136_ = lean_unbox(v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; 
lean_dec(v_val_133_);
v___x_137_ = lean_box(0);
return v___x_137_;
}
else
{
uint8_t v___x_138_; 
v___x_138_ = lean_unbox(v___x_134_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; 
lean_dec(v_val_133_);
v___x_139_ = lean_box(0);
return v___x_139_;
}
else
{
lean_object* v___x_140_; 
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v_val_133_);
return v___x_140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_ofInt_x3f(lean_object* v_rel_141_, lean_object* v_lo_142_, lean_object* v_hi_143_, lean_object* v_inst_144_, lean_object* v_val_145_){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
lean_inc_ref(v_inst_144_);
lean_inc_n(v_val_145_, 2);
v___x_146_ = lean_apply_2(v_inst_144_, v_val_145_, v_hi_143_);
v___x_147_ = lean_apply_2(v_inst_144_, v_lo_142_, v_val_145_);
v___x_148_ = lean_unbox(v___x_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; 
lean_dec(v_val_145_);
v___x_149_ = lean_box(0);
return v___x_149_;
}
else
{
uint8_t v___x_150_; 
v___x_150_ = lean_unbox(v___x_146_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; 
lean_dec(v_val_145_);
v___x_151_ = lean_box(0);
return v___x_151_;
}
else
{
lean_object* v___x_152_; 
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v_val_145_);
return v___x_152_;
}
}
}
}
static lean_object* _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(1u);
v___x_154_ = lean_nat_to_int(v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg(lean_object* v_lo_155_, lean_object* v_hi_156_, lean_object* v_val_157_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v_range_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_158_ = lean_int_sub(v_hi_156_, v_lo_155_);
v___x_159_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v_range_160_ = lean_int_add(v___x_158_, v___x_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_int_sub(v_val_157_, v_lo_155_);
v___x_162_ = lean_int_emod(v___x_161_, v_range_160_);
lean_dec(v___x_161_);
v___x_163_ = lean_int_add(v___x_162_, v_range_160_);
lean_dec(v___x_162_);
v___x_164_ = lean_int_emod(v___x_163_, v_range_160_);
lean_dec(v_range_160_);
lean_dec(v___x_163_);
v___x_165_ = lean_int_add(v___x_164_, v_lo_155_);
lean_dec(v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___boxed(lean_object* v_lo_166_, lean_object* v_hi_167_, lean_object* v_val_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg(v_lo_166_, v_hi_167_, v_val_168_);
lean_dec(v_val_168_);
lean_dec(v_hi_167_);
lean_dec(v_lo_166_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping(lean_object* v_lo_170_, lean_object* v_hi_171_, lean_object* v_val_172_, lean_object* v_h_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v_range_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_174_ = lean_int_sub(v_hi_171_, v_lo_170_);
v___x_175_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v_range_176_ = lean_int_add(v___x_174_, v___x_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_int_sub(v_val_172_, v_lo_170_);
v___x_178_ = lean_int_emod(v___x_177_, v_range_176_);
lean_dec(v___x_177_);
v___x_179_ = lean_int_add(v___x_178_, v_range_176_);
lean_dec(v___x_178_);
v___x_180_ = lean_int_emod(v___x_179_, v_range_176_);
lean_dec(v_range_176_);
lean_dec(v___x_179_);
v___x_181_ = lean_int_add(v___x_180_, v_lo_170_);
lean_dec(v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNatWrapping___boxed(lean_object* v_lo_182_, lean_object* v_hi_183_, lean_object* v_val_184_, lean_object* v_h_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Std_Time_Internal_Bounded_LE_ofNatWrapping(v_lo_182_, v_hi_183_, v_val_184_, v_h_185_);
lean_dec(v_val_184_);
lean_dec(v_hi_183_);
lean_dec(v_lo_182_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(lean_object* v_lo_187_, lean_object* v_n_188_, lean_object* v_k_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v_range_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_190_ = lean_nat_to_int(v_k_189_);
v___x_191_ = lean_int_add(v_lo_187_, v___x_190_);
lean_dec(v___x_190_);
v___x_192_ = lean_nat_to_int(v_n_188_);
v___x_193_ = lean_int_sub(v___x_191_, v_lo_187_);
lean_dec(v___x_191_);
v___x_194_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v_range_195_ = lean_int_add(v___x_193_, v___x_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_int_sub(v___x_192_, v_lo_187_);
lean_dec(v___x_192_);
v___x_197_ = lean_int_emod(v___x_196_, v_range_195_);
lean_dec(v___x_196_);
v___x_198_ = lean_int_add(v___x_197_, v_range_195_);
lean_dec(v___x_197_);
v___x_199_ = lean_int_emod(v___x_198_, v_range_195_);
lean_dec(v_range_195_);
lean_dec(v___x_198_);
v___x_200_ = lean_int_add(v___x_199_, v_lo_187_);
lean_dec(v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast___boxed(lean_object* v_lo_201_, lean_object* v_n_202_, lean_object* v_k_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(v_lo_201_, v_n_202_, v_k_203_);
lean_dec(v_lo_201_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instInhabitedHAddIntCast(lean_object* v_lo_205_, lean_object* v_k_206_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v_range_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_207_ = lean_nat_to_int(v_k_206_);
v___x_208_ = lean_int_add(v_lo_205_, v___x_207_);
lean_dec(v___x_207_);
v___x_209_ = lean_int_sub(v___x_208_, v_lo_205_);
lean_dec(v___x_208_);
v___x_210_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v_range_211_ = lean_int_add(v___x_209_, v___x_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_int_sub(v_lo_205_, v_lo_205_);
v___x_213_ = lean_int_emod(v___x_212_, v_range_211_);
lean_dec(v___x_212_);
v___x_214_ = lean_int_add(v___x_213_, v_range_211_);
lean_dec(v___x_213_);
v___x_215_ = lean_int_emod(v___x_214_, v_range_211_);
lean_dec(v_range_211_);
lean_dec(v___x_214_);
v___x_216_ = lean_int_add(v___x_215_, v_lo_205_);
lean_dec(v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_instInhabitedHAddIntCast___boxed(lean_object* v_lo_217_, lean_object* v_k_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Std_Time_Internal_Bounded_LE_instInhabitedHAddIntCast(v_lo_217_, v_k_218_);
lean_dec(v_lo_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk___redArg(lean_object* v_val_220_){
_start:
{
lean_inc(v_val_220_);
return v_val_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk___redArg___boxed(lean_object* v_val_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Std_Time_Internal_Bounded_LE_mk___redArg(v_val_221_);
lean_dec(v_val_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk(lean_object* v_lo_223_, lean_object* v_hi_224_, lean_object* v_val_225_, lean_object* v_proof_226_){
_start:
{
lean_inc(v_val_225_);
return v_val_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mk___boxed(lean_object* v_lo_227_, lean_object* v_hi_228_, lean_object* v_val_229_, lean_object* v_proof_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Std_Time_Internal_Bounded_LE_mk(v_lo_227_, v_hi_228_, v_val_229_, v_proof_230_);
lean_dec(v_val_229_);
lean_dec(v_hi_228_);
lean_dec(v_lo_227_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_exact(lean_object* v_val_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_nat_to_int(v_val_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofInt(lean_object* v_lo_234_, lean_object* v_hi_235_, lean_object* v_val_236_){
_start:
{
uint8_t v___x_237_; 
v___x_237_ = lean_int_dec_le(v_lo_234_, v_val_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; 
lean_dec(v_val_236_);
v___x_238_ = lean_box(0);
return v___x_238_;
}
else
{
uint8_t v___x_239_; 
v___x_239_ = lean_int_dec_le(v_val_236_, v_hi_235_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; 
lean_dec(v_val_236_);
v___x_240_ = lean_box(0);
return v___x_240_;
}
else
{
lean_object* v___x_241_; 
v___x_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_241_, 0, v_val_236_);
return v___x_241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofInt___boxed(lean_object* v_lo_242_, lean_object* v_hi_243_, lean_object* v_val_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_Time_Internal_Bounded_LE_ofInt(v_lo_242_, v_hi_243_, v_val_244_);
lean_dec(v_hi_243_);
lean_dec(v_lo_242_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat___redArg(lean_object* v_val_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = lean_nat_to_int(v_val_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat(lean_object* v_hi_248_, lean_object* v_val_249_, lean_object* v_h_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = lean_nat_to_int(v_val_249_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat___boxed(lean_object* v_hi_252_, lean_object* v_val_253_, lean_object* v_h_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Std_Time_Internal_Bounded_LE_ofNat(v_hi_252_, v_val_253_, v_h_254_);
lean_dec(v_hi_252_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x3f(lean_object* v_hi_256_, lean_object* v_val_257_){
_start:
{
uint8_t v___x_258_; 
v___x_258_ = lean_nat_dec_le(v_val_257_, v_hi_256_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
lean_dec(v_val_257_);
v___x_259_ = lean_box(0);
return v___x_259_;
}
else
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_nat_to_int(v_val_257_);
v___x_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x3f___boxed(lean_object* v_hi_262_, lean_object* v_val_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Std_Time_Internal_Bounded_LE_ofNat_x3f(v_hi_262_, v_val_263_);
lean_dec(v_hi_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27___redArg(lean_object* v_val_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = lean_nat_to_int(v_val_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27(lean_object* v_lo_267_, lean_object* v_hi_268_, lean_object* v_val_269_, lean_object* v_h_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = lean_nat_to_int(v_val_269_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27___boxed(lean_object* v_lo_272_, lean_object* v_hi_273_, lean_object* v_val_274_, lean_object* v_h_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Std_Time_Internal_Bounded_LE_ofNat_x27(v_lo_272_, v_hi_273_, v_val_274_, v_h_275_);
lean_dec(v_hi_273_);
lean_dec(v_lo_272_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___redArg(lean_object* v_lo_277_, lean_object* v_hi_278_, lean_object* v_val_279_){
_start:
{
uint8_t v___x_280_; 
v___x_280_ = lean_int_dec_le(v_lo_277_, v_val_279_);
if (v___x_280_ == 0)
{
lean_inc(v_lo_277_);
return v_lo_277_;
}
else
{
uint8_t v___x_281_; 
v___x_281_ = lean_int_dec_le(v_val_279_, v_hi_278_);
if (v___x_281_ == 0)
{
lean_inc(v_hi_278_);
return v_hi_278_;
}
else
{
lean_inc(v_val_279_);
return v_val_279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___redArg___boxed(lean_object* v_lo_282_, lean_object* v_hi_283_, lean_object* v_val_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Std_Time_Internal_Bounded_LE_clip___redArg(v_lo_282_, v_hi_283_, v_val_284_);
lean_dec(v_val_284_);
lean_dec(v_hi_283_);
lean_dec(v_lo_282_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip(lean_object* v_lo_286_, lean_object* v_hi_287_, lean_object* v_val_288_, lean_object* v_h_289_){
_start:
{
uint8_t v___x_290_; 
v___x_290_ = lean_int_dec_le(v_lo_286_, v_val_288_);
if (v___x_290_ == 0)
{
lean_inc(v_lo_286_);
return v_lo_286_;
}
else
{
uint8_t v___x_291_; 
v___x_291_ = lean_int_dec_le(v_val_288_, v_hi_287_);
if (v___x_291_ == 0)
{
lean_inc(v_hi_287_);
return v_hi_287_;
}
else
{
lean_inc(v_val_288_);
return v_val_288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___boxed(lean_object* v_lo_292_, lean_object* v_hi_293_, lean_object* v_val_294_, lean_object* v_h_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Std_Time_Internal_Bounded_LE_clip(v_lo_292_, v_hi_293_, v_val_294_, v_h_295_);
lean_dec(v_val_294_);
lean_dec(v_hi_293_);
lean_dec(v_lo_292_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___redArg(lean_object* v_n_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Int_toNat(v_n_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___redArg___boxed(lean_object* v_n_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_Time_Internal_Bounded_LE_toNat___redArg(v_n_299_);
lean_dec(v_n_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat(lean_object* v_lo_301_, lean_object* v_hi_302_, lean_object* v_n_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Int_toNat(v_n_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___boxed(lean_object* v_lo_305_, lean_object* v_hi_306_, lean_object* v_n_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Std_Time_Internal_Bounded_LE_toNat(v_lo_305_, v_hi_306_, v_n_307_);
lean_dec(v_n_307_);
lean_dec(v_hi_306_);
lean_dec(v_lo_305_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg(lean_object* v_n_309_){
_start:
{
lean_object* v_intZero_310_; uint8_t v_isNeg_311_; lean_object* v_a_312_; 
v_intZero_310_ = lean_obj_once(&l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0, &l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0_once, _init_l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0);
v_isNeg_311_ = lean_int_dec_lt(v_n_309_, v_intZero_310_);
v_a_312_ = lean_nat_abs(v_n_309_);
return v_a_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg___boxed(lean_object* v_n_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg(v_n_313_);
lean_dec(v_n_313_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27(lean_object* v_lo_315_, lean_object* v_hi_316_, lean_object* v_n_317_, lean_object* v_h_318_){
_start:
{
lean_object* v_intZero_319_; uint8_t v_isNeg_320_; lean_object* v_a_321_; 
v_intZero_319_ = lean_obj_once(&l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0, &l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0_once, _init_l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0);
v_isNeg_320_ = lean_int_dec_lt(v_n_317_, v_intZero_319_);
v_a_321_ = lean_nat_abs(v_n_317_);
return v_a_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___boxed(lean_object* v_lo_322_, lean_object* v_hi_323_, lean_object* v_n_324_, lean_object* v_h_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Std_Time_Internal_Bounded_LE_toNat_x27(v_lo_322_, v_hi_323_, v_n_324_, v_h_325_);
lean_dec(v_n_324_);
lean_dec(v_hi_323_);
lean_dec(v_lo_322_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___redArg(lean_object* v_n_327_){
_start:
{
lean_inc(v_n_327_);
return v_n_327_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___redArg___boxed(lean_object* v_n_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Std_Time_Internal_Bounded_LE_toInt___redArg(v_n_328_);
lean_dec(v_n_328_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt(lean_object* v_lo_330_, lean_object* v_hi_331_, lean_object* v_n_332_){
_start:
{
lean_inc(v_n_332_);
return v_n_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___boxed(lean_object* v_lo_333_, lean_object* v_hi_334_, lean_object* v_n_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Std_Time_Internal_Bounded_LE_toInt(v_lo_333_, v_hi_334_, v_n_335_);
lean_dec(v_n_335_);
lean_dec(v_hi_334_);
lean_dec(v_lo_333_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___redArg(lean_object* v_n_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Int_toNat(v_n_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___redArg___boxed(lean_object* v_n_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Std_Time_Internal_Bounded_LE_toFin___redArg(v_n_339_);
lean_dec(v_n_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin(lean_object* v_lo_341_, lean_object* v_hi_342_, lean_object* v_n_343_, lean_object* v_h_u2080_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Int_toNat(v_n_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___boxed(lean_object* v_lo_346_, lean_object* v_hi_347_, lean_object* v_n_348_, lean_object* v_h_u2080_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_Time_Internal_Bounded_LE_toFin(v_lo_346_, v_hi_347_, v_n_348_, v_h_u2080_349_);
lean_dec(v_n_348_);
lean_dec(v_hi_347_);
lean_dec(v_lo_346_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin___redArg(lean_object* v_fin_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_nat_to_int(v_fin_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin(lean_object* v_hi_353_, lean_object* v_fin_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lean_nat_to_int(v_fin_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin___boxed(lean_object* v_hi_356_, lean_object* v_fin_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_Time_Internal_Bounded_LE_ofFin(v_hi_356_, v_fin_357_);
lean_dec(v_hi_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27___redArg(lean_object* v_lo_359_, lean_object* v_fin_360_){
_start:
{
uint8_t v___x_361_; 
v___x_361_ = lean_nat_dec_le(v_lo_359_, v_fin_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
lean_dec(v_fin_360_);
v___x_362_ = lean_nat_to_int(v_lo_359_);
return v___x_362_;
}
else
{
lean_object* v___x_363_; 
lean_dec(v_lo_359_);
v___x_363_ = lean_nat_to_int(v_fin_360_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27(lean_object* v_hi_364_, lean_object* v_lo_365_, lean_object* v_fin_366_, lean_object* v_h_367_){
_start:
{
uint8_t v___x_368_; 
v___x_368_ = lean_nat_dec_le(v_lo_365_, v_fin_366_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; 
lean_dec(v_fin_366_);
v___x_369_ = lean_nat_to_int(v_lo_365_);
return v___x_369_;
}
else
{
lean_object* v___x_370_; 
lean_dec(v_lo_365_);
v___x_370_ = lean_nat_to_int(v_fin_366_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27___boxed(lean_object* v_hi_371_, lean_object* v_lo_372_, lean_object* v_fin_373_, lean_object* v_h_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Std_Time_Internal_Bounded_LE_ofFin_x27(v_hi_371_, v_lo_372_, v_fin_373_, v_h_374_);
lean_dec(v_hi_371_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___redArg(lean_object* v_b_376_, lean_object* v_i_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = lean_int_emod(v_b_376_, v_i_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___redArg___boxed(lean_object* v_b_379_, lean_object* v_i_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_Time_Internal_Bounded_LE_byEmod___redArg(v_b_379_, v_i_380_);
lean_dec(v_i_380_);
lean_dec(v_b_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod(lean_object* v_b_382_, lean_object* v_i_383_, lean_object* v_hi_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lean_int_emod(v_b_382_, v_i_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___boxed(lean_object* v_b_386_, lean_object* v_i_387_, lean_object* v_hi_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Std_Time_Internal_Bounded_LE_byEmod(v_b_386_, v_i_387_, v_hi_388_);
lean_dec(v_i_387_);
lean_dec(v_b_386_);
return v_res_389_;
}
}
static lean_object* _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_390_; lean_object* v_intZero_391_; 
v_natZero_390_ = lean_unsigned_to_nat(0u);
v_intZero_391_ = lean_nat_to_int(v_natZero_390_);
return v_intZero_391_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg(lean_object* v_x_392_, lean_object* v_x_393_, lean_object* v_h__1_394_, lean_object* v_h__2_395_, lean_object* v_h__3_396_, lean_object* v_h__4_397_){
_start:
{
lean_object* v_intZero_398_; uint8_t v_isNeg_399_; 
v_intZero_398_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v_isNeg_399_ = lean_int_dec_lt(v_x_392_, v_intZero_398_);
if (v_isNeg_399_ == 0)
{
lean_object* v_a_400_; uint8_t v_isNeg_401_; 
lean_dec(v_h__4_397_);
lean_dec(v_h__3_396_);
v_a_400_ = lean_nat_abs(v_x_392_);
v_isNeg_401_ = lean_int_dec_lt(v_x_393_, v_intZero_398_);
if (v_isNeg_401_ == 0)
{
lean_object* v_a_402_; lean_object* v___x_403_; 
lean_dec(v_h__2_395_);
v_a_402_ = lean_nat_abs(v_x_393_);
v___x_403_ = lean_apply_2(v_h__1_394_, v_a_400_, v_a_402_);
return v___x_403_;
}
else
{
lean_object* v_abs_404_; lean_object* v_one_405_; lean_object* v_a_406_; lean_object* v___x_407_; 
lean_dec(v_h__1_394_);
v_abs_404_ = lean_nat_abs(v_x_393_);
v_one_405_ = lean_unsigned_to_nat(1u);
v_a_406_ = lean_nat_sub(v_abs_404_, v_one_405_);
lean_dec(v_abs_404_);
v___x_407_ = lean_apply_2(v_h__2_395_, v_a_400_, v_a_406_);
return v___x_407_;
}
}
else
{
lean_object* v_abs_408_; lean_object* v_one_409_; lean_object* v_a_410_; uint8_t v_isNeg_411_; 
lean_dec(v_h__2_395_);
lean_dec(v_h__1_394_);
v_abs_408_ = lean_nat_abs(v_x_392_);
v_one_409_ = lean_unsigned_to_nat(1u);
v_a_410_ = lean_nat_sub(v_abs_408_, v_one_409_);
lean_dec(v_abs_408_);
v_isNeg_411_ = lean_int_dec_lt(v_x_393_, v_intZero_398_);
if (v_isNeg_411_ == 0)
{
lean_object* v_a_412_; lean_object* v___x_413_; 
lean_dec(v_h__4_397_);
v_a_412_ = lean_nat_abs(v_x_393_);
v___x_413_ = lean_apply_2(v_h__3_396_, v_a_410_, v_a_412_);
return v___x_413_;
}
else
{
lean_object* v_abs_414_; lean_object* v_a_415_; lean_object* v___x_416_; 
lean_dec(v_h__3_396_);
v_abs_414_ = lean_nat_abs(v_x_393_);
v_a_415_ = lean_nat_sub(v_abs_414_, v_one_409_);
lean_dec(v_abs_414_);
v___x_416_ = lean_apply_2(v_h__4_397_, v_a_410_, v_a_415_);
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___boxed(lean_object* v_x_417_, lean_object* v_x_418_, lean_object* v_h__1_419_, lean_object* v_h__2_420_, lean_object* v_h__3_421_, lean_object* v_h__4_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg(v_x_417_, v_x_418_, v_h__1_419_, v_h__2_420_, v_h__3_421_, v_h__4_422_);
lean_dec(v_x_418_);
lean_dec(v_x_417_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter(lean_object* v_motive_424_, lean_object* v_x_425_, lean_object* v_x_426_, lean_object* v_h__1_427_, lean_object* v_h__2_428_, lean_object* v_h__3_429_, lean_object* v_h__4_430_){
_start:
{
lean_object* v_intZero_431_; uint8_t v_isNeg_432_; 
v_intZero_431_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v_isNeg_432_ = lean_int_dec_lt(v_x_425_, v_intZero_431_);
if (v_isNeg_432_ == 0)
{
lean_object* v_a_433_; uint8_t v_isNeg_434_; 
lean_dec(v_h__4_430_);
lean_dec(v_h__3_429_);
v_a_433_ = lean_nat_abs(v_x_425_);
v_isNeg_434_ = lean_int_dec_lt(v_x_426_, v_intZero_431_);
if (v_isNeg_434_ == 0)
{
lean_object* v_a_435_; lean_object* v___x_436_; 
lean_dec(v_h__2_428_);
v_a_435_ = lean_nat_abs(v_x_426_);
v___x_436_ = lean_apply_2(v_h__1_427_, v_a_433_, v_a_435_);
return v___x_436_;
}
else
{
lean_object* v_abs_437_; lean_object* v_one_438_; lean_object* v_a_439_; lean_object* v___x_440_; 
lean_dec(v_h__1_427_);
v_abs_437_ = lean_nat_abs(v_x_426_);
v_one_438_ = lean_unsigned_to_nat(1u);
v_a_439_ = lean_nat_sub(v_abs_437_, v_one_438_);
lean_dec(v_abs_437_);
v___x_440_ = lean_apply_2(v_h__2_428_, v_a_433_, v_a_439_);
return v___x_440_;
}
}
else
{
lean_object* v_abs_441_; lean_object* v_one_442_; lean_object* v_a_443_; uint8_t v_isNeg_444_; 
lean_dec(v_h__2_428_);
lean_dec(v_h__1_427_);
v_abs_441_ = lean_nat_abs(v_x_425_);
v_one_442_ = lean_unsigned_to_nat(1u);
v_a_443_ = lean_nat_sub(v_abs_441_, v_one_442_);
lean_dec(v_abs_441_);
v_isNeg_444_ = lean_int_dec_lt(v_x_426_, v_intZero_431_);
if (v_isNeg_444_ == 0)
{
lean_object* v_a_445_; lean_object* v___x_446_; 
lean_dec(v_h__4_430_);
v_a_445_ = lean_nat_abs(v_x_426_);
v___x_446_ = lean_apply_2(v_h__3_429_, v_a_443_, v_a_445_);
return v___x_446_;
}
else
{
lean_object* v_abs_447_; lean_object* v_a_448_; lean_object* v___x_449_; 
lean_dec(v_h__3_429_);
v_abs_447_ = lean_nat_abs(v_x_426_);
v_a_448_ = lean_nat_sub(v_abs_447_, v_one_442_);
lean_dec(v_abs_447_);
v___x_449_ = lean_apply_2(v_h__4_430_, v_a_443_, v_a_448_);
return v___x_449_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___boxed(lean_object* v_motive_450_, lean_object* v_x_451_, lean_object* v_x_452_, lean_object* v_h__1_453_, lean_object* v_h__2_454_, lean_object* v_h__3_455_, lean_object* v_h__4_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter(v_motive_450_, v_x_451_, v_x_452_, v_h__1_453_, v_h__2_454_, v_h__3_455_, v_h__4_456_);
lean_dec(v_x_452_);
lean_dec(v_x_451_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___redArg(lean_object* v_b_458_, lean_object* v_i_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = lean_int_mod(v_b_458_, v_i_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___redArg___boxed(lean_object* v_b_461_, lean_object* v_i_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Std_Time_Internal_Bounded_LE_byMod___redArg(v_b_461_, v_i_462_);
lean_dec(v_i_462_);
lean_dec(v_b_461_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod(lean_object* v_b_464_, lean_object* v_i_465_, lean_object* v_hi_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = lean_int_mod(v_b_464_, v_i_465_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___boxed(lean_object* v_b_468_, lean_object* v_i_469_, lean_object* v_hi_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Std_Time_Internal_Bounded_LE_byMod(v_b_468_, v_i_469_, v_hi_470_);
lean_dec(v_i_469_);
lean_dec(v_b_468_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___redArg(lean_object* v_n_472_, lean_object* v_bounded_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = lean_int_sub(v_bounded_473_, v_n_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___redArg___boxed(lean_object* v_n_475_, lean_object* v_bounded_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_Time_Internal_Bounded_LE_truncate___redArg(v_n_475_, v_bounded_476_);
lean_dec(v_bounded_476_);
lean_dec(v_n_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate(lean_object* v_n_478_, lean_object* v_m_479_, lean_object* v_bounded_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = lean_int_sub(v_bounded_480_, v_n_478_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___boxed(lean_object* v_n_482_, lean_object* v_m_483_, lean_object* v_bounded_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Std_Time_Internal_Bounded_LE_truncate(v_n_482_, v_m_483_, v_bounded_484_);
lean_dec(v_bounded_484_);
lean_dec(v_m_483_);
lean_dec(v_n_482_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___redArg(lean_object* v_bounded_486_){
_start:
{
lean_inc(v_bounded_486_);
return v_bounded_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___redArg___boxed(lean_object* v_bounded_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Std_Time_Internal_Bounded_LE_truncateTop___redArg(v_bounded_487_);
lean_dec(v_bounded_487_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop(lean_object* v_n_489_, lean_object* v_m_490_, lean_object* v_j_491_, lean_object* v_bounded_492_, lean_object* v_h_493_){
_start:
{
lean_inc(v_bounded_492_);
return v_bounded_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___boxed(lean_object* v_n_494_, lean_object* v_m_495_, lean_object* v_j_496_, lean_object* v_bounded_497_, lean_object* v_h_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Std_Time_Internal_Bounded_LE_truncateTop(v_n_494_, v_m_495_, v_j_496_, v_bounded_497_, v_h_498_);
lean_dec(v_bounded_497_);
lean_dec(v_j_496_);
lean_dec(v_m_495_);
lean_dec(v_n_494_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg(lean_object* v_bounded_500_){
_start:
{
lean_inc(v_bounded_500_);
return v_bounded_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg___boxed(lean_object* v_bounded_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg(v_bounded_501_);
lean_dec(v_bounded_501_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom(lean_object* v_n_503_, lean_object* v_m_504_, lean_object* v_j_505_, lean_object* v_bounded_506_, lean_object* v_h_507_){
_start:
{
lean_inc(v_bounded_506_);
return v_bounded_506_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___boxed(lean_object* v_n_508_, lean_object* v_m_509_, lean_object* v_j_510_, lean_object* v_bounded_511_, lean_object* v_h_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Std_Time_Internal_Bounded_LE_truncateBottom(v_n_508_, v_m_509_, v_j_510_, v_bounded_511_, v_h_512_);
lean_dec(v_bounded_511_);
lean_dec(v_j_510_);
lean_dec(v_m_509_);
lean_dec(v_n_508_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___redArg(lean_object* v_bounded_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = lean_int_neg(v_bounded_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___redArg___boxed(lean_object* v_bounded_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_Time_Internal_Bounded_LE_neg___redArg(v_bounded_516_);
lean_dec(v_bounded_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg(lean_object* v_n_518_, lean_object* v_m_519_, lean_object* v_bounded_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = lean_int_neg(v_bounded_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___boxed(lean_object* v_n_522_, lean_object* v_m_523_, lean_object* v_bounded_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_Time_Internal_Bounded_LE_neg(v_n_522_, v_m_523_, v_bounded_524_);
lean_dec(v_bounded_524_);
lean_dec(v_m_523_);
lean_dec(v_n_522_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___redArg(lean_object* v_bounded_526_, lean_object* v_num_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = lean_int_add(v_bounded_526_, v_num_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___redArg___boxed(lean_object* v_bounded_529_, lean_object* v_num_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Std_Time_Internal_Bounded_LE_add___redArg(v_bounded_529_, v_num_530_);
lean_dec(v_num_530_);
lean_dec(v_bounded_529_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add(lean_object* v_n_532_, lean_object* v_m_533_, lean_object* v_bounded_534_, lean_object* v_num_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = lean_int_add(v_bounded_534_, v_num_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___boxed(lean_object* v_n_537_, lean_object* v_m_538_, lean_object* v_bounded_539_, lean_object* v_num_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_Time_Internal_Bounded_LE_add(v_n_537_, v_m_538_, v_bounded_539_, v_num_540_);
lean_dec(v_num_540_);
lean_dec(v_bounded_539_);
lean_dec(v_m_538_);
lean_dec(v_n_537_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___redArg(lean_object* v_num_542_, lean_object* v_bounded_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = lean_int_add(v_bounded_543_, v_num_542_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___redArg___boxed(lean_object* v_num_545_, lean_object* v_bounded_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Std_Time_Internal_Bounded_LE_addProven___redArg(v_num_545_, v_bounded_546_);
lean_dec(v_bounded_546_);
lean_dec(v_num_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven(lean_object* v_n_548_, lean_object* v_m_549_, lean_object* v_num_550_, lean_object* v_bounded_551_, lean_object* v_h_u2080_552_, lean_object* v_h_u2081_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = lean_int_add(v_bounded_551_, v_num_550_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___boxed(lean_object* v_n_555_, lean_object* v_m_556_, lean_object* v_num_557_, lean_object* v_bounded_558_, lean_object* v_h_u2080_559_, lean_object* v_h_u2081_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_Time_Internal_Bounded_LE_addProven(v_n_555_, v_m_556_, v_num_557_, v_bounded_558_, v_h_u2080_559_, v_h_u2081_560_);
lean_dec(v_bounded_558_);
lean_dec(v_num_557_);
lean_dec(v_m_556_);
lean_dec(v_n_555_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___redArg(lean_object* v_bounded_562_, lean_object* v_num_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = lean_int_add(v_bounded_562_, v_num_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___redArg___boxed(lean_object* v_bounded_565_, lean_object* v_num_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_Time_Internal_Bounded_LE_addTop___redArg(v_bounded_565_, v_num_566_);
lean_dec(v_num_566_);
lean_dec(v_bounded_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop(lean_object* v_n_568_, lean_object* v_m_569_, lean_object* v_bounded_570_, lean_object* v_num_571_, lean_object* v_h_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = lean_int_add(v_bounded_570_, v_num_571_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___boxed(lean_object* v_n_574_, lean_object* v_m_575_, lean_object* v_bounded_576_, lean_object* v_num_577_, lean_object* v_h_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Std_Time_Internal_Bounded_LE_addTop(v_n_574_, v_m_575_, v_bounded_576_, v_num_577_, v_h_578_);
lean_dec(v_num_577_);
lean_dec(v_bounded_576_);
lean_dec(v_m_575_);
lean_dec(v_n_574_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___redArg(lean_object* v_bounded_580_, lean_object* v_num_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = lean_int_sub(v_bounded_580_, v_num_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___redArg___boxed(lean_object* v_bounded_583_, lean_object* v_num_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_Time_Internal_Bounded_LE_subBottom___redArg(v_bounded_583_, v_num_584_);
lean_dec(v_num_584_);
lean_dec(v_bounded_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom(lean_object* v_n_586_, lean_object* v_m_587_, lean_object* v_bounded_588_, lean_object* v_num_589_, lean_object* v_h_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = lean_int_sub(v_bounded_588_, v_num_589_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___boxed(lean_object* v_n_592_, lean_object* v_m_593_, lean_object* v_bounded_594_, lean_object* v_num_595_, lean_object* v_h_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Std_Time_Internal_Bounded_LE_subBottom(v_n_592_, v_m_593_, v_bounded_594_, v_num_595_, v_h_596_);
lean_dec(v_num_595_);
lean_dec(v_bounded_594_);
lean_dec(v_m_593_);
lean_dec(v_n_592_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___redArg(lean_object* v_bounded_598_, lean_object* v_bounded_u2082_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = lean_int_add(v_bounded_598_, v_bounded_u2082_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___redArg___boxed(lean_object* v_bounded_601_, lean_object* v_bounded_u2082_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Std_Time_Internal_Bounded_LE_addBounds___redArg(v_bounded_601_, v_bounded_u2082_602_);
lean_dec(v_bounded_u2082_602_);
lean_dec(v_bounded_601_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds(lean_object* v_n_604_, lean_object* v_m_605_, lean_object* v_i_606_, lean_object* v_j_607_, lean_object* v_bounded_608_, lean_object* v_bounded_u2082_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = lean_int_add(v_bounded_608_, v_bounded_u2082_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___boxed(lean_object* v_n_611_, lean_object* v_m_612_, lean_object* v_i_613_, lean_object* v_j_614_, lean_object* v_bounded_615_, lean_object* v_bounded_u2082_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Std_Time_Internal_Bounded_LE_addBounds(v_n_611_, v_m_612_, v_i_613_, v_j_614_, v_bounded_615_, v_bounded_u2082_616_);
lean_dec(v_bounded_u2082_616_);
lean_dec(v_bounded_615_);
lean_dec(v_j_614_);
lean_dec(v_i_613_);
lean_dec(v_m_612_);
lean_dec(v_n_611_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___redArg(lean_object* v_bounded_618_, lean_object* v_num_619_){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_int_neg(v_num_619_);
v___x_621_ = lean_int_add(v_bounded_618_, v___x_620_);
lean_dec(v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___redArg___boxed(lean_object* v_bounded_622_, lean_object* v_num_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Std_Time_Internal_Bounded_LE_sub___redArg(v_bounded_622_, v_num_623_);
lean_dec(v_num_623_);
lean_dec(v_bounded_622_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub(lean_object* v_n_625_, lean_object* v_m_626_, lean_object* v_bounded_627_, lean_object* v_num_628_){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_int_neg(v_num_628_);
v___x_630_ = lean_int_add(v_bounded_627_, v___x_629_);
lean_dec(v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___boxed(lean_object* v_n_631_, lean_object* v_m_632_, lean_object* v_bounded_633_, lean_object* v_num_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Std_Time_Internal_Bounded_LE_sub(v_n_631_, v_m_632_, v_bounded_633_, v_num_634_);
lean_dec(v_num_634_);
lean_dec(v_bounded_633_);
lean_dec(v_m_632_);
lean_dec(v_n_631_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___redArg(lean_object* v_bounded_636_, lean_object* v_bounded_u2082_637_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_int_neg(v_bounded_u2082_637_);
v___x_639_ = lean_int_add(v_bounded_636_, v___x_638_);
lean_dec(v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___redArg___boxed(lean_object* v_bounded_640_, lean_object* v_bounded_u2082_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Std_Time_Internal_Bounded_LE_subBounds___redArg(v_bounded_640_, v_bounded_u2082_641_);
lean_dec(v_bounded_u2082_641_);
lean_dec(v_bounded_640_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds(lean_object* v_n_643_, lean_object* v_m_644_, lean_object* v_i_645_, lean_object* v_j_646_, lean_object* v_bounded_647_, lean_object* v_bounded_u2082_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_int_neg(v_bounded_u2082_648_);
v___x_650_ = lean_int_add(v_bounded_647_, v___x_649_);
lean_dec(v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___boxed(lean_object* v_n_651_, lean_object* v_m_652_, lean_object* v_i_653_, lean_object* v_j_654_, lean_object* v_bounded_655_, lean_object* v_bounded_u2082_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Std_Time_Internal_Bounded_LE_subBounds(v_n_651_, v_m_652_, v_i_653_, v_j_654_, v_bounded_655_, v_bounded_u2082_656_);
lean_dec(v_bounded_u2082_656_);
lean_dec(v_bounded_655_);
lean_dec(v_j_654_);
lean_dec(v_i_653_);
lean_dec(v_m_652_);
lean_dec(v_n_651_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___redArg(lean_object* v_bounded_658_, lean_object* v_num_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = lean_int_emod(v_bounded_658_, v_num_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___redArg___boxed(lean_object* v_bounded_661_, lean_object* v_num_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Std_Time_Internal_Bounded_LE_emod___redArg(v_bounded_661_, v_num_662_);
lean_dec(v_num_662_);
lean_dec(v_bounded_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod(lean_object* v_n_664_, lean_object* v_num_665_, lean_object* v_bounded_666_, lean_object* v_num_667_, lean_object* v_hi_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = lean_int_emod(v_bounded_666_, v_num_667_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___boxed(lean_object* v_n_670_, lean_object* v_num_671_, lean_object* v_bounded_672_, lean_object* v_num_673_, lean_object* v_hi_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_Time_Internal_Bounded_LE_emod(v_n_670_, v_num_671_, v_bounded_672_, v_num_673_, v_hi_674_);
lean_dec(v_num_673_);
lean_dec(v_bounded_672_);
lean_dec(v_num_671_);
lean_dec(v_n_670_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___redArg(lean_object* v_bounded_676_, lean_object* v_num_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = lean_int_mod(v_bounded_676_, v_num_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___redArg___boxed(lean_object* v_bounded_679_, lean_object* v_num_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Std_Time_Internal_Bounded_LE_mod___redArg(v_bounded_679_, v_num_680_);
lean_dec(v_num_680_);
lean_dec(v_bounded_679_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod(lean_object* v_n_682_, lean_object* v_num_683_, lean_object* v_bounded_684_, lean_object* v_num_685_, lean_object* v_hi_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = lean_int_mod(v_bounded_684_, v_num_685_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___boxed(lean_object* v_n_688_, lean_object* v_num_689_, lean_object* v_bounded_690_, lean_object* v_num_691_, lean_object* v_hi_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Std_Time_Internal_Bounded_LE_mod(v_n_688_, v_num_689_, v_bounded_690_, v_num_691_, v_hi_692_);
lean_dec(v_num_691_);
lean_dec(v_bounded_690_);
lean_dec(v_num_689_);
lean_dec(v_n_688_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___redArg(lean_object* v_bounded_694_, lean_object* v_num_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = lean_int_mul(v_bounded_694_, v_num_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___redArg___boxed(lean_object* v_bounded_697_, lean_object* v_num_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Std_Time_Internal_Bounded_LE_mul__pos___redArg(v_bounded_697_, v_num_698_);
lean_dec(v_num_698_);
lean_dec(v_bounded_697_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos(lean_object* v_n_700_, lean_object* v_m_701_, lean_object* v_bounded_702_, lean_object* v_num_703_, lean_object* v_h_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = lean_int_mul(v_bounded_702_, v_num_703_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___boxed(lean_object* v_n_706_, lean_object* v_m_707_, lean_object* v_bounded_708_, lean_object* v_num_709_, lean_object* v_h_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Std_Time_Internal_Bounded_LE_mul__pos(v_n_706_, v_m_707_, v_bounded_708_, v_num_709_, v_h_710_);
lean_dec(v_num_709_);
lean_dec(v_bounded_708_);
lean_dec(v_m_707_);
lean_dec(v_n_706_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___redArg(lean_object* v_bounded_712_, lean_object* v_num_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = lean_int_mul(v_bounded_712_, v_num_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___redArg___boxed(lean_object* v_bounded_715_, lean_object* v_num_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Std_Time_Internal_Bounded_LE_mul__neg___redArg(v_bounded_715_, v_num_716_);
lean_dec(v_num_716_);
lean_dec(v_bounded_715_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg(lean_object* v_n_718_, lean_object* v_m_719_, lean_object* v_bounded_720_, lean_object* v_num_721_, lean_object* v_h_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = lean_int_mul(v_bounded_720_, v_num_721_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___boxed(lean_object* v_n_724_, lean_object* v_m_725_, lean_object* v_bounded_726_, lean_object* v_num_727_, lean_object* v_h_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Std_Time_Internal_Bounded_LE_mul__neg(v_n_724_, v_m_725_, v_bounded_726_, v_num_727_, v_h_728_);
lean_dec(v_num_727_);
lean_dec(v_bounded_726_);
lean_dec(v_m_725_);
lean_dec(v_n_724_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___redArg(lean_object* v_bounded_730_, lean_object* v_num_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = lean_int_ediv(v_bounded_730_, v_num_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___redArg___boxed(lean_object* v_bounded_733_, lean_object* v_num_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_Time_Internal_Bounded_LE_ediv___redArg(v_bounded_733_, v_num_734_);
lean_dec(v_num_734_);
lean_dec(v_bounded_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv(lean_object* v_n_736_, lean_object* v_m_737_, lean_object* v_bounded_738_, lean_object* v_num_739_, lean_object* v_h_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = lean_int_ediv(v_bounded_738_, v_num_739_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___boxed(lean_object* v_n_742_, lean_object* v_m_743_, lean_object* v_bounded_744_, lean_object* v_num_745_, lean_object* v_h_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Std_Time_Internal_Bounded_LE_ediv(v_n_742_, v_m_743_, v_bounded_744_, v_num_745_, v_h_746_);
lean_dec(v_num_745_);
lean_dec(v_bounded_744_);
lean_dec(v_m_743_);
lean_dec(v_n_742_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_eq(lean_object* v_n_748_){
_start:
{
lean_inc(v_n_748_);
return v_n_748_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_eq___boxed(lean_object* v_n_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Std_Time_Internal_Bounded_LE_eq(v_n_749_);
lean_dec(v_n_749_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___redArg(lean_object* v_bounded_751_){
_start:
{
lean_inc(v_bounded_751_);
return v_bounded_751_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___redArg___boxed(lean_object* v_bounded_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Std_Time_Internal_Bounded_LE_expand___redArg(v_bounded_752_);
lean_dec(v_bounded_752_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand(lean_object* v_lo_754_, lean_object* v_hi_755_, lean_object* v_nhi_756_, lean_object* v_nlo_757_, lean_object* v_bounded_758_, lean_object* v_h_759_, lean_object* v_h_u2081_760_){
_start:
{
lean_inc(v_bounded_758_);
return v_bounded_758_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___boxed(lean_object* v_lo_761_, lean_object* v_hi_762_, lean_object* v_nhi_763_, lean_object* v_nlo_764_, lean_object* v_bounded_765_, lean_object* v_h_766_, lean_object* v_h_u2081_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_Time_Internal_Bounded_LE_expand(v_lo_761_, v_hi_762_, v_nhi_763_, v_nlo_764_, v_bounded_765_, v_h_766_, v_h_u2081_767_);
lean_dec(v_bounded_765_);
lean_dec(v_nlo_764_);
lean_dec(v_nhi_763_);
lean_dec(v_hi_762_);
lean_dec(v_lo_761_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___redArg(lean_object* v_bounded_769_){
_start:
{
lean_inc(v_bounded_769_);
return v_bounded_769_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___redArg___boxed(lean_object* v_bounded_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Std_Time_Internal_Bounded_LE_expandTop___redArg(v_bounded_770_);
lean_dec(v_bounded_770_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop(lean_object* v_lo_772_, lean_object* v_hi_773_, lean_object* v_nhi_774_, lean_object* v_bounded_775_, lean_object* v_h_776_){
_start:
{
lean_inc(v_bounded_775_);
return v_bounded_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___boxed(lean_object* v_lo_777_, lean_object* v_hi_778_, lean_object* v_nhi_779_, lean_object* v_bounded_780_, lean_object* v_h_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Std_Time_Internal_Bounded_LE_expandTop(v_lo_777_, v_hi_778_, v_nhi_779_, v_bounded_780_, v_h_781_);
lean_dec(v_bounded_780_);
lean_dec(v_nhi_779_);
lean_dec(v_hi_778_);
lean_dec(v_lo_777_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___redArg(lean_object* v_bounded_783_){
_start:
{
lean_inc(v_bounded_783_);
return v_bounded_783_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___redArg___boxed(lean_object* v_bounded_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Std_Time_Internal_Bounded_LE_expandBottom___redArg(v_bounded_784_);
lean_dec(v_bounded_784_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom(lean_object* v_lo_786_, lean_object* v_hi_787_, lean_object* v_nlo_788_, lean_object* v_bounded_789_, lean_object* v_h_790_){
_start:
{
lean_inc(v_bounded_789_);
return v_bounded_789_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___boxed(lean_object* v_lo_791_, lean_object* v_hi_792_, lean_object* v_nlo_793_, lean_object* v_bounded_794_, lean_object* v_h_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Std_Time_Internal_Bounded_LE_expandBottom(v_lo_791_, v_hi_792_, v_nlo_793_, v_bounded_794_, v_h_795_);
lean_dec(v_bounded_794_);
lean_dec(v_nlo_793_);
lean_dec(v_hi_792_);
lean_dec(v_lo_791_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___redArg(lean_object* v_bounded_797_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v___x_799_ = lean_int_add(v_bounded_797_, v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___redArg___boxed(lean_object* v_bounded_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Std_Time_Internal_Bounded_LE_succ___redArg(v_bounded_800_);
lean_dec(v_bounded_800_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ(lean_object* v_lo_802_, lean_object* v_hi_803_, lean_object* v_bounded_804_, lean_object* v_h_805_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v___x_807_ = lean_int_add(v_bounded_804_, v___x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___boxed(lean_object* v_lo_808_, lean_object* v_hi_809_, lean_object* v_bounded_810_, lean_object* v_h_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Std_Time_Internal_Bounded_LE_succ(v_lo_808_, v_hi_809_, v_bounded_810_, v_h_811_);
lean_dec(v_bounded_810_);
lean_dec(v_hi_809_);
lean_dec(v_lo_808_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___redArg(lean_object* v_bo_813_){
_start:
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v___x_815_ = lean_int_dec_le(v___x_814_, v_bo_813_);
if (v___x_815_ == 0)
{
lean_object* v_r_816_; 
v_r_816_ = lean_int_neg(v_bo_813_);
return v_r_816_;
}
else
{
lean_inc(v_bo_813_);
return v_bo_813_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___redArg___boxed(lean_object* v_bo_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Std_Time_Internal_Bounded_LE_abs___redArg(v_bo_817_);
lean_dec(v_bo_817_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs(lean_object* v_i_819_, lean_object* v_bo_820_){
_start:
{
lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_821_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v___x_822_ = lean_int_dec_le(v___x_821_, v_bo_820_);
if (v___x_822_ == 0)
{
lean_object* v_r_823_; 
v_r_823_ = lean_int_neg(v_bo_820_);
return v_r_823_;
}
else
{
lean_inc(v_bo_820_);
return v_bo_820_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___boxed(lean_object* v_i_824_, lean_object* v_bo_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Std_Time_Internal_Bounded_LE_abs(v_i_824_, v_bo_825_);
lean_dec(v_bo_825_);
lean_dec(v_i_824_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___redArg(lean_object* v_bounded_827_, lean_object* v_val_828_){
_start:
{
uint8_t v___x_829_; 
v___x_829_ = lean_int_dec_le(v_bounded_827_, v_val_828_);
if (v___x_829_ == 0)
{
lean_inc(v_bounded_827_);
return v_bounded_827_;
}
else
{
lean_inc(v_val_828_);
return v_val_828_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___redArg___boxed(lean_object* v_bounded_830_, lean_object* v_val_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Std_Time_Internal_Bounded_LE_max___redArg(v_bounded_830_, v_val_831_);
lean_dec(v_val_831_);
lean_dec(v_bounded_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max(lean_object* v_n_833_, lean_object* v_m_834_, lean_object* v_bounded_835_, lean_object* v_val_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Std_Time_Internal_Bounded_LE_max___redArg(v_bounded_835_, v_val_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___boxed(lean_object* v_n_838_, lean_object* v_m_839_, lean_object* v_bounded_840_, lean_object* v_val_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_Time_Internal_Bounded_LE_max(v_n_838_, v_m_839_, v_bounded_840_, v_val_841_);
lean_dec(v_val_841_);
lean_dec(v_bounded_840_);
lean_dec(v_m_839_);
lean_dec(v_n_838_);
return v_res_842_;
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
