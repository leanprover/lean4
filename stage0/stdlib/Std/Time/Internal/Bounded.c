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
lean_object* v___x_134_; uint8_t v___x_135_; 
lean_inc_ref(v_inst_132_);
lean_inc(v_val_133_);
v___x_134_ = lean_apply_2(v_inst_132_, v_lo_130_, v_val_133_);
v___x_135_ = lean_unbox(v___x_134_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; 
lean_dec(v_val_133_);
lean_dec_ref(v_inst_132_);
lean_dec(v_hi_131_);
v___x_136_ = lean_box(0);
return v___x_136_;
}
else
{
lean_object* v___x_137_; uint8_t v___x_138_; 
lean_inc(v_val_133_);
v___x_137_ = lean_apply_2(v_inst_132_, v_val_133_, v_hi_131_);
v___x_138_ = lean_unbox(v___x_137_);
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
lean_object* v___x_146_; uint8_t v___x_147_; 
lean_inc_ref(v_inst_144_);
lean_inc(v_val_145_);
v___x_146_ = lean_apply_2(v_inst_144_, v_lo_142_, v_val_145_);
v___x_147_ = lean_unbox(v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; 
lean_dec(v_val_145_);
lean_dec_ref(v_inst_144_);
lean_dec(v_hi_143_);
v___x_148_ = lean_box(0);
return v___x_148_;
}
else
{
lean_object* v___x_149_; uint8_t v___x_150_; 
lean_inc(v_val_145_);
v___x_149_ = lean_apply_2(v_inst_144_, v_val_145_, v_hi_143_);
v___x_150_ = lean_unbox(v___x_149_);
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
uint8_t v___y_238_; uint8_t v___x_241_; 
v___x_241_ = lean_int_dec_le(v_lo_234_, v_val_236_);
if (v___x_241_ == 0)
{
v___y_238_ = v___x_241_;
goto v___jp_237_;
}
else
{
uint8_t v___x_242_; 
v___x_242_ = lean_int_dec_le(v_val_236_, v_hi_235_);
v___y_238_ = v___x_242_;
goto v___jp_237_;
}
v___jp_237_:
{
if (v___y_238_ == 0)
{
lean_object* v___x_239_; 
lean_dec(v_val_236_);
v___x_239_ = lean_box(0);
return v___x_239_;
}
else
{
lean_object* v___x_240_; 
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v_val_236_);
return v___x_240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofInt___boxed(lean_object* v_lo_243_, lean_object* v_hi_244_, lean_object* v_val_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Std_Time_Internal_Bounded_LE_ofInt(v_lo_243_, v_hi_244_, v_val_245_);
lean_dec(v_hi_244_);
lean_dec(v_lo_243_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat___redArg(lean_object* v_val_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = lean_nat_to_int(v_val_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat(lean_object* v_hi_249_, lean_object* v_val_250_, lean_object* v_h_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lean_nat_to_int(v_val_250_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat___boxed(lean_object* v_hi_253_, lean_object* v_val_254_, lean_object* v_h_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Std_Time_Internal_Bounded_LE_ofNat(v_hi_253_, v_val_254_, v_h_255_);
lean_dec(v_hi_253_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x3f(lean_object* v_hi_257_, lean_object* v_val_258_){
_start:
{
uint8_t v___x_259_; 
v___x_259_ = lean_nat_dec_le(v_val_258_, v_hi_257_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
lean_dec(v_val_258_);
v___x_260_ = lean_box(0);
return v___x_260_;
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_nat_to_int(v_val_258_);
v___x_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x3f___boxed(lean_object* v_hi_263_, lean_object* v_val_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_Time_Internal_Bounded_LE_ofNat_x3f(v_hi_263_, v_val_264_);
lean_dec(v_hi_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27___redArg(lean_object* v_val_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lean_nat_to_int(v_val_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27(lean_object* v_lo_268_, lean_object* v_hi_269_, lean_object* v_val_270_, lean_object* v_h_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lean_nat_to_int(v_val_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27___boxed(lean_object* v_lo_273_, lean_object* v_hi_274_, lean_object* v_val_275_, lean_object* v_h_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Std_Time_Internal_Bounded_LE_ofNat_x27(v_lo_273_, v_hi_274_, v_val_275_, v_h_276_);
lean_dec(v_hi_274_);
lean_dec(v_lo_273_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___redArg(lean_object* v_lo_278_, lean_object* v_hi_279_, lean_object* v_val_280_){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = lean_int_dec_le(v_lo_278_, v_val_280_);
if (v___x_281_ == 0)
{
lean_inc(v_lo_278_);
return v_lo_278_;
}
else
{
uint8_t v___x_282_; 
v___x_282_ = lean_int_dec_le(v_val_280_, v_hi_279_);
if (v___x_282_ == 0)
{
lean_inc(v_hi_279_);
return v_hi_279_;
}
else
{
lean_inc(v_val_280_);
return v_val_280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___redArg___boxed(lean_object* v_lo_283_, lean_object* v_hi_284_, lean_object* v_val_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Std_Time_Internal_Bounded_LE_clip___redArg(v_lo_283_, v_hi_284_, v_val_285_);
lean_dec(v_val_285_);
lean_dec(v_hi_284_);
lean_dec(v_lo_283_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip(lean_object* v_lo_287_, lean_object* v_hi_288_, lean_object* v_val_289_, lean_object* v_h_290_){
_start:
{
uint8_t v___x_291_; 
v___x_291_ = lean_int_dec_le(v_lo_287_, v_val_289_);
if (v___x_291_ == 0)
{
lean_inc(v_lo_287_);
return v_lo_287_;
}
else
{
uint8_t v___x_292_; 
v___x_292_ = lean_int_dec_le(v_val_289_, v_hi_288_);
if (v___x_292_ == 0)
{
lean_inc(v_hi_288_);
return v_hi_288_;
}
else
{
lean_inc(v_val_289_);
return v_val_289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___boxed(lean_object* v_lo_293_, lean_object* v_hi_294_, lean_object* v_val_295_, lean_object* v_h_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Std_Time_Internal_Bounded_LE_clip(v_lo_293_, v_hi_294_, v_val_295_, v_h_296_);
lean_dec(v_val_295_);
lean_dec(v_hi_294_);
lean_dec(v_lo_293_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___redArg(lean_object* v_n_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Int_toNat(v_n_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___redArg___boxed(lean_object* v_n_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Std_Time_Internal_Bounded_LE_toNat___redArg(v_n_300_);
lean_dec(v_n_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat(lean_object* v_lo_302_, lean_object* v_hi_303_, lean_object* v_n_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Int_toNat(v_n_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___boxed(lean_object* v_lo_306_, lean_object* v_hi_307_, lean_object* v_n_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_Time_Internal_Bounded_LE_toNat(v_lo_306_, v_hi_307_, v_n_308_);
lean_dec(v_n_308_);
lean_dec(v_hi_307_);
lean_dec(v_lo_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg(lean_object* v_n_310_){
_start:
{
lean_object* v_intZero_311_; uint8_t v_isNeg_312_; lean_object* v_a_313_; 
v_intZero_311_ = lean_obj_once(&l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0, &l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0_once, _init_l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0);
v_isNeg_312_ = lean_int_dec_lt(v_n_310_, v_intZero_311_);
v_a_313_ = lean_nat_abs(v_n_310_);
return v_a_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg___boxed(lean_object* v_n_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg(v_n_314_);
lean_dec(v_n_314_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27(lean_object* v_lo_316_, lean_object* v_hi_317_, lean_object* v_n_318_, lean_object* v_h_319_){
_start:
{
lean_object* v_intZero_320_; uint8_t v_isNeg_321_; lean_object* v_a_322_; 
v_intZero_320_ = lean_obj_once(&l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0, &l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0_once, _init_l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0);
v_isNeg_321_ = lean_int_dec_lt(v_n_318_, v_intZero_320_);
v_a_322_ = lean_nat_abs(v_n_318_);
return v_a_322_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___boxed(lean_object* v_lo_323_, lean_object* v_hi_324_, lean_object* v_n_325_, lean_object* v_h_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Std_Time_Internal_Bounded_LE_toNat_x27(v_lo_323_, v_hi_324_, v_n_325_, v_h_326_);
lean_dec(v_n_325_);
lean_dec(v_hi_324_);
lean_dec(v_lo_323_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___redArg(lean_object* v_n_328_){
_start:
{
lean_inc(v_n_328_);
return v_n_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___redArg___boxed(lean_object* v_n_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Std_Time_Internal_Bounded_LE_toInt___redArg(v_n_329_);
lean_dec(v_n_329_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt(lean_object* v_lo_331_, lean_object* v_hi_332_, lean_object* v_n_333_){
_start:
{
lean_inc(v_n_333_);
return v_n_333_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___boxed(lean_object* v_lo_334_, lean_object* v_hi_335_, lean_object* v_n_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Std_Time_Internal_Bounded_LE_toInt(v_lo_334_, v_hi_335_, v_n_336_);
lean_dec(v_n_336_);
lean_dec(v_hi_335_);
lean_dec(v_lo_334_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___redArg(lean_object* v_n_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Int_toNat(v_n_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___redArg___boxed(lean_object* v_n_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_Time_Internal_Bounded_LE_toFin___redArg(v_n_340_);
lean_dec(v_n_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin(lean_object* v_lo_342_, lean_object* v_hi_343_, lean_object* v_n_344_, lean_object* v_h_u2080_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Int_toNat(v_n_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___boxed(lean_object* v_lo_347_, lean_object* v_hi_348_, lean_object* v_n_349_, lean_object* v_h_u2080_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Std_Time_Internal_Bounded_LE_toFin(v_lo_347_, v_hi_348_, v_n_349_, v_h_u2080_350_);
lean_dec(v_n_349_);
lean_dec(v_hi_348_);
lean_dec(v_lo_347_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin___redArg(lean_object* v_fin_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = lean_nat_to_int(v_fin_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin(lean_object* v_hi_354_, lean_object* v_fin_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = lean_nat_to_int(v_fin_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin___boxed(lean_object* v_hi_357_, lean_object* v_fin_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Std_Time_Internal_Bounded_LE_ofFin(v_hi_357_, v_fin_358_);
lean_dec(v_hi_357_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27___redArg(lean_object* v_lo_360_, lean_object* v_fin_361_){
_start:
{
uint8_t v___x_362_; 
v___x_362_ = lean_nat_dec_le(v_lo_360_, v_fin_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
lean_dec(v_fin_361_);
v___x_363_ = lean_nat_to_int(v_lo_360_);
return v___x_363_;
}
else
{
lean_object* v___x_364_; 
lean_dec(v_lo_360_);
v___x_364_ = lean_nat_to_int(v_fin_361_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27(lean_object* v_hi_365_, lean_object* v_lo_366_, lean_object* v_fin_367_, lean_object* v_h_368_){
_start:
{
uint8_t v___x_369_; 
v___x_369_ = lean_nat_dec_le(v_lo_366_, v_fin_367_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
lean_dec(v_fin_367_);
v___x_370_ = lean_nat_to_int(v_lo_366_);
return v___x_370_;
}
else
{
lean_object* v___x_371_; 
lean_dec(v_lo_366_);
v___x_371_ = lean_nat_to_int(v_fin_367_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27___boxed(lean_object* v_hi_372_, lean_object* v_lo_373_, lean_object* v_fin_374_, lean_object* v_h_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Std_Time_Internal_Bounded_LE_ofFin_x27(v_hi_372_, v_lo_373_, v_fin_374_, v_h_375_);
lean_dec(v_hi_372_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___redArg(lean_object* v_b_377_, lean_object* v_i_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = lean_int_emod(v_b_377_, v_i_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___redArg___boxed(lean_object* v_b_380_, lean_object* v_i_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Std_Time_Internal_Bounded_LE_byEmod___redArg(v_b_380_, v_i_381_);
lean_dec(v_i_381_);
lean_dec(v_b_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod(lean_object* v_b_383_, lean_object* v_i_384_, lean_object* v_hi_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = lean_int_emod(v_b_383_, v_i_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___boxed(lean_object* v_b_387_, lean_object* v_i_388_, lean_object* v_hi_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_Time_Internal_Bounded_LE_byEmod(v_b_387_, v_i_388_, v_hi_389_);
lean_dec(v_i_388_);
lean_dec(v_b_387_);
return v_res_390_;
}
}
static lean_object* _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_391_; lean_object* v_intZero_392_; 
v_natZero_391_ = lean_unsigned_to_nat(0u);
v_intZero_392_ = lean_nat_to_int(v_natZero_391_);
return v_intZero_392_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg(lean_object* v_x_393_, lean_object* v_x_394_, lean_object* v_h__1_395_, lean_object* v_h__2_396_, lean_object* v_h__3_397_, lean_object* v_h__4_398_){
_start:
{
lean_object* v_intZero_399_; uint8_t v_isNeg_400_; 
v_intZero_399_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v_isNeg_400_ = lean_int_dec_lt(v_x_393_, v_intZero_399_);
if (v_isNeg_400_ == 0)
{
lean_object* v_a_401_; uint8_t v_isNeg_402_; 
lean_dec(v_h__4_398_);
lean_dec(v_h__3_397_);
v_a_401_ = lean_nat_abs(v_x_393_);
v_isNeg_402_ = lean_int_dec_lt(v_x_394_, v_intZero_399_);
if (v_isNeg_402_ == 0)
{
lean_object* v_a_403_; lean_object* v___x_404_; 
lean_dec(v_h__2_396_);
v_a_403_ = lean_nat_abs(v_x_394_);
v___x_404_ = lean_apply_2(v_h__1_395_, v_a_401_, v_a_403_);
return v___x_404_;
}
else
{
lean_object* v_abs_405_; lean_object* v_one_406_; lean_object* v_a_407_; lean_object* v___x_408_; 
lean_dec(v_h__1_395_);
v_abs_405_ = lean_nat_abs(v_x_394_);
v_one_406_ = lean_unsigned_to_nat(1u);
v_a_407_ = lean_nat_sub(v_abs_405_, v_one_406_);
lean_dec(v_abs_405_);
v___x_408_ = lean_apply_2(v_h__2_396_, v_a_401_, v_a_407_);
return v___x_408_;
}
}
else
{
lean_object* v_abs_409_; lean_object* v_one_410_; lean_object* v_a_411_; uint8_t v_isNeg_412_; 
lean_dec(v_h__2_396_);
lean_dec(v_h__1_395_);
v_abs_409_ = lean_nat_abs(v_x_393_);
v_one_410_ = lean_unsigned_to_nat(1u);
v_a_411_ = lean_nat_sub(v_abs_409_, v_one_410_);
lean_dec(v_abs_409_);
v_isNeg_412_ = lean_int_dec_lt(v_x_394_, v_intZero_399_);
if (v_isNeg_412_ == 0)
{
lean_object* v_a_413_; lean_object* v___x_414_; 
lean_dec(v_h__4_398_);
v_a_413_ = lean_nat_abs(v_x_394_);
v___x_414_ = lean_apply_2(v_h__3_397_, v_a_411_, v_a_413_);
return v___x_414_;
}
else
{
lean_object* v_abs_415_; lean_object* v_a_416_; lean_object* v___x_417_; 
lean_dec(v_h__3_397_);
v_abs_415_ = lean_nat_abs(v_x_394_);
v_a_416_ = lean_nat_sub(v_abs_415_, v_one_410_);
lean_dec(v_abs_415_);
v___x_417_ = lean_apply_2(v_h__4_398_, v_a_411_, v_a_416_);
return v___x_417_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___boxed(lean_object* v_x_418_, lean_object* v_x_419_, lean_object* v_h__1_420_, lean_object* v_h__2_421_, lean_object* v_h__3_422_, lean_object* v_h__4_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg(v_x_418_, v_x_419_, v_h__1_420_, v_h__2_421_, v_h__3_422_, v_h__4_423_);
lean_dec(v_x_419_);
lean_dec(v_x_418_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter(lean_object* v_motive_425_, lean_object* v_x_426_, lean_object* v_x_427_, lean_object* v_h__1_428_, lean_object* v_h__2_429_, lean_object* v_h__3_430_, lean_object* v_h__4_431_){
_start:
{
lean_object* v_intZero_432_; uint8_t v_isNeg_433_; 
v_intZero_432_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v_isNeg_433_ = lean_int_dec_lt(v_x_426_, v_intZero_432_);
if (v_isNeg_433_ == 0)
{
lean_object* v_a_434_; uint8_t v_isNeg_435_; 
lean_dec(v_h__4_431_);
lean_dec(v_h__3_430_);
v_a_434_ = lean_nat_abs(v_x_426_);
v_isNeg_435_ = lean_int_dec_lt(v_x_427_, v_intZero_432_);
if (v_isNeg_435_ == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; 
lean_dec(v_h__2_429_);
v_a_436_ = lean_nat_abs(v_x_427_);
v___x_437_ = lean_apply_2(v_h__1_428_, v_a_434_, v_a_436_);
return v___x_437_;
}
else
{
lean_object* v_abs_438_; lean_object* v_one_439_; lean_object* v_a_440_; lean_object* v___x_441_; 
lean_dec(v_h__1_428_);
v_abs_438_ = lean_nat_abs(v_x_427_);
v_one_439_ = lean_unsigned_to_nat(1u);
v_a_440_ = lean_nat_sub(v_abs_438_, v_one_439_);
lean_dec(v_abs_438_);
v___x_441_ = lean_apply_2(v_h__2_429_, v_a_434_, v_a_440_);
return v___x_441_;
}
}
else
{
lean_object* v_abs_442_; lean_object* v_one_443_; lean_object* v_a_444_; uint8_t v_isNeg_445_; 
lean_dec(v_h__2_429_);
lean_dec(v_h__1_428_);
v_abs_442_ = lean_nat_abs(v_x_426_);
v_one_443_ = lean_unsigned_to_nat(1u);
v_a_444_ = lean_nat_sub(v_abs_442_, v_one_443_);
lean_dec(v_abs_442_);
v_isNeg_445_ = lean_int_dec_lt(v_x_427_, v_intZero_432_);
if (v_isNeg_445_ == 0)
{
lean_object* v_a_446_; lean_object* v___x_447_; 
lean_dec(v_h__4_431_);
v_a_446_ = lean_nat_abs(v_x_427_);
v___x_447_ = lean_apply_2(v_h__3_430_, v_a_444_, v_a_446_);
return v___x_447_;
}
else
{
lean_object* v_abs_448_; lean_object* v_a_449_; lean_object* v___x_450_; 
lean_dec(v_h__3_430_);
v_abs_448_ = lean_nat_abs(v_x_427_);
v_a_449_ = lean_nat_sub(v_abs_448_, v_one_443_);
lean_dec(v_abs_448_);
v___x_450_ = lean_apply_2(v_h__4_431_, v_a_444_, v_a_449_);
return v___x_450_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___boxed(lean_object* v_motive_451_, lean_object* v_x_452_, lean_object* v_x_453_, lean_object* v_h__1_454_, lean_object* v_h__2_455_, lean_object* v_h__3_456_, lean_object* v_h__4_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter(v_motive_451_, v_x_452_, v_x_453_, v_h__1_454_, v_h__2_455_, v_h__3_456_, v_h__4_457_);
lean_dec(v_x_453_);
lean_dec(v_x_452_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___redArg(lean_object* v_b_459_, lean_object* v_i_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = lean_int_mod(v_b_459_, v_i_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___redArg___boxed(lean_object* v_b_462_, lean_object* v_i_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Std_Time_Internal_Bounded_LE_byMod___redArg(v_b_462_, v_i_463_);
lean_dec(v_i_463_);
lean_dec(v_b_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod(lean_object* v_b_465_, lean_object* v_i_466_, lean_object* v_hi_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = lean_int_mod(v_b_465_, v_i_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___boxed(lean_object* v_b_469_, lean_object* v_i_470_, lean_object* v_hi_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Std_Time_Internal_Bounded_LE_byMod(v_b_469_, v_i_470_, v_hi_471_);
lean_dec(v_i_470_);
lean_dec(v_b_469_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___redArg(lean_object* v_n_473_, lean_object* v_bounded_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = lean_int_sub(v_bounded_474_, v_n_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___redArg___boxed(lean_object* v_n_476_, lean_object* v_bounded_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Std_Time_Internal_Bounded_LE_truncate___redArg(v_n_476_, v_bounded_477_);
lean_dec(v_bounded_477_);
lean_dec(v_n_476_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate(lean_object* v_n_479_, lean_object* v_m_480_, lean_object* v_bounded_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = lean_int_sub(v_bounded_481_, v_n_479_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___boxed(lean_object* v_n_483_, lean_object* v_m_484_, lean_object* v_bounded_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_Time_Internal_Bounded_LE_truncate(v_n_483_, v_m_484_, v_bounded_485_);
lean_dec(v_bounded_485_);
lean_dec(v_m_484_);
lean_dec(v_n_483_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___redArg(lean_object* v_bounded_487_){
_start:
{
lean_inc(v_bounded_487_);
return v_bounded_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___redArg___boxed(lean_object* v_bounded_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Std_Time_Internal_Bounded_LE_truncateTop___redArg(v_bounded_488_);
lean_dec(v_bounded_488_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop(lean_object* v_n_490_, lean_object* v_m_491_, lean_object* v_j_492_, lean_object* v_bounded_493_, lean_object* v_h_494_){
_start:
{
lean_inc(v_bounded_493_);
return v_bounded_493_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___boxed(lean_object* v_n_495_, lean_object* v_m_496_, lean_object* v_j_497_, lean_object* v_bounded_498_, lean_object* v_h_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_Time_Internal_Bounded_LE_truncateTop(v_n_495_, v_m_496_, v_j_497_, v_bounded_498_, v_h_499_);
lean_dec(v_bounded_498_);
lean_dec(v_j_497_);
lean_dec(v_m_496_);
lean_dec(v_n_495_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg(lean_object* v_bounded_501_){
_start:
{
lean_inc(v_bounded_501_);
return v_bounded_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg___boxed(lean_object* v_bounded_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg(v_bounded_502_);
lean_dec(v_bounded_502_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom(lean_object* v_n_504_, lean_object* v_m_505_, lean_object* v_j_506_, lean_object* v_bounded_507_, lean_object* v_h_508_){
_start:
{
lean_inc(v_bounded_507_);
return v_bounded_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___boxed(lean_object* v_n_509_, lean_object* v_m_510_, lean_object* v_j_511_, lean_object* v_bounded_512_, lean_object* v_h_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_Time_Internal_Bounded_LE_truncateBottom(v_n_509_, v_m_510_, v_j_511_, v_bounded_512_, v_h_513_);
lean_dec(v_bounded_512_);
lean_dec(v_j_511_);
lean_dec(v_m_510_);
lean_dec(v_n_509_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___redArg(lean_object* v_bounded_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = lean_int_neg(v_bounded_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___redArg___boxed(lean_object* v_bounded_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_Time_Internal_Bounded_LE_neg___redArg(v_bounded_517_);
lean_dec(v_bounded_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg(lean_object* v_n_519_, lean_object* v_m_520_, lean_object* v_bounded_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = lean_int_neg(v_bounded_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___boxed(lean_object* v_n_523_, lean_object* v_m_524_, lean_object* v_bounded_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Std_Time_Internal_Bounded_LE_neg(v_n_523_, v_m_524_, v_bounded_525_);
lean_dec(v_bounded_525_);
lean_dec(v_m_524_);
lean_dec(v_n_523_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___redArg(lean_object* v_bounded_527_, lean_object* v_num_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = lean_int_add(v_bounded_527_, v_num_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___redArg___boxed(lean_object* v_bounded_530_, lean_object* v_num_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_Time_Internal_Bounded_LE_add___redArg(v_bounded_530_, v_num_531_);
lean_dec(v_num_531_);
lean_dec(v_bounded_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add(lean_object* v_n_533_, lean_object* v_m_534_, lean_object* v_bounded_535_, lean_object* v_num_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = lean_int_add(v_bounded_535_, v_num_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___boxed(lean_object* v_n_538_, lean_object* v_m_539_, lean_object* v_bounded_540_, lean_object* v_num_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_Time_Internal_Bounded_LE_add(v_n_538_, v_m_539_, v_bounded_540_, v_num_541_);
lean_dec(v_num_541_);
lean_dec(v_bounded_540_);
lean_dec(v_m_539_);
lean_dec(v_n_538_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___redArg(lean_object* v_num_543_, lean_object* v_bounded_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = lean_int_add(v_bounded_544_, v_num_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___redArg___boxed(lean_object* v_num_546_, lean_object* v_bounded_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_Time_Internal_Bounded_LE_addProven___redArg(v_num_546_, v_bounded_547_);
lean_dec(v_bounded_547_);
lean_dec(v_num_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven(lean_object* v_n_549_, lean_object* v_m_550_, lean_object* v_num_551_, lean_object* v_bounded_552_, lean_object* v_h_u2080_553_, lean_object* v_h_u2081_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = lean_int_add(v_bounded_552_, v_num_551_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___boxed(lean_object* v_n_556_, lean_object* v_m_557_, lean_object* v_num_558_, lean_object* v_bounded_559_, lean_object* v_h_u2080_560_, lean_object* v_h_u2081_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Std_Time_Internal_Bounded_LE_addProven(v_n_556_, v_m_557_, v_num_558_, v_bounded_559_, v_h_u2080_560_, v_h_u2081_561_);
lean_dec(v_bounded_559_);
lean_dec(v_num_558_);
lean_dec(v_m_557_);
lean_dec(v_n_556_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___redArg(lean_object* v_bounded_563_, lean_object* v_num_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = lean_int_add(v_bounded_563_, v_num_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___redArg___boxed(lean_object* v_bounded_566_, lean_object* v_num_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Std_Time_Internal_Bounded_LE_addTop___redArg(v_bounded_566_, v_num_567_);
lean_dec(v_num_567_);
lean_dec(v_bounded_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop(lean_object* v_n_569_, lean_object* v_m_570_, lean_object* v_bounded_571_, lean_object* v_num_572_, lean_object* v_h_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = lean_int_add(v_bounded_571_, v_num_572_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___boxed(lean_object* v_n_575_, lean_object* v_m_576_, lean_object* v_bounded_577_, lean_object* v_num_578_, lean_object* v_h_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Std_Time_Internal_Bounded_LE_addTop(v_n_575_, v_m_576_, v_bounded_577_, v_num_578_, v_h_579_);
lean_dec(v_num_578_);
lean_dec(v_bounded_577_);
lean_dec(v_m_576_);
lean_dec(v_n_575_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___redArg(lean_object* v_bounded_581_, lean_object* v_num_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = lean_int_sub(v_bounded_581_, v_num_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___redArg___boxed(lean_object* v_bounded_584_, lean_object* v_num_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Std_Time_Internal_Bounded_LE_subBottom___redArg(v_bounded_584_, v_num_585_);
lean_dec(v_num_585_);
lean_dec(v_bounded_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom(lean_object* v_n_587_, lean_object* v_m_588_, lean_object* v_bounded_589_, lean_object* v_num_590_, lean_object* v_h_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = lean_int_sub(v_bounded_589_, v_num_590_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___boxed(lean_object* v_n_593_, lean_object* v_m_594_, lean_object* v_bounded_595_, lean_object* v_num_596_, lean_object* v_h_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Std_Time_Internal_Bounded_LE_subBottom(v_n_593_, v_m_594_, v_bounded_595_, v_num_596_, v_h_597_);
lean_dec(v_num_596_);
lean_dec(v_bounded_595_);
lean_dec(v_m_594_);
lean_dec(v_n_593_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___redArg(lean_object* v_bounded_599_, lean_object* v_bounded_u2082_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = lean_int_add(v_bounded_599_, v_bounded_u2082_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___redArg___boxed(lean_object* v_bounded_602_, lean_object* v_bounded_u2082_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Std_Time_Internal_Bounded_LE_addBounds___redArg(v_bounded_602_, v_bounded_u2082_603_);
lean_dec(v_bounded_u2082_603_);
lean_dec(v_bounded_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds(lean_object* v_n_605_, lean_object* v_m_606_, lean_object* v_i_607_, lean_object* v_j_608_, lean_object* v_bounded_609_, lean_object* v_bounded_u2082_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = lean_int_add(v_bounded_609_, v_bounded_u2082_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___boxed(lean_object* v_n_612_, lean_object* v_m_613_, lean_object* v_i_614_, lean_object* v_j_615_, lean_object* v_bounded_616_, lean_object* v_bounded_u2082_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Std_Time_Internal_Bounded_LE_addBounds(v_n_612_, v_m_613_, v_i_614_, v_j_615_, v_bounded_616_, v_bounded_u2082_617_);
lean_dec(v_bounded_u2082_617_);
lean_dec(v_bounded_616_);
lean_dec(v_j_615_);
lean_dec(v_i_614_);
lean_dec(v_m_613_);
lean_dec(v_n_612_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___redArg(lean_object* v_bounded_619_, lean_object* v_num_620_){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_int_neg(v_num_620_);
v___x_622_ = lean_int_add(v_bounded_619_, v___x_621_);
lean_dec(v___x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___redArg___boxed(lean_object* v_bounded_623_, lean_object* v_num_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Std_Time_Internal_Bounded_LE_sub___redArg(v_bounded_623_, v_num_624_);
lean_dec(v_num_624_);
lean_dec(v_bounded_623_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub(lean_object* v_n_626_, lean_object* v_m_627_, lean_object* v_bounded_628_, lean_object* v_num_629_){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_int_neg(v_num_629_);
v___x_631_ = lean_int_add(v_bounded_628_, v___x_630_);
lean_dec(v___x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___boxed(lean_object* v_n_632_, lean_object* v_m_633_, lean_object* v_bounded_634_, lean_object* v_num_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Std_Time_Internal_Bounded_LE_sub(v_n_632_, v_m_633_, v_bounded_634_, v_num_635_);
lean_dec(v_num_635_);
lean_dec(v_bounded_634_);
lean_dec(v_m_633_);
lean_dec(v_n_632_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___redArg(lean_object* v_bounded_637_, lean_object* v_bounded_u2082_638_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_int_neg(v_bounded_u2082_638_);
v___x_640_ = lean_int_add(v_bounded_637_, v___x_639_);
lean_dec(v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___redArg___boxed(lean_object* v_bounded_641_, lean_object* v_bounded_u2082_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Std_Time_Internal_Bounded_LE_subBounds___redArg(v_bounded_641_, v_bounded_u2082_642_);
lean_dec(v_bounded_u2082_642_);
lean_dec(v_bounded_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds(lean_object* v_n_644_, lean_object* v_m_645_, lean_object* v_i_646_, lean_object* v_j_647_, lean_object* v_bounded_648_, lean_object* v_bounded_u2082_649_){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_int_neg(v_bounded_u2082_649_);
v___x_651_ = lean_int_add(v_bounded_648_, v___x_650_);
lean_dec(v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___boxed(lean_object* v_n_652_, lean_object* v_m_653_, lean_object* v_i_654_, lean_object* v_j_655_, lean_object* v_bounded_656_, lean_object* v_bounded_u2082_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Std_Time_Internal_Bounded_LE_subBounds(v_n_652_, v_m_653_, v_i_654_, v_j_655_, v_bounded_656_, v_bounded_u2082_657_);
lean_dec(v_bounded_u2082_657_);
lean_dec(v_bounded_656_);
lean_dec(v_j_655_);
lean_dec(v_i_654_);
lean_dec(v_m_653_);
lean_dec(v_n_652_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___redArg(lean_object* v_bounded_659_, lean_object* v_num_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = lean_int_emod(v_bounded_659_, v_num_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___redArg___boxed(lean_object* v_bounded_662_, lean_object* v_num_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Std_Time_Internal_Bounded_LE_emod___redArg(v_bounded_662_, v_num_663_);
lean_dec(v_num_663_);
lean_dec(v_bounded_662_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod(lean_object* v_n_665_, lean_object* v_num_666_, lean_object* v_bounded_667_, lean_object* v_num_668_, lean_object* v_hi_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = lean_int_emod(v_bounded_667_, v_num_668_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___boxed(lean_object* v_n_671_, lean_object* v_num_672_, lean_object* v_bounded_673_, lean_object* v_num_674_, lean_object* v_hi_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Std_Time_Internal_Bounded_LE_emod(v_n_671_, v_num_672_, v_bounded_673_, v_num_674_, v_hi_675_);
lean_dec(v_num_674_);
lean_dec(v_bounded_673_);
lean_dec(v_num_672_);
lean_dec(v_n_671_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___redArg(lean_object* v_bounded_677_, lean_object* v_num_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = lean_int_mod(v_bounded_677_, v_num_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___redArg___boxed(lean_object* v_bounded_680_, lean_object* v_num_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Std_Time_Internal_Bounded_LE_mod___redArg(v_bounded_680_, v_num_681_);
lean_dec(v_num_681_);
lean_dec(v_bounded_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod(lean_object* v_n_683_, lean_object* v_num_684_, lean_object* v_bounded_685_, lean_object* v_num_686_, lean_object* v_hi_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = lean_int_mod(v_bounded_685_, v_num_686_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___boxed(lean_object* v_n_689_, lean_object* v_num_690_, lean_object* v_bounded_691_, lean_object* v_num_692_, lean_object* v_hi_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Std_Time_Internal_Bounded_LE_mod(v_n_689_, v_num_690_, v_bounded_691_, v_num_692_, v_hi_693_);
lean_dec(v_num_692_);
lean_dec(v_bounded_691_);
lean_dec(v_num_690_);
lean_dec(v_n_689_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___redArg(lean_object* v_bounded_695_, lean_object* v_num_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = lean_int_mul(v_bounded_695_, v_num_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___redArg___boxed(lean_object* v_bounded_698_, lean_object* v_num_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Std_Time_Internal_Bounded_LE_mul__pos___redArg(v_bounded_698_, v_num_699_);
lean_dec(v_num_699_);
lean_dec(v_bounded_698_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos(lean_object* v_n_701_, lean_object* v_m_702_, lean_object* v_bounded_703_, lean_object* v_num_704_, lean_object* v_h_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = lean_int_mul(v_bounded_703_, v_num_704_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___boxed(lean_object* v_n_707_, lean_object* v_m_708_, lean_object* v_bounded_709_, lean_object* v_num_710_, lean_object* v_h_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Std_Time_Internal_Bounded_LE_mul__pos(v_n_707_, v_m_708_, v_bounded_709_, v_num_710_, v_h_711_);
lean_dec(v_num_710_);
lean_dec(v_bounded_709_);
lean_dec(v_m_708_);
lean_dec(v_n_707_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___redArg(lean_object* v_bounded_713_, lean_object* v_num_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = lean_int_mul(v_bounded_713_, v_num_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___redArg___boxed(lean_object* v_bounded_716_, lean_object* v_num_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Std_Time_Internal_Bounded_LE_mul__neg___redArg(v_bounded_716_, v_num_717_);
lean_dec(v_num_717_);
lean_dec(v_bounded_716_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg(lean_object* v_n_719_, lean_object* v_m_720_, lean_object* v_bounded_721_, lean_object* v_num_722_, lean_object* v_h_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = lean_int_mul(v_bounded_721_, v_num_722_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___boxed(lean_object* v_n_725_, lean_object* v_m_726_, lean_object* v_bounded_727_, lean_object* v_num_728_, lean_object* v_h_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_Time_Internal_Bounded_LE_mul__neg(v_n_725_, v_m_726_, v_bounded_727_, v_num_728_, v_h_729_);
lean_dec(v_num_728_);
lean_dec(v_bounded_727_);
lean_dec(v_m_726_);
lean_dec(v_n_725_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___redArg(lean_object* v_bounded_731_, lean_object* v_num_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = lean_int_ediv(v_bounded_731_, v_num_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___redArg___boxed(lean_object* v_bounded_734_, lean_object* v_num_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Std_Time_Internal_Bounded_LE_ediv___redArg(v_bounded_734_, v_num_735_);
lean_dec(v_num_735_);
lean_dec(v_bounded_734_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv(lean_object* v_n_737_, lean_object* v_m_738_, lean_object* v_bounded_739_, lean_object* v_num_740_, lean_object* v_h_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = lean_int_ediv(v_bounded_739_, v_num_740_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___boxed(lean_object* v_n_743_, lean_object* v_m_744_, lean_object* v_bounded_745_, lean_object* v_num_746_, lean_object* v_h_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Std_Time_Internal_Bounded_LE_ediv(v_n_743_, v_m_744_, v_bounded_745_, v_num_746_, v_h_747_);
lean_dec(v_num_746_);
lean_dec(v_bounded_745_);
lean_dec(v_m_744_);
lean_dec(v_n_743_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_eq(lean_object* v_n_749_){
_start:
{
lean_inc(v_n_749_);
return v_n_749_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_eq___boxed(lean_object* v_n_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Std_Time_Internal_Bounded_LE_eq(v_n_750_);
lean_dec(v_n_750_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___redArg(lean_object* v_bounded_752_){
_start:
{
lean_inc(v_bounded_752_);
return v_bounded_752_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___redArg___boxed(lean_object* v_bounded_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Std_Time_Internal_Bounded_LE_expand___redArg(v_bounded_753_);
lean_dec(v_bounded_753_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand(lean_object* v_lo_755_, lean_object* v_hi_756_, lean_object* v_nhi_757_, lean_object* v_nlo_758_, lean_object* v_bounded_759_, lean_object* v_h_760_, lean_object* v_h_u2081_761_){
_start:
{
lean_inc(v_bounded_759_);
return v_bounded_759_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___boxed(lean_object* v_lo_762_, lean_object* v_hi_763_, lean_object* v_nhi_764_, lean_object* v_nlo_765_, lean_object* v_bounded_766_, lean_object* v_h_767_, lean_object* v_h_u2081_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Std_Time_Internal_Bounded_LE_expand(v_lo_762_, v_hi_763_, v_nhi_764_, v_nlo_765_, v_bounded_766_, v_h_767_, v_h_u2081_768_);
lean_dec(v_bounded_766_);
lean_dec(v_nlo_765_);
lean_dec(v_nhi_764_);
lean_dec(v_hi_763_);
lean_dec(v_lo_762_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___redArg(lean_object* v_bounded_770_){
_start:
{
lean_inc(v_bounded_770_);
return v_bounded_770_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___redArg___boxed(lean_object* v_bounded_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Std_Time_Internal_Bounded_LE_expandTop___redArg(v_bounded_771_);
lean_dec(v_bounded_771_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop(lean_object* v_lo_773_, lean_object* v_hi_774_, lean_object* v_nhi_775_, lean_object* v_bounded_776_, lean_object* v_h_777_){
_start:
{
lean_inc(v_bounded_776_);
return v_bounded_776_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___boxed(lean_object* v_lo_778_, lean_object* v_hi_779_, lean_object* v_nhi_780_, lean_object* v_bounded_781_, lean_object* v_h_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Std_Time_Internal_Bounded_LE_expandTop(v_lo_778_, v_hi_779_, v_nhi_780_, v_bounded_781_, v_h_782_);
lean_dec(v_bounded_781_);
lean_dec(v_nhi_780_);
lean_dec(v_hi_779_);
lean_dec(v_lo_778_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___redArg(lean_object* v_bounded_784_){
_start:
{
lean_inc(v_bounded_784_);
return v_bounded_784_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___redArg___boxed(lean_object* v_bounded_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Std_Time_Internal_Bounded_LE_expandBottom___redArg(v_bounded_785_);
lean_dec(v_bounded_785_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom(lean_object* v_lo_787_, lean_object* v_hi_788_, lean_object* v_nlo_789_, lean_object* v_bounded_790_, lean_object* v_h_791_){
_start:
{
lean_inc(v_bounded_790_);
return v_bounded_790_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___boxed(lean_object* v_lo_792_, lean_object* v_hi_793_, lean_object* v_nlo_794_, lean_object* v_bounded_795_, lean_object* v_h_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Std_Time_Internal_Bounded_LE_expandBottom(v_lo_792_, v_hi_793_, v_nlo_794_, v_bounded_795_, v_h_796_);
lean_dec(v_bounded_795_);
lean_dec(v_nlo_794_);
lean_dec(v_hi_793_);
lean_dec(v_lo_792_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___redArg(lean_object* v_bounded_798_){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v___x_800_ = lean_int_add(v_bounded_798_, v___x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___redArg___boxed(lean_object* v_bounded_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Std_Time_Internal_Bounded_LE_succ___redArg(v_bounded_801_);
lean_dec(v_bounded_801_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ(lean_object* v_lo_803_, lean_object* v_hi_804_, lean_object* v_bounded_805_, lean_object* v_h_806_){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v___x_808_ = lean_int_add(v_bounded_805_, v___x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___boxed(lean_object* v_lo_809_, lean_object* v_hi_810_, lean_object* v_bounded_811_, lean_object* v_h_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Std_Time_Internal_Bounded_LE_succ(v_lo_809_, v_hi_810_, v_bounded_811_, v_h_812_);
lean_dec(v_bounded_811_);
lean_dec(v_hi_810_);
lean_dec(v_lo_809_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___redArg(lean_object* v_bo_814_){
_start:
{
lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_815_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v___x_816_ = lean_int_dec_le(v___x_815_, v_bo_814_);
if (v___x_816_ == 0)
{
lean_object* v_r_817_; 
v_r_817_ = lean_int_neg(v_bo_814_);
return v_r_817_;
}
else
{
lean_inc(v_bo_814_);
return v_bo_814_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___redArg___boxed(lean_object* v_bo_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Std_Time_Internal_Bounded_LE_abs___redArg(v_bo_818_);
lean_dec(v_bo_818_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs(lean_object* v_i_820_, lean_object* v_bo_821_){
_start:
{
lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_822_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v___x_823_ = lean_int_dec_le(v___x_822_, v_bo_821_);
if (v___x_823_ == 0)
{
lean_object* v_r_824_; 
v_r_824_ = lean_int_neg(v_bo_821_);
return v_r_824_;
}
else
{
lean_inc(v_bo_821_);
return v_bo_821_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___boxed(lean_object* v_i_825_, lean_object* v_bo_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Std_Time_Internal_Bounded_LE_abs(v_i_825_, v_bo_826_);
lean_dec(v_bo_826_);
lean_dec(v_i_825_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___redArg(lean_object* v_bounded_828_, lean_object* v_val_829_){
_start:
{
uint8_t v___x_830_; 
v___x_830_ = lean_int_dec_le(v_bounded_828_, v_val_829_);
if (v___x_830_ == 0)
{
lean_inc(v_bounded_828_);
return v_bounded_828_;
}
else
{
lean_inc(v_val_829_);
return v_val_829_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___redArg___boxed(lean_object* v_bounded_831_, lean_object* v_val_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Std_Time_Internal_Bounded_LE_max___redArg(v_bounded_831_, v_val_832_);
lean_dec(v_val_832_);
lean_dec(v_bounded_831_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max(lean_object* v_n_834_, lean_object* v_m_835_, lean_object* v_bounded_836_, lean_object* v_val_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Std_Time_Internal_Bounded_LE_max___redArg(v_bounded_836_, v_val_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___boxed(lean_object* v_n_839_, lean_object* v_m_840_, lean_object* v_bounded_841_, lean_object* v_val_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Std_Time_Internal_Bounded_LE_max(v_n_839_, v_m_840_, v_bounded_841_, v_val_842_);
lean_dec(v_val_842_);
lean_dec(v_bounded_841_);
lean_dec(v_m_840_);
lean_dec(v_n_839_);
return v_res_843_;
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
