// Lean compiler output
// Module: Std.Time.Internal.Bounded
// Imports: public import Init.Data.Int.DivMod.Lemmas public import Init.Data.Order.Ord public import Init.Omega import Init.Ext
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
lean_inc(v_val_133_);
v___x_134_ = lean_apply_2(v_inst_132_, v_val_133_, v_hi_131_);
lean_inc(v_val_133_);
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
lean_inc(v_val_145_);
v___x_146_ = lean_apply_2(v_inst_144_, v_val_145_, v_hi_143_);
lean_inc(v_val_145_);
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
lean_object* v___x_431_; 
v___x_431_ = l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg(v_x_425_, v_x_426_, v_h__1_427_, v_h__2_428_, v_h__3_429_, v_h__4_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___boxed(lean_object* v_motive_432_, lean_object* v_x_433_, lean_object* v_x_434_, lean_object* v_h__1_435_, lean_object* v_h__2_436_, lean_object* v_h__3_437_, lean_object* v_h__4_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter(v_motive_432_, v_x_433_, v_x_434_, v_h__1_435_, v_h__2_436_, v_h__3_437_, v_h__4_438_);
lean_dec(v_x_434_);
lean_dec(v_x_433_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___redArg(lean_object* v_b_440_, lean_object* v_i_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = lean_int_mod(v_b_440_, v_i_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___redArg___boxed(lean_object* v_b_443_, lean_object* v_i_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Std_Time_Internal_Bounded_LE_byMod___redArg(v_b_443_, v_i_444_);
lean_dec(v_i_444_);
lean_dec(v_b_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod(lean_object* v_b_446_, lean_object* v_i_447_, lean_object* v_hi_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = lean_int_mod(v_b_446_, v_i_447_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___boxed(lean_object* v_b_450_, lean_object* v_i_451_, lean_object* v_hi_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Std_Time_Internal_Bounded_LE_byMod(v_b_450_, v_i_451_, v_hi_452_);
lean_dec(v_i_451_);
lean_dec(v_b_450_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___redArg(lean_object* v_n_454_, lean_object* v_bounded_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = lean_int_sub(v_bounded_455_, v_n_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___redArg___boxed(lean_object* v_n_457_, lean_object* v_bounded_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_Time_Internal_Bounded_LE_truncate___redArg(v_n_457_, v_bounded_458_);
lean_dec(v_bounded_458_);
lean_dec(v_n_457_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate(lean_object* v_n_460_, lean_object* v_m_461_, lean_object* v_bounded_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = lean_int_sub(v_bounded_462_, v_n_460_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___boxed(lean_object* v_n_464_, lean_object* v_m_465_, lean_object* v_bounded_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_Time_Internal_Bounded_LE_truncate(v_n_464_, v_m_465_, v_bounded_466_);
lean_dec(v_bounded_466_);
lean_dec(v_m_465_);
lean_dec(v_n_464_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___redArg(lean_object* v_bounded_468_){
_start:
{
lean_inc(v_bounded_468_);
return v_bounded_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___redArg___boxed(lean_object* v_bounded_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Std_Time_Internal_Bounded_LE_truncateTop___redArg(v_bounded_469_);
lean_dec(v_bounded_469_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop(lean_object* v_n_471_, lean_object* v_m_472_, lean_object* v_j_473_, lean_object* v_bounded_474_, lean_object* v_h_475_){
_start:
{
lean_inc(v_bounded_474_);
return v_bounded_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___boxed(lean_object* v_n_476_, lean_object* v_m_477_, lean_object* v_j_478_, lean_object* v_bounded_479_, lean_object* v_h_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Std_Time_Internal_Bounded_LE_truncateTop(v_n_476_, v_m_477_, v_j_478_, v_bounded_479_, v_h_480_);
lean_dec(v_bounded_479_);
lean_dec(v_j_478_);
lean_dec(v_m_477_);
lean_dec(v_n_476_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg(lean_object* v_bounded_482_){
_start:
{
lean_inc(v_bounded_482_);
return v_bounded_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg___boxed(lean_object* v_bounded_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg(v_bounded_483_);
lean_dec(v_bounded_483_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom(lean_object* v_n_485_, lean_object* v_m_486_, lean_object* v_j_487_, lean_object* v_bounded_488_, lean_object* v_h_489_){
_start:
{
lean_inc(v_bounded_488_);
return v_bounded_488_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___boxed(lean_object* v_n_490_, lean_object* v_m_491_, lean_object* v_j_492_, lean_object* v_bounded_493_, lean_object* v_h_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Std_Time_Internal_Bounded_LE_truncateBottom(v_n_490_, v_m_491_, v_j_492_, v_bounded_493_, v_h_494_);
lean_dec(v_bounded_493_);
lean_dec(v_j_492_);
lean_dec(v_m_491_);
lean_dec(v_n_490_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___redArg(lean_object* v_bounded_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = lean_int_neg(v_bounded_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___redArg___boxed(lean_object* v_bounded_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Std_Time_Internal_Bounded_LE_neg___redArg(v_bounded_498_);
lean_dec(v_bounded_498_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg(lean_object* v_n_500_, lean_object* v_m_501_, lean_object* v_bounded_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = lean_int_neg(v_bounded_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___boxed(lean_object* v_n_504_, lean_object* v_m_505_, lean_object* v_bounded_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Std_Time_Internal_Bounded_LE_neg(v_n_504_, v_m_505_, v_bounded_506_);
lean_dec(v_bounded_506_);
lean_dec(v_m_505_);
lean_dec(v_n_504_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___redArg(lean_object* v_bounded_508_, lean_object* v_num_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = lean_int_add(v_bounded_508_, v_num_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___redArg___boxed(lean_object* v_bounded_511_, lean_object* v_num_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Std_Time_Internal_Bounded_LE_add___redArg(v_bounded_511_, v_num_512_);
lean_dec(v_num_512_);
lean_dec(v_bounded_511_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add(lean_object* v_n_514_, lean_object* v_m_515_, lean_object* v_bounded_516_, lean_object* v_num_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = lean_int_add(v_bounded_516_, v_num_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___boxed(lean_object* v_n_519_, lean_object* v_m_520_, lean_object* v_bounded_521_, lean_object* v_num_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Std_Time_Internal_Bounded_LE_add(v_n_519_, v_m_520_, v_bounded_521_, v_num_522_);
lean_dec(v_num_522_);
lean_dec(v_bounded_521_);
lean_dec(v_m_520_);
lean_dec(v_n_519_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___redArg(lean_object* v_num_524_, lean_object* v_bounded_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = lean_int_add(v_bounded_525_, v_num_524_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___redArg___boxed(lean_object* v_num_527_, lean_object* v_bounded_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Std_Time_Internal_Bounded_LE_addProven___redArg(v_num_527_, v_bounded_528_);
lean_dec(v_bounded_528_);
lean_dec(v_num_527_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven(lean_object* v_n_530_, lean_object* v_m_531_, lean_object* v_num_532_, lean_object* v_bounded_533_, lean_object* v_h_u2080_534_, lean_object* v_h_u2081_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = lean_int_add(v_bounded_533_, v_num_532_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___boxed(lean_object* v_n_537_, lean_object* v_m_538_, lean_object* v_num_539_, lean_object* v_bounded_540_, lean_object* v_h_u2080_541_, lean_object* v_h_u2081_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Std_Time_Internal_Bounded_LE_addProven(v_n_537_, v_m_538_, v_num_539_, v_bounded_540_, v_h_u2080_541_, v_h_u2081_542_);
lean_dec(v_bounded_540_);
lean_dec(v_num_539_);
lean_dec(v_m_538_);
lean_dec(v_n_537_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___redArg(lean_object* v_bounded_544_, lean_object* v_num_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = lean_int_add(v_bounded_544_, v_num_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___redArg___boxed(lean_object* v_bounded_547_, lean_object* v_num_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Std_Time_Internal_Bounded_LE_addTop___redArg(v_bounded_547_, v_num_548_);
lean_dec(v_num_548_);
lean_dec(v_bounded_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop(lean_object* v_n_550_, lean_object* v_m_551_, lean_object* v_bounded_552_, lean_object* v_num_553_, lean_object* v_h_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = lean_int_add(v_bounded_552_, v_num_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___boxed(lean_object* v_n_556_, lean_object* v_m_557_, lean_object* v_bounded_558_, lean_object* v_num_559_, lean_object* v_h_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_Time_Internal_Bounded_LE_addTop(v_n_556_, v_m_557_, v_bounded_558_, v_num_559_, v_h_560_);
lean_dec(v_num_559_);
lean_dec(v_bounded_558_);
lean_dec(v_m_557_);
lean_dec(v_n_556_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___redArg(lean_object* v_bounded_562_, lean_object* v_num_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = lean_int_sub(v_bounded_562_, v_num_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___redArg___boxed(lean_object* v_bounded_565_, lean_object* v_num_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_Time_Internal_Bounded_LE_subBottom___redArg(v_bounded_565_, v_num_566_);
lean_dec(v_num_566_);
lean_dec(v_bounded_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom(lean_object* v_n_568_, lean_object* v_m_569_, lean_object* v_bounded_570_, lean_object* v_num_571_, lean_object* v_h_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = lean_int_sub(v_bounded_570_, v_num_571_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___boxed(lean_object* v_n_574_, lean_object* v_m_575_, lean_object* v_bounded_576_, lean_object* v_num_577_, lean_object* v_h_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Std_Time_Internal_Bounded_LE_subBottom(v_n_574_, v_m_575_, v_bounded_576_, v_num_577_, v_h_578_);
lean_dec(v_num_577_);
lean_dec(v_bounded_576_);
lean_dec(v_m_575_);
lean_dec(v_n_574_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___redArg(lean_object* v_bounded_580_, lean_object* v_bounded_u2082_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = lean_int_add(v_bounded_580_, v_bounded_u2082_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___redArg___boxed(lean_object* v_bounded_583_, lean_object* v_bounded_u2082_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_Time_Internal_Bounded_LE_addBounds___redArg(v_bounded_583_, v_bounded_u2082_584_);
lean_dec(v_bounded_u2082_584_);
lean_dec(v_bounded_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds(lean_object* v_n_586_, lean_object* v_m_587_, lean_object* v_i_588_, lean_object* v_j_589_, lean_object* v_bounded_590_, lean_object* v_bounded_u2082_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = lean_int_add(v_bounded_590_, v_bounded_u2082_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___boxed(lean_object* v_n_593_, lean_object* v_m_594_, lean_object* v_i_595_, lean_object* v_j_596_, lean_object* v_bounded_597_, lean_object* v_bounded_u2082_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Std_Time_Internal_Bounded_LE_addBounds(v_n_593_, v_m_594_, v_i_595_, v_j_596_, v_bounded_597_, v_bounded_u2082_598_);
lean_dec(v_bounded_u2082_598_);
lean_dec(v_bounded_597_);
lean_dec(v_j_596_);
lean_dec(v_i_595_);
lean_dec(v_m_594_);
lean_dec(v_n_593_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___redArg(lean_object* v_bounded_600_, lean_object* v_num_601_){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_int_neg(v_num_601_);
v___x_603_ = lean_int_add(v_bounded_600_, v___x_602_);
lean_dec(v___x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___redArg___boxed(lean_object* v_bounded_604_, lean_object* v_num_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Std_Time_Internal_Bounded_LE_sub___redArg(v_bounded_604_, v_num_605_);
lean_dec(v_num_605_);
lean_dec(v_bounded_604_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub(lean_object* v_n_607_, lean_object* v_m_608_, lean_object* v_bounded_609_, lean_object* v_num_610_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_int_neg(v_num_610_);
v___x_612_ = lean_int_add(v_bounded_609_, v___x_611_);
lean_dec(v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___boxed(lean_object* v_n_613_, lean_object* v_m_614_, lean_object* v_bounded_615_, lean_object* v_num_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Std_Time_Internal_Bounded_LE_sub(v_n_613_, v_m_614_, v_bounded_615_, v_num_616_);
lean_dec(v_num_616_);
lean_dec(v_bounded_615_);
lean_dec(v_m_614_);
lean_dec(v_n_613_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___redArg(lean_object* v_bounded_618_, lean_object* v_bounded_u2082_619_){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_int_neg(v_bounded_u2082_619_);
v___x_621_ = lean_int_add(v_bounded_618_, v___x_620_);
lean_dec(v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___redArg___boxed(lean_object* v_bounded_622_, lean_object* v_bounded_u2082_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Std_Time_Internal_Bounded_LE_subBounds___redArg(v_bounded_622_, v_bounded_u2082_623_);
lean_dec(v_bounded_u2082_623_);
lean_dec(v_bounded_622_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds(lean_object* v_n_625_, lean_object* v_m_626_, lean_object* v_i_627_, lean_object* v_j_628_, lean_object* v_bounded_629_, lean_object* v_bounded_u2082_630_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_int_neg(v_bounded_u2082_630_);
v___x_632_ = lean_int_add(v_bounded_629_, v___x_631_);
lean_dec(v___x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___boxed(lean_object* v_n_633_, lean_object* v_m_634_, lean_object* v_i_635_, lean_object* v_j_636_, lean_object* v_bounded_637_, lean_object* v_bounded_u2082_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Std_Time_Internal_Bounded_LE_subBounds(v_n_633_, v_m_634_, v_i_635_, v_j_636_, v_bounded_637_, v_bounded_u2082_638_);
lean_dec(v_bounded_u2082_638_);
lean_dec(v_bounded_637_);
lean_dec(v_j_636_);
lean_dec(v_i_635_);
lean_dec(v_m_634_);
lean_dec(v_n_633_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___redArg(lean_object* v_bounded_640_, lean_object* v_num_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = lean_int_emod(v_bounded_640_, v_num_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___redArg___boxed(lean_object* v_bounded_643_, lean_object* v_num_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Std_Time_Internal_Bounded_LE_emod___redArg(v_bounded_643_, v_num_644_);
lean_dec(v_num_644_);
lean_dec(v_bounded_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod(lean_object* v_n_646_, lean_object* v_num_647_, lean_object* v_bounded_648_, lean_object* v_num_649_, lean_object* v_hi_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = lean_int_emod(v_bounded_648_, v_num_649_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___boxed(lean_object* v_n_652_, lean_object* v_num_653_, lean_object* v_bounded_654_, lean_object* v_num_655_, lean_object* v_hi_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Std_Time_Internal_Bounded_LE_emod(v_n_652_, v_num_653_, v_bounded_654_, v_num_655_, v_hi_656_);
lean_dec(v_num_655_);
lean_dec(v_bounded_654_);
lean_dec(v_num_653_);
lean_dec(v_n_652_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___redArg(lean_object* v_bounded_658_, lean_object* v_num_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = lean_int_mod(v_bounded_658_, v_num_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___redArg___boxed(lean_object* v_bounded_661_, lean_object* v_num_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Std_Time_Internal_Bounded_LE_mod___redArg(v_bounded_661_, v_num_662_);
lean_dec(v_num_662_);
lean_dec(v_bounded_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod(lean_object* v_n_664_, lean_object* v_num_665_, lean_object* v_bounded_666_, lean_object* v_num_667_, lean_object* v_hi_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = lean_int_mod(v_bounded_666_, v_num_667_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___boxed(lean_object* v_n_670_, lean_object* v_num_671_, lean_object* v_bounded_672_, lean_object* v_num_673_, lean_object* v_hi_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_Time_Internal_Bounded_LE_mod(v_n_670_, v_num_671_, v_bounded_672_, v_num_673_, v_hi_674_);
lean_dec(v_num_673_);
lean_dec(v_bounded_672_);
lean_dec(v_num_671_);
lean_dec(v_n_670_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___redArg(lean_object* v_bounded_676_, lean_object* v_num_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = lean_int_mul(v_bounded_676_, v_num_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___redArg___boxed(lean_object* v_bounded_679_, lean_object* v_num_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Std_Time_Internal_Bounded_LE_mul__pos___redArg(v_bounded_679_, v_num_680_);
lean_dec(v_num_680_);
lean_dec(v_bounded_679_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos(lean_object* v_n_682_, lean_object* v_m_683_, lean_object* v_bounded_684_, lean_object* v_num_685_, lean_object* v_h_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = lean_int_mul(v_bounded_684_, v_num_685_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___boxed(lean_object* v_n_688_, lean_object* v_m_689_, lean_object* v_bounded_690_, lean_object* v_num_691_, lean_object* v_h_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Std_Time_Internal_Bounded_LE_mul__pos(v_n_688_, v_m_689_, v_bounded_690_, v_num_691_, v_h_692_);
lean_dec(v_num_691_);
lean_dec(v_bounded_690_);
lean_dec(v_m_689_);
lean_dec(v_n_688_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___redArg(lean_object* v_bounded_694_, lean_object* v_num_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = lean_int_mul(v_bounded_694_, v_num_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___redArg___boxed(lean_object* v_bounded_697_, lean_object* v_num_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Std_Time_Internal_Bounded_LE_mul__neg___redArg(v_bounded_697_, v_num_698_);
lean_dec(v_num_698_);
lean_dec(v_bounded_697_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg(lean_object* v_n_700_, lean_object* v_m_701_, lean_object* v_bounded_702_, lean_object* v_num_703_, lean_object* v_h_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = lean_int_mul(v_bounded_702_, v_num_703_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___boxed(lean_object* v_n_706_, lean_object* v_m_707_, lean_object* v_bounded_708_, lean_object* v_num_709_, lean_object* v_h_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Std_Time_Internal_Bounded_LE_mul__neg(v_n_706_, v_m_707_, v_bounded_708_, v_num_709_, v_h_710_);
lean_dec(v_num_709_);
lean_dec(v_bounded_708_);
lean_dec(v_m_707_);
lean_dec(v_n_706_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___redArg(lean_object* v_bounded_712_, lean_object* v_num_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = lean_int_ediv(v_bounded_712_, v_num_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___redArg___boxed(lean_object* v_bounded_715_, lean_object* v_num_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Std_Time_Internal_Bounded_LE_ediv___redArg(v_bounded_715_, v_num_716_);
lean_dec(v_num_716_);
lean_dec(v_bounded_715_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv(lean_object* v_n_718_, lean_object* v_m_719_, lean_object* v_bounded_720_, lean_object* v_num_721_, lean_object* v_h_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = lean_int_ediv(v_bounded_720_, v_num_721_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___boxed(lean_object* v_n_724_, lean_object* v_m_725_, lean_object* v_bounded_726_, lean_object* v_num_727_, lean_object* v_h_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Std_Time_Internal_Bounded_LE_ediv(v_n_724_, v_m_725_, v_bounded_726_, v_num_727_, v_h_728_);
lean_dec(v_num_727_);
lean_dec(v_bounded_726_);
lean_dec(v_m_725_);
lean_dec(v_n_724_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_eq(lean_object* v_n_730_){
_start:
{
lean_inc(v_n_730_);
return v_n_730_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_eq___boxed(lean_object* v_n_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Std_Time_Internal_Bounded_LE_eq(v_n_731_);
lean_dec(v_n_731_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___redArg(lean_object* v_bounded_733_){
_start:
{
lean_inc(v_bounded_733_);
return v_bounded_733_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___redArg___boxed(lean_object* v_bounded_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_Time_Internal_Bounded_LE_expand___redArg(v_bounded_734_);
lean_dec(v_bounded_734_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand(lean_object* v_lo_736_, lean_object* v_hi_737_, lean_object* v_nhi_738_, lean_object* v_nlo_739_, lean_object* v_bounded_740_, lean_object* v_h_741_, lean_object* v_h_u2081_742_){
_start:
{
lean_inc(v_bounded_740_);
return v_bounded_740_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___boxed(lean_object* v_lo_743_, lean_object* v_hi_744_, lean_object* v_nhi_745_, lean_object* v_nlo_746_, lean_object* v_bounded_747_, lean_object* v_h_748_, lean_object* v_h_u2081_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Std_Time_Internal_Bounded_LE_expand(v_lo_743_, v_hi_744_, v_nhi_745_, v_nlo_746_, v_bounded_747_, v_h_748_, v_h_u2081_749_);
lean_dec(v_bounded_747_);
lean_dec(v_nlo_746_);
lean_dec(v_nhi_745_);
lean_dec(v_hi_744_);
lean_dec(v_lo_743_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___redArg(lean_object* v_bounded_751_){
_start:
{
lean_inc(v_bounded_751_);
return v_bounded_751_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___redArg___boxed(lean_object* v_bounded_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Std_Time_Internal_Bounded_LE_expandTop___redArg(v_bounded_752_);
lean_dec(v_bounded_752_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop(lean_object* v_lo_754_, lean_object* v_hi_755_, lean_object* v_nhi_756_, lean_object* v_bounded_757_, lean_object* v_h_758_){
_start:
{
lean_inc(v_bounded_757_);
return v_bounded_757_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___boxed(lean_object* v_lo_759_, lean_object* v_hi_760_, lean_object* v_nhi_761_, lean_object* v_bounded_762_, lean_object* v_h_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Std_Time_Internal_Bounded_LE_expandTop(v_lo_759_, v_hi_760_, v_nhi_761_, v_bounded_762_, v_h_763_);
lean_dec(v_bounded_762_);
lean_dec(v_nhi_761_);
lean_dec(v_hi_760_);
lean_dec(v_lo_759_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___redArg(lean_object* v_bounded_765_){
_start:
{
lean_inc(v_bounded_765_);
return v_bounded_765_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___redArg___boxed(lean_object* v_bounded_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Std_Time_Internal_Bounded_LE_expandBottom___redArg(v_bounded_766_);
lean_dec(v_bounded_766_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom(lean_object* v_lo_768_, lean_object* v_hi_769_, lean_object* v_nlo_770_, lean_object* v_bounded_771_, lean_object* v_h_772_){
_start:
{
lean_inc(v_bounded_771_);
return v_bounded_771_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___boxed(lean_object* v_lo_773_, lean_object* v_hi_774_, lean_object* v_nlo_775_, lean_object* v_bounded_776_, lean_object* v_h_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Std_Time_Internal_Bounded_LE_expandBottom(v_lo_773_, v_hi_774_, v_nlo_775_, v_bounded_776_, v_h_777_);
lean_dec(v_bounded_776_);
lean_dec(v_nlo_775_);
lean_dec(v_hi_774_);
lean_dec(v_lo_773_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___redArg(lean_object* v_bounded_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v___x_781_ = lean_int_add(v_bounded_779_, v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___redArg___boxed(lean_object* v_bounded_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Std_Time_Internal_Bounded_LE_succ___redArg(v_bounded_782_);
lean_dec(v_bounded_782_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ(lean_object* v_lo_784_, lean_object* v_hi_785_, lean_object* v_bounded_786_, lean_object* v_h_787_){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v___x_789_ = lean_int_add(v_bounded_786_, v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___boxed(lean_object* v_lo_790_, lean_object* v_hi_791_, lean_object* v_bounded_792_, lean_object* v_h_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Std_Time_Internal_Bounded_LE_succ(v_lo_790_, v_hi_791_, v_bounded_792_, v_h_793_);
lean_dec(v_bounded_792_);
lean_dec(v_hi_791_);
lean_dec(v_lo_790_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___redArg(lean_object* v_bo_795_){
_start:
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v___x_797_ = lean_int_dec_le(v___x_796_, v_bo_795_);
if (v___x_797_ == 0)
{
lean_object* v_r_798_; 
v_r_798_ = lean_int_neg(v_bo_795_);
return v_r_798_;
}
else
{
lean_inc(v_bo_795_);
return v_bo_795_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___redArg___boxed(lean_object* v_bo_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Std_Time_Internal_Bounded_LE_abs___redArg(v_bo_799_);
lean_dec(v_bo_799_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs(lean_object* v_i_801_, lean_object* v_bo_802_){
_start:
{
lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_803_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v___x_804_ = lean_int_dec_le(v___x_803_, v_bo_802_);
if (v___x_804_ == 0)
{
lean_object* v_r_805_; 
v_r_805_ = lean_int_neg(v_bo_802_);
return v_r_805_;
}
else
{
lean_inc(v_bo_802_);
return v_bo_802_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___boxed(lean_object* v_i_806_, lean_object* v_bo_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Std_Time_Internal_Bounded_LE_abs(v_i_806_, v_bo_807_);
lean_dec(v_bo_807_);
lean_dec(v_i_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___redArg(lean_object* v_bounded_809_, lean_object* v_val_810_){
_start:
{
uint8_t v___x_811_; 
v___x_811_ = lean_int_dec_le(v_bounded_809_, v_val_810_);
if (v___x_811_ == 0)
{
lean_inc(v_bounded_809_);
return v_bounded_809_;
}
else
{
lean_inc(v_val_810_);
return v_val_810_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___redArg___boxed(lean_object* v_bounded_812_, lean_object* v_val_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Std_Time_Internal_Bounded_LE_max___redArg(v_bounded_812_, v_val_813_);
lean_dec(v_val_813_);
lean_dec(v_bounded_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max(lean_object* v_n_815_, lean_object* v_m_816_, lean_object* v_bounded_817_, lean_object* v_val_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Std_Time_Internal_Bounded_LE_max___redArg(v_bounded_817_, v_val_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___boxed(lean_object* v_n_820_, lean_object* v_m_821_, lean_object* v_bounded_822_, lean_object* v_val_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_Time_Internal_Bounded_LE_max(v_n_820_, v_m_821_, v_bounded_822_, v_val_823_);
lean_dec(v_val_823_);
lean_dec(v_bounded_822_);
lean_dec(v_m_821_);
lean_dec(v_n_820_);
return v_res_824_;
}
}
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Ord(uint8_t builtin);
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
