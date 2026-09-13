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
uint8_t v___y_254_; uint8_t v___x_257_; 
v___x_257_ = lean_int_dec_le(v_lo_250_, v_val_252_);
if (v___x_257_ == 0)
{
v___y_254_ = v___x_257_;
goto v___jp_253_;
}
else
{
uint8_t v___x_258_; 
v___x_258_ = lean_int_dec_le(v_val_252_, v_hi_251_);
v___y_254_ = v___x_258_;
goto v___jp_253_;
}
v___jp_253_:
{
if (v___y_254_ == 0)
{
lean_object* v___x_255_; 
lean_dec(v_val_252_);
v___x_255_ = lean_box(0);
return v___x_255_;
}
else
{
lean_object* v___x_256_; 
v___x_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_256_, 0, v_val_252_);
return v___x_256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofInt___boxed(lean_object* v_lo_259_, lean_object* v_hi_260_, lean_object* v_val_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_Time_Internal_Bounded_LE_ofInt(v_lo_259_, v_hi_260_, v_val_261_);
lean_dec(v_hi_260_);
lean_dec(v_lo_259_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat___redArg(lean_object* v_val_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = lean_nat_to_int(v_val_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat(lean_object* v_hi_265_, lean_object* v_val_266_, lean_object* v_h_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_nat_to_int(v_val_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat___boxed(lean_object* v_hi_269_, lean_object* v_val_270_, lean_object* v_h_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Std_Time_Internal_Bounded_LE_ofNat(v_hi_269_, v_val_270_, v_h_271_);
lean_dec(v_hi_269_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x3f(lean_object* v_hi_273_, lean_object* v_val_274_){
_start:
{
uint8_t v___x_275_; 
v___x_275_ = lean_nat_dec_le(v_val_274_, v_hi_273_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; 
lean_dec(v_val_274_);
v___x_276_ = lean_box(0);
return v___x_276_;
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_nat_to_int(v_val_274_);
v___x_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x3f___boxed(lean_object* v_hi_279_, lean_object* v_val_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Std_Time_Internal_Bounded_LE_ofNat_x3f(v_hi_279_, v_val_280_);
lean_dec(v_hi_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27___redArg(lean_object* v_val_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_nat_to_int(v_val_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27(lean_object* v_lo_284_, lean_object* v_hi_285_, lean_object* v_val_286_, lean_object* v_h_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_nat_to_int(v_val_286_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofNat_x27___boxed(lean_object* v_lo_289_, lean_object* v_hi_290_, lean_object* v_val_291_, lean_object* v_h_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Std_Time_Internal_Bounded_LE_ofNat_x27(v_lo_289_, v_hi_290_, v_val_291_, v_h_292_);
lean_dec(v_hi_290_);
lean_dec(v_lo_289_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___redArg(lean_object* v_lo_294_, lean_object* v_hi_295_, lean_object* v_val_296_){
_start:
{
uint8_t v___x_297_; 
v___x_297_ = lean_int_dec_le(v_lo_294_, v_val_296_);
if (v___x_297_ == 0)
{
lean_inc(v_lo_294_);
return v_lo_294_;
}
else
{
uint8_t v___x_298_; 
v___x_298_ = lean_int_dec_le(v_val_296_, v_hi_295_);
if (v___x_298_ == 0)
{
lean_inc(v_hi_295_);
return v_hi_295_;
}
else
{
lean_inc(v_val_296_);
return v_val_296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___redArg___boxed(lean_object* v_lo_299_, lean_object* v_hi_300_, lean_object* v_val_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Std_Time_Internal_Bounded_LE_clip___redArg(v_lo_299_, v_hi_300_, v_val_301_);
lean_dec(v_val_301_);
lean_dec(v_hi_300_);
lean_dec(v_lo_299_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip(lean_object* v_lo_303_, lean_object* v_hi_304_, lean_object* v_val_305_, lean_object* v_h_306_){
_start:
{
uint8_t v___x_307_; 
v___x_307_ = lean_int_dec_le(v_lo_303_, v_val_305_);
if (v___x_307_ == 0)
{
lean_inc(v_lo_303_);
return v_lo_303_;
}
else
{
uint8_t v___x_308_; 
v___x_308_ = lean_int_dec_le(v_val_305_, v_hi_304_);
if (v___x_308_ == 0)
{
lean_inc(v_hi_304_);
return v_hi_304_;
}
else
{
lean_inc(v_val_305_);
return v_val_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_clip___boxed(lean_object* v_lo_309_, lean_object* v_hi_310_, lean_object* v_val_311_, lean_object* v_h_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Std_Time_Internal_Bounded_LE_clip(v_lo_309_, v_hi_310_, v_val_311_, v_h_312_);
lean_dec(v_val_311_);
lean_dec(v_hi_310_);
lean_dec(v_lo_309_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___redArg(lean_object* v_n_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Int_toNat(v_n_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___redArg___boxed(lean_object* v_n_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Std_Time_Internal_Bounded_LE_toNat___redArg(v_n_316_);
lean_dec(v_n_316_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat(lean_object* v_lo_318_, lean_object* v_hi_319_, lean_object* v_n_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Int_toNat(v_n_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat___boxed(lean_object* v_lo_322_, lean_object* v_hi_323_, lean_object* v_n_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Std_Time_Internal_Bounded_LE_toNat(v_lo_322_, v_hi_323_, v_n_324_);
lean_dec(v_n_324_);
lean_dec(v_hi_323_);
lean_dec(v_lo_322_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg(lean_object* v_n_326_){
_start:
{
lean_object* v_intZero_327_; uint8_t v_isNeg_328_; lean_object* v_a_329_; 
v_intZero_327_ = lean_obj_once(&l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0, &l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0_once, _init_l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0);
v_isNeg_328_ = lean_int_dec_lt(v_n_326_, v_intZero_327_);
v_a_329_ = lean_nat_abs(v_n_326_);
return v_a_329_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg___boxed(lean_object* v_n_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg(v_n_330_);
lean_dec(v_n_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27(lean_object* v_lo_332_, lean_object* v_hi_333_, lean_object* v_n_334_, lean_object* v_h_335_){
_start:
{
lean_object* v_intZero_336_; uint8_t v_isNeg_337_; lean_object* v_a_338_; 
v_intZero_336_ = lean_obj_once(&l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0, &l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0_once, _init_l_Std_Time_Internal_Bounded_instRepr___redArg___lam__0___closed__0);
v_isNeg_337_ = lean_int_dec_lt(v_n_334_, v_intZero_336_);
v_a_338_ = lean_nat_abs(v_n_334_);
return v_a_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toNat_x27___boxed(lean_object* v_lo_339_, lean_object* v_hi_340_, lean_object* v_n_341_, lean_object* v_h_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Std_Time_Internal_Bounded_LE_toNat_x27(v_lo_339_, v_hi_340_, v_n_341_, v_h_342_);
lean_dec(v_n_341_);
lean_dec(v_hi_340_);
lean_dec(v_lo_339_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___redArg(lean_object* v_n_344_){
_start:
{
lean_inc(v_n_344_);
return v_n_344_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___redArg___boxed(lean_object* v_n_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Std_Time_Internal_Bounded_LE_toInt___redArg(v_n_345_);
lean_dec(v_n_345_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt(lean_object* v_lo_347_, lean_object* v_hi_348_, lean_object* v_n_349_){
_start:
{
lean_inc(v_n_349_);
return v_n_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toInt___boxed(lean_object* v_lo_350_, lean_object* v_hi_351_, lean_object* v_n_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_Time_Internal_Bounded_LE_toInt(v_lo_350_, v_hi_351_, v_n_352_);
lean_dec(v_n_352_);
lean_dec(v_hi_351_);
lean_dec(v_lo_350_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___redArg(lean_object* v_n_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Int_toNat(v_n_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___redArg___boxed(lean_object* v_n_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Std_Time_Internal_Bounded_LE_toFin___redArg(v_n_356_);
lean_dec(v_n_356_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin(lean_object* v_lo_358_, lean_object* v_hi_359_, lean_object* v_n_360_, lean_object* v_h_u2080_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Int_toNat(v_n_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_toFin___boxed(lean_object* v_lo_363_, lean_object* v_hi_364_, lean_object* v_n_365_, lean_object* v_h_u2080_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Std_Time_Internal_Bounded_LE_toFin(v_lo_363_, v_hi_364_, v_n_365_, v_h_u2080_366_);
lean_dec(v_n_365_);
lean_dec(v_hi_364_);
lean_dec(v_lo_363_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin___redArg(lean_object* v_fin_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_nat_to_int(v_fin_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin(lean_object* v_hi_370_, lean_object* v_fin_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = lean_nat_to_int(v_fin_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin___boxed(lean_object* v_hi_373_, lean_object* v_fin_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Std_Time_Internal_Bounded_LE_ofFin(v_hi_373_, v_fin_374_);
lean_dec(v_hi_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27___redArg(lean_object* v_lo_376_, lean_object* v_fin_377_){
_start:
{
uint8_t v___x_378_; 
v___x_378_ = lean_nat_dec_le(v_lo_376_, v_fin_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
lean_dec(v_fin_377_);
v___x_379_ = lean_nat_to_int(v_lo_376_);
return v___x_379_;
}
else
{
lean_object* v___x_380_; 
lean_dec(v_lo_376_);
v___x_380_ = lean_nat_to_int(v_fin_377_);
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27(lean_object* v_hi_381_, lean_object* v_lo_382_, lean_object* v_fin_383_, lean_object* v_h_384_){
_start:
{
uint8_t v___x_385_; 
v___x_385_ = lean_nat_dec_le(v_lo_382_, v_fin_383_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
lean_dec(v_fin_383_);
v___x_386_ = lean_nat_to_int(v_lo_382_);
return v___x_386_;
}
else
{
lean_object* v___x_387_; 
lean_dec(v_lo_382_);
v___x_387_ = lean_nat_to_int(v_fin_383_);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ofFin_x27___boxed(lean_object* v_hi_388_, lean_object* v_lo_389_, lean_object* v_fin_390_, lean_object* v_h_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_Time_Internal_Bounded_LE_ofFin_x27(v_hi_388_, v_lo_389_, v_fin_390_, v_h_391_);
lean_dec(v_hi_388_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___redArg(lean_object* v_b_393_, lean_object* v_i_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = lean_int_emod(v_b_393_, v_i_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___redArg___boxed(lean_object* v_b_396_, lean_object* v_i_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Std_Time_Internal_Bounded_LE_byEmod___redArg(v_b_396_, v_i_397_);
lean_dec(v_i_397_);
lean_dec(v_b_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod(lean_object* v_b_399_, lean_object* v_i_400_, lean_object* v_hi_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = lean_int_emod(v_b_399_, v_i_400_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byEmod___boxed(lean_object* v_b_403_, lean_object* v_i_404_, lean_object* v_hi_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Std_Time_Internal_Bounded_LE_byEmod(v_b_403_, v_i_404_, v_hi_405_);
lean_dec(v_i_404_);
lean_dec(v_b_403_);
return v_res_406_;
}
}
static lean_object* _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_407_; lean_object* v_intZero_408_; 
v_natZero_407_ = lean_unsigned_to_nat(0u);
v_intZero_408_ = lean_nat_to_int(v_natZero_407_);
return v_intZero_408_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg(lean_object* v_x_409_, lean_object* v_x_410_, lean_object* v_h__1_411_, lean_object* v_h__2_412_, lean_object* v_h__3_413_, lean_object* v_h__4_414_){
_start:
{
lean_object* v_intZero_415_; uint8_t v_isNeg_416_; 
v_intZero_415_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v_isNeg_416_ = lean_int_dec_lt(v_x_409_, v_intZero_415_);
if (v_isNeg_416_ == 0)
{
lean_object* v_a_417_; uint8_t v_isNeg_418_; 
lean_dec(v_h__4_414_);
lean_dec(v_h__3_413_);
v_a_417_ = lean_nat_abs(v_x_409_);
v_isNeg_418_ = lean_int_dec_lt(v_x_410_, v_intZero_415_);
if (v_isNeg_418_ == 0)
{
lean_object* v_a_419_; lean_object* v___x_420_; 
lean_dec(v_h__2_412_);
v_a_419_ = lean_nat_abs(v_x_410_);
v___x_420_ = lean_apply_2(v_h__1_411_, v_a_417_, v_a_419_);
return v___x_420_;
}
else
{
lean_object* v_abs_421_; lean_object* v_one_422_; lean_object* v_a_423_; lean_object* v___x_424_; 
lean_dec(v_h__1_411_);
v_abs_421_ = lean_nat_abs(v_x_410_);
v_one_422_ = lean_unsigned_to_nat(1u);
v_a_423_ = lean_nat_sub(v_abs_421_, v_one_422_);
lean_dec(v_abs_421_);
v___x_424_ = lean_apply_2(v_h__2_412_, v_a_417_, v_a_423_);
return v___x_424_;
}
}
else
{
lean_object* v_abs_425_; lean_object* v_one_426_; lean_object* v_a_427_; uint8_t v_isNeg_428_; 
lean_dec(v_h__2_412_);
lean_dec(v_h__1_411_);
v_abs_425_ = lean_nat_abs(v_x_409_);
v_one_426_ = lean_unsigned_to_nat(1u);
v_a_427_ = lean_nat_sub(v_abs_425_, v_one_426_);
lean_dec(v_abs_425_);
v_isNeg_428_ = lean_int_dec_lt(v_x_410_, v_intZero_415_);
if (v_isNeg_428_ == 0)
{
lean_object* v_a_429_; lean_object* v___x_430_; 
lean_dec(v_h__4_414_);
v_a_429_ = lean_nat_abs(v_x_410_);
v___x_430_ = lean_apply_2(v_h__3_413_, v_a_427_, v_a_429_);
return v___x_430_;
}
else
{
lean_object* v_abs_431_; lean_object* v_a_432_; lean_object* v___x_433_; 
lean_dec(v_h__3_413_);
v_abs_431_ = lean_nat_abs(v_x_410_);
v_a_432_ = lean_nat_sub(v_abs_431_, v_one_426_);
lean_dec(v_abs_431_);
v___x_433_ = lean_apply_2(v_h__4_414_, v_a_427_, v_a_432_);
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___boxed(lean_object* v_x_434_, lean_object* v_x_435_, lean_object* v_h__1_436_, lean_object* v_h__2_437_, lean_object* v_h__3_438_, lean_object* v_h__4_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg(v_x_434_, v_x_435_, v_h__1_436_, v_h__2_437_, v_h__3_438_, v_h__4_439_);
lean_dec(v_x_435_);
lean_dec(v_x_434_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter(lean_object* v_motive_441_, lean_object* v_x_442_, lean_object* v_x_443_, lean_object* v_h__1_444_, lean_object* v_h__2_445_, lean_object* v_h__3_446_, lean_object* v_h__4_447_){
_start:
{
lean_object* v_intZero_448_; uint8_t v_isNeg_449_; 
v_intZero_448_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v_isNeg_449_ = lean_int_dec_lt(v_x_442_, v_intZero_448_);
if (v_isNeg_449_ == 0)
{
lean_object* v_a_450_; uint8_t v_isNeg_451_; 
lean_dec(v_h__4_447_);
lean_dec(v_h__3_446_);
v_a_450_ = lean_nat_abs(v_x_442_);
v_isNeg_451_ = lean_int_dec_lt(v_x_443_, v_intZero_448_);
if (v_isNeg_451_ == 0)
{
lean_object* v_a_452_; lean_object* v___x_453_; 
lean_dec(v_h__2_445_);
v_a_452_ = lean_nat_abs(v_x_443_);
v___x_453_ = lean_apply_2(v_h__1_444_, v_a_450_, v_a_452_);
return v___x_453_;
}
else
{
lean_object* v_abs_454_; lean_object* v_one_455_; lean_object* v_a_456_; lean_object* v___x_457_; 
lean_dec(v_h__1_444_);
v_abs_454_ = lean_nat_abs(v_x_443_);
v_one_455_ = lean_unsigned_to_nat(1u);
v_a_456_ = lean_nat_sub(v_abs_454_, v_one_455_);
lean_dec(v_abs_454_);
v___x_457_ = lean_apply_2(v_h__2_445_, v_a_450_, v_a_456_);
return v___x_457_;
}
}
else
{
lean_object* v_abs_458_; lean_object* v_one_459_; lean_object* v_a_460_; uint8_t v_isNeg_461_; 
lean_dec(v_h__2_445_);
lean_dec(v_h__1_444_);
v_abs_458_ = lean_nat_abs(v_x_442_);
v_one_459_ = lean_unsigned_to_nat(1u);
v_a_460_ = lean_nat_sub(v_abs_458_, v_one_459_);
lean_dec(v_abs_458_);
v_isNeg_461_ = lean_int_dec_lt(v_x_443_, v_intZero_448_);
if (v_isNeg_461_ == 0)
{
lean_object* v_a_462_; lean_object* v___x_463_; 
lean_dec(v_h__4_447_);
v_a_462_ = lean_nat_abs(v_x_443_);
v___x_463_ = lean_apply_2(v_h__3_446_, v_a_460_, v_a_462_);
return v___x_463_;
}
else
{
lean_object* v_abs_464_; lean_object* v_a_465_; lean_object* v___x_466_; 
lean_dec(v_h__3_446_);
v_abs_464_ = lean_nat_abs(v_x_443_);
v_a_465_ = lean_nat_sub(v_abs_464_, v_one_459_);
lean_dec(v_abs_464_);
v___x_466_ = lean_apply_2(v_h__4_447_, v_a_460_, v_a_465_);
return v___x_466_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___boxed(lean_object* v_motive_467_, lean_object* v_x_468_, lean_object* v_x_469_, lean_object* v_h__1_470_, lean_object* v_h__2_471_, lean_object* v_h__3_472_, lean_object* v_h__4_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter(v_motive_467_, v_x_468_, v_x_469_, v_h__1_470_, v_h__2_471_, v_h__3_472_, v_h__4_473_);
lean_dec(v_x_469_);
lean_dec(v_x_468_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___redArg(lean_object* v_b_475_, lean_object* v_i_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = lean_int_mod(v_b_475_, v_i_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___redArg___boxed(lean_object* v_b_478_, lean_object* v_i_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_Time_Internal_Bounded_LE_byMod___redArg(v_b_478_, v_i_479_);
lean_dec(v_i_479_);
lean_dec(v_b_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod(lean_object* v_b_481_, lean_object* v_i_482_, lean_object* v_hi_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = lean_int_mod(v_b_481_, v_i_482_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_byMod___boxed(lean_object* v_b_485_, lean_object* v_i_486_, lean_object* v_hi_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Std_Time_Internal_Bounded_LE_byMod(v_b_485_, v_i_486_, v_hi_487_);
lean_dec(v_i_486_);
lean_dec(v_b_485_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___redArg(lean_object* v_n_489_, lean_object* v_bounded_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = lean_int_sub(v_bounded_490_, v_n_489_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___redArg___boxed(lean_object* v_n_492_, lean_object* v_bounded_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Std_Time_Internal_Bounded_LE_truncate___redArg(v_n_492_, v_bounded_493_);
lean_dec(v_bounded_493_);
lean_dec(v_n_492_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate(lean_object* v_n_495_, lean_object* v_m_496_, lean_object* v_bounded_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = lean_int_sub(v_bounded_497_, v_n_495_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncate___boxed(lean_object* v_n_499_, lean_object* v_m_500_, lean_object* v_bounded_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Std_Time_Internal_Bounded_LE_truncate(v_n_499_, v_m_500_, v_bounded_501_);
lean_dec(v_bounded_501_);
lean_dec(v_m_500_);
lean_dec(v_n_499_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___redArg(lean_object* v_bounded_503_){
_start:
{
lean_inc(v_bounded_503_);
return v_bounded_503_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___redArg___boxed(lean_object* v_bounded_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Std_Time_Internal_Bounded_LE_truncateTop___redArg(v_bounded_504_);
lean_dec(v_bounded_504_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop(lean_object* v_n_506_, lean_object* v_m_507_, lean_object* v_j_508_, lean_object* v_bounded_509_, lean_object* v_h_510_){
_start:
{
lean_inc(v_bounded_509_);
return v_bounded_509_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateTop___boxed(lean_object* v_n_511_, lean_object* v_m_512_, lean_object* v_j_513_, lean_object* v_bounded_514_, lean_object* v_h_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_Time_Internal_Bounded_LE_truncateTop(v_n_511_, v_m_512_, v_j_513_, v_bounded_514_, v_h_515_);
lean_dec(v_bounded_514_);
lean_dec(v_j_513_);
lean_dec(v_m_512_);
lean_dec(v_n_511_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg(lean_object* v_bounded_517_){
_start:
{
lean_inc(v_bounded_517_);
return v_bounded_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg___boxed(lean_object* v_bounded_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg(v_bounded_518_);
lean_dec(v_bounded_518_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom(lean_object* v_n_520_, lean_object* v_m_521_, lean_object* v_j_522_, lean_object* v_bounded_523_, lean_object* v_h_524_){
_start:
{
lean_inc(v_bounded_523_);
return v_bounded_523_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_truncateBottom___boxed(lean_object* v_n_525_, lean_object* v_m_526_, lean_object* v_j_527_, lean_object* v_bounded_528_, lean_object* v_h_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Std_Time_Internal_Bounded_LE_truncateBottom(v_n_525_, v_m_526_, v_j_527_, v_bounded_528_, v_h_529_);
lean_dec(v_bounded_528_);
lean_dec(v_j_527_);
lean_dec(v_m_526_);
lean_dec(v_n_525_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___redArg(lean_object* v_bounded_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_int_neg(v_bounded_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___redArg___boxed(lean_object* v_bounded_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_Time_Internal_Bounded_LE_neg___redArg(v_bounded_533_);
lean_dec(v_bounded_533_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg(lean_object* v_n_535_, lean_object* v_m_536_, lean_object* v_bounded_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = lean_int_neg(v_bounded_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_neg___boxed(lean_object* v_n_539_, lean_object* v_m_540_, lean_object* v_bounded_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_Time_Internal_Bounded_LE_neg(v_n_539_, v_m_540_, v_bounded_541_);
lean_dec(v_bounded_541_);
lean_dec(v_m_540_);
lean_dec(v_n_539_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___redArg(lean_object* v_bounded_543_, lean_object* v_num_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = lean_int_add(v_bounded_543_, v_num_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___redArg___boxed(lean_object* v_bounded_546_, lean_object* v_num_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_Time_Internal_Bounded_LE_add___redArg(v_bounded_546_, v_num_547_);
lean_dec(v_num_547_);
lean_dec(v_bounded_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add(lean_object* v_n_549_, lean_object* v_m_550_, lean_object* v_bounded_551_, lean_object* v_num_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = lean_int_add(v_bounded_551_, v_num_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_add___boxed(lean_object* v_n_554_, lean_object* v_m_555_, lean_object* v_bounded_556_, lean_object* v_num_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Std_Time_Internal_Bounded_LE_add(v_n_554_, v_m_555_, v_bounded_556_, v_num_557_);
lean_dec(v_num_557_);
lean_dec(v_bounded_556_);
lean_dec(v_m_555_);
lean_dec(v_n_554_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___redArg(lean_object* v_num_559_, lean_object* v_bounded_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = lean_int_add(v_bounded_560_, v_num_559_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___redArg___boxed(lean_object* v_num_562_, lean_object* v_bounded_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Std_Time_Internal_Bounded_LE_addProven___redArg(v_num_562_, v_bounded_563_);
lean_dec(v_bounded_563_);
lean_dec(v_num_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven(lean_object* v_n_565_, lean_object* v_m_566_, lean_object* v_num_567_, lean_object* v_bounded_568_, lean_object* v_h_u2080_569_, lean_object* v_h_u2081_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = lean_int_add(v_bounded_568_, v_num_567_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addProven___boxed(lean_object* v_n_572_, lean_object* v_m_573_, lean_object* v_num_574_, lean_object* v_bounded_575_, lean_object* v_h_u2080_576_, lean_object* v_h_u2081_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Std_Time_Internal_Bounded_LE_addProven(v_n_572_, v_m_573_, v_num_574_, v_bounded_575_, v_h_u2080_576_, v_h_u2081_577_);
lean_dec(v_bounded_575_);
lean_dec(v_num_574_);
lean_dec(v_m_573_);
lean_dec(v_n_572_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___redArg(lean_object* v_bounded_579_, lean_object* v_num_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = lean_int_add(v_bounded_579_, v_num_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___redArg___boxed(lean_object* v_bounded_582_, lean_object* v_num_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Std_Time_Internal_Bounded_LE_addTop___redArg(v_bounded_582_, v_num_583_);
lean_dec(v_num_583_);
lean_dec(v_bounded_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop(lean_object* v_n_585_, lean_object* v_m_586_, lean_object* v_bounded_587_, lean_object* v_num_588_, lean_object* v_h_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = lean_int_add(v_bounded_587_, v_num_588_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addTop___boxed(lean_object* v_n_591_, lean_object* v_m_592_, lean_object* v_bounded_593_, lean_object* v_num_594_, lean_object* v_h_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Std_Time_Internal_Bounded_LE_addTop(v_n_591_, v_m_592_, v_bounded_593_, v_num_594_, v_h_595_);
lean_dec(v_num_594_);
lean_dec(v_bounded_593_);
lean_dec(v_m_592_);
lean_dec(v_n_591_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___redArg(lean_object* v_bounded_597_, lean_object* v_num_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = lean_int_sub(v_bounded_597_, v_num_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___redArg___boxed(lean_object* v_bounded_600_, lean_object* v_num_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_Time_Internal_Bounded_LE_subBottom___redArg(v_bounded_600_, v_num_601_);
lean_dec(v_num_601_);
lean_dec(v_bounded_600_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom(lean_object* v_n_603_, lean_object* v_m_604_, lean_object* v_bounded_605_, lean_object* v_num_606_, lean_object* v_h_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = lean_int_sub(v_bounded_605_, v_num_606_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBottom___boxed(lean_object* v_n_609_, lean_object* v_m_610_, lean_object* v_bounded_611_, lean_object* v_num_612_, lean_object* v_h_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Std_Time_Internal_Bounded_LE_subBottom(v_n_609_, v_m_610_, v_bounded_611_, v_num_612_, v_h_613_);
lean_dec(v_num_612_);
lean_dec(v_bounded_611_);
lean_dec(v_m_610_);
lean_dec(v_n_609_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___redArg(lean_object* v_bounded_615_, lean_object* v_bounded_u2082_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = lean_int_add(v_bounded_615_, v_bounded_u2082_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___redArg___boxed(lean_object* v_bounded_618_, lean_object* v_bounded_u2082_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Std_Time_Internal_Bounded_LE_addBounds___redArg(v_bounded_618_, v_bounded_u2082_619_);
lean_dec(v_bounded_u2082_619_);
lean_dec(v_bounded_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds(lean_object* v_n_621_, lean_object* v_m_622_, lean_object* v_i_623_, lean_object* v_j_624_, lean_object* v_bounded_625_, lean_object* v_bounded_u2082_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = lean_int_add(v_bounded_625_, v_bounded_u2082_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_addBounds___boxed(lean_object* v_n_628_, lean_object* v_m_629_, lean_object* v_i_630_, lean_object* v_j_631_, lean_object* v_bounded_632_, lean_object* v_bounded_u2082_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_Time_Internal_Bounded_LE_addBounds(v_n_628_, v_m_629_, v_i_630_, v_j_631_, v_bounded_632_, v_bounded_u2082_633_);
lean_dec(v_bounded_u2082_633_);
lean_dec(v_bounded_632_);
lean_dec(v_j_631_);
lean_dec(v_i_630_);
lean_dec(v_m_629_);
lean_dec(v_n_628_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___redArg(lean_object* v_bounded_635_, lean_object* v_num_636_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_int_neg(v_num_636_);
v___x_638_ = lean_int_add(v_bounded_635_, v___x_637_);
lean_dec(v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___redArg___boxed(lean_object* v_bounded_639_, lean_object* v_num_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Std_Time_Internal_Bounded_LE_sub___redArg(v_bounded_639_, v_num_640_);
lean_dec(v_num_640_);
lean_dec(v_bounded_639_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub(lean_object* v_n_642_, lean_object* v_m_643_, lean_object* v_bounded_644_, lean_object* v_num_645_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_int_neg(v_num_645_);
v___x_647_ = lean_int_add(v_bounded_644_, v___x_646_);
lean_dec(v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_sub___boxed(lean_object* v_n_648_, lean_object* v_m_649_, lean_object* v_bounded_650_, lean_object* v_num_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Std_Time_Internal_Bounded_LE_sub(v_n_648_, v_m_649_, v_bounded_650_, v_num_651_);
lean_dec(v_num_651_);
lean_dec(v_bounded_650_);
lean_dec(v_m_649_);
lean_dec(v_n_648_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___redArg(lean_object* v_bounded_653_, lean_object* v_bounded_u2082_654_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_int_neg(v_bounded_u2082_654_);
v___x_656_ = lean_int_add(v_bounded_653_, v___x_655_);
lean_dec(v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___redArg___boxed(lean_object* v_bounded_657_, lean_object* v_bounded_u2082_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_Time_Internal_Bounded_LE_subBounds___redArg(v_bounded_657_, v_bounded_u2082_658_);
lean_dec(v_bounded_u2082_658_);
lean_dec(v_bounded_657_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds(lean_object* v_n_660_, lean_object* v_m_661_, lean_object* v_i_662_, lean_object* v_j_663_, lean_object* v_bounded_664_, lean_object* v_bounded_u2082_665_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_int_neg(v_bounded_u2082_665_);
v___x_667_ = lean_int_add(v_bounded_664_, v___x_666_);
lean_dec(v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_subBounds___boxed(lean_object* v_n_668_, lean_object* v_m_669_, lean_object* v_i_670_, lean_object* v_j_671_, lean_object* v_bounded_672_, lean_object* v_bounded_u2082_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Std_Time_Internal_Bounded_LE_subBounds(v_n_668_, v_m_669_, v_i_670_, v_j_671_, v_bounded_672_, v_bounded_u2082_673_);
lean_dec(v_bounded_u2082_673_);
lean_dec(v_bounded_672_);
lean_dec(v_j_671_);
lean_dec(v_i_670_);
lean_dec(v_m_669_);
lean_dec(v_n_668_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___redArg(lean_object* v_bounded_675_, lean_object* v_num_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = lean_int_emod(v_bounded_675_, v_num_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___redArg___boxed(lean_object* v_bounded_678_, lean_object* v_num_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Std_Time_Internal_Bounded_LE_emod___redArg(v_bounded_678_, v_num_679_);
lean_dec(v_num_679_);
lean_dec(v_bounded_678_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod(lean_object* v_n_681_, lean_object* v_num_682_, lean_object* v_bounded_683_, lean_object* v_num_684_, lean_object* v_hi_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = lean_int_emod(v_bounded_683_, v_num_684_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_emod___boxed(lean_object* v_n_687_, lean_object* v_num_688_, lean_object* v_bounded_689_, lean_object* v_num_690_, lean_object* v_hi_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Std_Time_Internal_Bounded_LE_emod(v_n_687_, v_num_688_, v_bounded_689_, v_num_690_, v_hi_691_);
lean_dec(v_num_690_);
lean_dec(v_bounded_689_);
lean_dec(v_num_688_);
lean_dec(v_n_687_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___redArg(lean_object* v_bounded_693_, lean_object* v_num_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = lean_int_mod(v_bounded_693_, v_num_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___redArg___boxed(lean_object* v_bounded_696_, lean_object* v_num_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Std_Time_Internal_Bounded_LE_mod___redArg(v_bounded_696_, v_num_697_);
lean_dec(v_num_697_);
lean_dec(v_bounded_696_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod(lean_object* v_n_699_, lean_object* v_num_700_, lean_object* v_bounded_701_, lean_object* v_num_702_, lean_object* v_hi_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = lean_int_mod(v_bounded_701_, v_num_702_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mod___boxed(lean_object* v_n_705_, lean_object* v_num_706_, lean_object* v_bounded_707_, lean_object* v_num_708_, lean_object* v_hi_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Std_Time_Internal_Bounded_LE_mod(v_n_705_, v_num_706_, v_bounded_707_, v_num_708_, v_hi_709_);
lean_dec(v_num_708_);
lean_dec(v_bounded_707_);
lean_dec(v_num_706_);
lean_dec(v_n_705_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___redArg(lean_object* v_bounded_711_, lean_object* v_num_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = lean_int_mul(v_bounded_711_, v_num_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___redArg___boxed(lean_object* v_bounded_714_, lean_object* v_num_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Std_Time_Internal_Bounded_LE_mul__pos___redArg(v_bounded_714_, v_num_715_);
lean_dec(v_num_715_);
lean_dec(v_bounded_714_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos(lean_object* v_n_717_, lean_object* v_m_718_, lean_object* v_bounded_719_, lean_object* v_num_720_, lean_object* v_h_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = lean_int_mul(v_bounded_719_, v_num_720_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__pos___boxed(lean_object* v_n_723_, lean_object* v_m_724_, lean_object* v_bounded_725_, lean_object* v_num_726_, lean_object* v_h_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Std_Time_Internal_Bounded_LE_mul__pos(v_n_723_, v_m_724_, v_bounded_725_, v_num_726_, v_h_727_);
lean_dec(v_num_726_);
lean_dec(v_bounded_725_);
lean_dec(v_m_724_);
lean_dec(v_n_723_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___redArg(lean_object* v_bounded_729_, lean_object* v_num_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = lean_int_mul(v_bounded_729_, v_num_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___redArg___boxed(lean_object* v_bounded_732_, lean_object* v_num_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Std_Time_Internal_Bounded_LE_mul__neg___redArg(v_bounded_732_, v_num_733_);
lean_dec(v_num_733_);
lean_dec(v_bounded_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg(lean_object* v_n_735_, lean_object* v_m_736_, lean_object* v_bounded_737_, lean_object* v_num_738_, lean_object* v_h_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = lean_int_mul(v_bounded_737_, v_num_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_mul__neg___boxed(lean_object* v_n_741_, lean_object* v_m_742_, lean_object* v_bounded_743_, lean_object* v_num_744_, lean_object* v_h_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Std_Time_Internal_Bounded_LE_mul__neg(v_n_741_, v_m_742_, v_bounded_743_, v_num_744_, v_h_745_);
lean_dec(v_num_744_);
lean_dec(v_bounded_743_);
lean_dec(v_m_742_);
lean_dec(v_n_741_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___redArg(lean_object* v_bounded_747_, lean_object* v_num_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = lean_int_ediv(v_bounded_747_, v_num_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___redArg___boxed(lean_object* v_bounded_750_, lean_object* v_num_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Std_Time_Internal_Bounded_LE_ediv___redArg(v_bounded_750_, v_num_751_);
lean_dec(v_num_751_);
lean_dec(v_bounded_750_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv(lean_object* v_n_753_, lean_object* v_m_754_, lean_object* v_bounded_755_, lean_object* v_num_756_, lean_object* v_h_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = lean_int_ediv(v_bounded_755_, v_num_756_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_ediv___boxed(lean_object* v_n_759_, lean_object* v_m_760_, lean_object* v_bounded_761_, lean_object* v_num_762_, lean_object* v_h_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Std_Time_Internal_Bounded_LE_ediv(v_n_759_, v_m_760_, v_bounded_761_, v_num_762_, v_h_763_);
lean_dec(v_num_762_);
lean_dec(v_bounded_761_);
lean_dec(v_m_760_);
lean_dec(v_n_759_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_eq(lean_object* v_n_765_){
_start:
{
lean_inc(v_n_765_);
return v_n_765_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_eq___boxed(lean_object* v_n_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Std_Time_Internal_Bounded_LE_eq(v_n_766_);
lean_dec(v_n_766_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___redArg(lean_object* v_bounded_768_){
_start:
{
lean_inc(v_bounded_768_);
return v_bounded_768_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___redArg___boxed(lean_object* v_bounded_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Std_Time_Internal_Bounded_LE_expand___redArg(v_bounded_769_);
lean_dec(v_bounded_769_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand(lean_object* v_lo_771_, lean_object* v_hi_772_, lean_object* v_nhi_773_, lean_object* v_nlo_774_, lean_object* v_bounded_775_, lean_object* v_h_776_, lean_object* v_h_u2081_777_){
_start:
{
lean_inc(v_bounded_775_);
return v_bounded_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expand___boxed(lean_object* v_lo_778_, lean_object* v_hi_779_, lean_object* v_nhi_780_, lean_object* v_nlo_781_, lean_object* v_bounded_782_, lean_object* v_h_783_, lean_object* v_h_u2081_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Std_Time_Internal_Bounded_LE_expand(v_lo_778_, v_hi_779_, v_nhi_780_, v_nlo_781_, v_bounded_782_, v_h_783_, v_h_u2081_784_);
lean_dec(v_bounded_782_);
lean_dec(v_nlo_781_);
lean_dec(v_nhi_780_);
lean_dec(v_hi_779_);
lean_dec(v_lo_778_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___redArg(lean_object* v_bounded_786_){
_start:
{
lean_inc(v_bounded_786_);
return v_bounded_786_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___redArg___boxed(lean_object* v_bounded_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Std_Time_Internal_Bounded_LE_expandTop___redArg(v_bounded_787_);
lean_dec(v_bounded_787_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop(lean_object* v_lo_789_, lean_object* v_hi_790_, lean_object* v_nhi_791_, lean_object* v_bounded_792_, lean_object* v_h_793_){
_start:
{
lean_inc(v_bounded_792_);
return v_bounded_792_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandTop___boxed(lean_object* v_lo_794_, lean_object* v_hi_795_, lean_object* v_nhi_796_, lean_object* v_bounded_797_, lean_object* v_h_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Std_Time_Internal_Bounded_LE_expandTop(v_lo_794_, v_hi_795_, v_nhi_796_, v_bounded_797_, v_h_798_);
lean_dec(v_bounded_797_);
lean_dec(v_nhi_796_);
lean_dec(v_hi_795_);
lean_dec(v_lo_794_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___redArg(lean_object* v_bounded_800_){
_start:
{
lean_inc(v_bounded_800_);
return v_bounded_800_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___redArg___boxed(lean_object* v_bounded_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Std_Time_Internal_Bounded_LE_expandBottom___redArg(v_bounded_801_);
lean_dec(v_bounded_801_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom(lean_object* v_lo_803_, lean_object* v_hi_804_, lean_object* v_nlo_805_, lean_object* v_bounded_806_, lean_object* v_h_807_){
_start:
{
lean_inc(v_bounded_806_);
return v_bounded_806_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_expandBottom___boxed(lean_object* v_lo_808_, lean_object* v_hi_809_, lean_object* v_nlo_810_, lean_object* v_bounded_811_, lean_object* v_h_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Std_Time_Internal_Bounded_LE_expandBottom(v_lo_808_, v_hi_809_, v_nlo_810_, v_bounded_811_, v_h_812_);
lean_dec(v_bounded_811_);
lean_dec(v_nlo_810_);
lean_dec(v_hi_809_);
lean_dec(v_lo_808_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___redArg(lean_object* v_bounded_814_){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v___x_816_ = lean_int_add(v_bounded_814_, v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___redArg___boxed(lean_object* v_bounded_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Std_Time_Internal_Bounded_LE_succ___redArg(v_bounded_817_);
lean_dec(v_bounded_817_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ(lean_object* v_lo_819_, lean_object* v_hi_820_, lean_object* v_bounded_821_, lean_object* v_h_822_){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_obj_once(&l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0, &l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once, _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0);
v___x_824_ = lean_int_add(v_bounded_821_, v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_succ___boxed(lean_object* v_lo_825_, lean_object* v_hi_826_, lean_object* v_bounded_827_, lean_object* v_h_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Std_Time_Internal_Bounded_LE_succ(v_lo_825_, v_hi_826_, v_bounded_827_, v_h_828_);
lean_dec(v_bounded_827_);
lean_dec(v_hi_826_);
lean_dec(v_lo_825_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___redArg(lean_object* v_bo_830_){
_start:
{
lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_831_ = lean_obj_once(&l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v___x_832_ = lean_int_dec_le(v___x_831_, v_bo_830_);
if (v___x_832_ == 0)
{
lean_object* v_r_833_; 
v_r_833_ = lean_int_neg(v_bo_830_);
return v_r_833_;
}
else
{
lean_inc(v_bo_830_);
return v_bo_830_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___redArg___boxed(lean_object* v_bo_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Std_Time_Internal_Bounded_LE_abs___redArg(v_bo_834_);
lean_dec(v_bo_834_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs(lean_object* v_i_836_, lean_object* v_bo_837_){
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
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_abs___boxed(lean_object* v_i_841_, lean_object* v_bo_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Std_Time_Internal_Bounded_LE_abs(v_i_841_, v_bo_842_);
lean_dec(v_bo_842_);
lean_dec(v_i_841_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___redArg(lean_object* v_bounded_844_, lean_object* v_val_845_){
_start:
{
uint8_t v___x_846_; 
v___x_846_ = lean_int_dec_le(v_bounded_844_, v_val_845_);
if (v___x_846_ == 0)
{
lean_inc(v_bounded_844_);
return v_bounded_844_;
}
else
{
lean_inc(v_val_845_);
return v_val_845_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___redArg___boxed(lean_object* v_bounded_847_, lean_object* v_val_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Std_Time_Internal_Bounded_LE_max___redArg(v_bounded_847_, v_val_848_);
lean_dec(v_val_848_);
lean_dec(v_bounded_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max(lean_object* v_n_850_, lean_object* v_m_851_, lean_object* v_bounded_852_, lean_object* v_val_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Std_Time_Internal_Bounded_LE_max___redArg(v_bounded_852_, v_val_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_Bounded_LE_max___boxed(lean_object* v_n_855_, lean_object* v_m_856_, lean_object* v_bounded_857_, lean_object* v_val_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Std_Time_Internal_Bounded_LE_max(v_n_855_, v_m_856_, v_bounded_857_, v_val_858_);
lean_dec(v_val_858_);
lean_dec(v_bounded_857_);
lean_dec(v_m_856_);
lean_dec(v_n_855_);
return v_res_859_;
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
