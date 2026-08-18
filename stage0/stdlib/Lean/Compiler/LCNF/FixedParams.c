// Lean compiler output
// Module: Lean.Compiler.LCNF.FixedParams
// Imports: public import Lean.Compiler.LCNF.Basic
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_top_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_top_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_erased_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_erased_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_val_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_val_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue = (const lean_object*)&l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue = (const lean_object*)&l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FixedParams_abort___redArg___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_FixedParams_abort___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__3_value;
static const lean_closure_object l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__5_value;
static const lean_closure_object l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__6_value;
static const lean_closure_object l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__1_value),((lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__2_value)}};
static const lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__8_value),((lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__3_value),((lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__4_value),((lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__5_value),((lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__6_value)}};
static const lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__9_value),((lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__7_value)}};
static const lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalFVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalFVar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_inMutualBlock(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_inMutualBlock___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkAssignment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkAssignment___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__5(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7_spec__11(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalLetValue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalCode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalLetValue___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkInitialValues___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFixedParamsMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorIdx(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
if (lean_obj_tag(v_t_7_) == 2)
{
lean_object* v_i_9_; lean_object* v___x_10_; 
v_i_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_i_9_);
lean_dec_ref_known(v_t_7_, 1);
v___x_10_ = lean_apply_1(v_k_8_, v_i_9_);
return v___x_10_;
}
else
{
lean_dec(v_t_7_);
return v_k_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_top_elim___redArg(lean_object* v_t_23_, lean_object* v_top_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_23_, v_top_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_top_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_top_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_27_, v_top_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_erased_elim___redArg(lean_object* v_t_31_, lean_object* v_erased_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_31_, v_erased_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_erased_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_erased_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_35_, v_erased_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_val_elim___redArg(lean_object* v_t_39_, lean_object* v_val_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_39_, v_val_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_val_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_val_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_43_, v_val_45_);
return v___x_46_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue_default(void){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_box(0);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_box(0);
return v___x_48_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(lean_object* v_x_49_, lean_object* v_x_50_){
_start:
{
switch(lean_obj_tag(v_x_49_))
{
case 0:
{
if (lean_obj_tag(v_x_50_) == 0)
{
uint8_t v___x_51_; 
v___x_51_ = 1;
return v___x_51_;
}
else
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
}
case 1:
{
if (lean_obj_tag(v_x_50_) == 1)
{
uint8_t v___x_53_; 
v___x_53_ = 1;
return v___x_53_;
}
else
{
uint8_t v___x_54_; 
v___x_54_ = 0;
return v___x_54_;
}
}
default: 
{
if (lean_obj_tag(v_x_50_) == 2)
{
lean_object* v_i_55_; lean_object* v_i_56_; uint8_t v___x_57_; 
v_i_55_ = lean_ctor_get(v_x_49_, 0);
v_i_56_ = lean_ctor_get(v_x_50_, 0);
v___x_57_ = lean_nat_dec_eq(v_i_55_, v_i_56_);
return v___x_57_;
}
else
{
uint8_t v___x_58_; 
v___x_58_ = 0;
return v___x_58_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq___boxed(lean_object* v_x_59_, lean_object* v_x_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v_x_59_, v_x_60_);
lean_dec(v_x_60_);
lean_dec(v_x_59_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash(lean_object* v_x_65_){
_start:
{
switch(lean_obj_tag(v_x_65_))
{
case 0:
{
uint64_t v___x_66_; 
v___x_66_ = 0ULL;
return v___x_66_;
}
case 1:
{
uint64_t v___x_67_; 
v___x_67_ = 1ULL;
return v___x_67_;
}
default: 
{
lean_object* v_i_68_; uint64_t v___x_69_; uint64_t v___x_70_; uint64_t v___x_71_; 
v_i_68_ = lean_ctor_get(v_x_65_, 0);
v___x_69_ = 2ULL;
v___x_70_ = lean_uint64_of_nat(v_i_68_);
v___x_71_ = lean_uint64_mix_hash(v___x_69_, v___x_70_);
return v___x_71_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash___boxed(lean_object* v_x_72_){
_start:
{
uint64_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash(v_x_72_);
lean_dec(v_x_72_);
v_r_74_ = lean_box_uint64(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FixedParams_abort___redArg___lam__0(uint8_t v_x_77_){
_start:
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___redArg___lam__0___boxed(lean_object* v_x_79_){
_start:
{
uint8_t v_x_273__boxed_80_; uint8_t v_res_81_; lean_object* v_r_82_; 
v_x_273__boxed_80_ = lean_unbox(v_x_79_);
v_res_81_ = l_Lean_Compiler_LCNF_FixedParams_abort___redArg___lam__0(v_x_273__boxed_80_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___redArg(lean_object* v_a_103_){
_start:
{
lean_object* v_visited_104_; lean_object* v_fixed_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_119_; 
v_visited_104_ = lean_ctor_get(v_a_103_, 0);
v_fixed_105_ = lean_ctor_get(v_a_103_, 1);
v_isSharedCheck_119_ = !lean_is_exclusive(v_a_103_);
if (v_isSharedCheck_119_ == 0)
{
v___x_107_ = v_a_103_;
v_isShared_108_ = v_isSharedCheck_119_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_fixed_105_);
lean_inc(v_visited_104_);
lean_dec(v_a_103_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_119_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___f_109_; lean_object* v___x_110_; size_t v_sz_111_; size_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_115_; 
v___f_109_ = ((lean_object*)(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__0));
v___x_110_ = ((lean_object*)(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__10));
v_sz_111_ = lean_array_size(v_fixed_105_);
v___x_112_ = ((size_t)0ULL);
v___x_113_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_110_, v___f_109_, v_sz_111_, v___x_112_, v_fixed_105_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 1, v___x_113_);
v___x_115_ = v___x_107_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_visited_104_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v___x_113_);
v___x_115_ = v_reuseFailAlloc_118_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_box(0);
v___x_117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___x_115_);
return v___x_117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort(lean_object* v_00_u03b1_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v_visited_123_; lean_object* v_fixed_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_138_; 
v_visited_123_ = lean_ctor_get(v_a_122_, 0);
v_fixed_124_ = lean_ctor_get(v_a_122_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v_a_122_);
if (v_isSharedCheck_138_ == 0)
{
v___x_126_ = v_a_122_;
v_isShared_127_ = v_isSharedCheck_138_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_fixed_124_);
lean_inc(v_visited_123_);
lean_dec(v_a_122_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_138_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___f_128_; lean_object* v___x_129_; size_t v_sz_130_; size_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v___f_128_ = ((lean_object*)(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__0));
v___x_129_ = ((lean_object*)(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__10));
v_sz_130_ = lean_array_size(v_fixed_124_);
v___x_131_ = ((size_t)0ULL);
v___x_132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_129_, v___f_128_, v_sz_130_, v___x_131_, v_fixed_124_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v___x_132_);
v___x_134_ = v___x_126_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_visited_123_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v___x_132_);
v___x_134_ = v_reuseFailAlloc_137_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_box(0);
v___x_136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___x_134_);
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___boxed(lean_object* v_00_u03b1_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_Compiler_LCNF_FixedParams_abort(v_00_u03b1_139_, v_a_140_, v_a_141_);
lean_dec_ref(v_a_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(lean_object* v_t_143_, lean_object* v_k_144_){
_start:
{
if (lean_obj_tag(v_t_143_) == 0)
{
lean_object* v_k_145_; lean_object* v_v_146_; lean_object* v_l_147_; lean_object* v_r_148_; uint8_t v___x_149_; 
v_k_145_ = lean_ctor_get(v_t_143_, 1);
v_v_146_ = lean_ctor_get(v_t_143_, 2);
v_l_147_ = lean_ctor_get(v_t_143_, 3);
v_r_148_ = lean_ctor_get(v_t_143_, 4);
v___x_149_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_144_, v_k_145_);
switch(v___x_149_)
{
case 0:
{
v_t_143_ = v_l_147_;
goto _start;
}
case 1:
{
lean_object* v___x_151_; 
lean_inc(v_v_146_);
v___x_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_151_, 0, v_v_146_);
return v___x_151_;
}
default: 
{
v_t_143_ = v_r_148_;
goto _start;
}
}
}
else
{
lean_object* v___x_153_; 
v___x_153_ = lean_box(0);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg___boxed(lean_object* v_t_154_, lean_object* v_k_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(v_t_154_, v_k_155_);
lean_dec(v_k_155_);
lean_dec(v_t_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalFVar(lean_object* v_fvarId_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_assignment_160_; lean_object* v___x_161_; 
v_assignment_160_ = lean_ctor_get(v_a_158_, 2);
v___x_161_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(v_assignment_160_, v_fvarId_157_);
if (lean_obj_tag(v___x_161_) == 1)
{
lean_object* v_val_162_; lean_object* v___x_163_; 
v_val_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_val_162_);
lean_dec_ref_known(v___x_161_, 1);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v_val_162_);
lean_ctor_set(v___x_163_, 1, v_a_159_);
return v___x_163_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v_a_159_);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalFVar___boxed(lean_object* v_fvarId_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Compiler_LCNF_FixedParams_evalFVar(v_fvarId_166_, v_a_167_, v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec(v_fvarId_166_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0(lean_object* v_00_u03b4_170_, lean_object* v_t_171_, lean_object* v_k_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(v_t_171_, v_k_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___boxed(lean_object* v_00_u03b4_174_, lean_object* v_t_175_, lean_object* v_k_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0(v_00_u03b4_174_, v_t_175_, v_k_176_);
lean_dec(v_k_176_);
lean_dec(v_t_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalArg(lean_object* v_arg_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
switch(lean_obj_tag(v_arg_178_))
{
case 0:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_box(1);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_a_180_);
return v___x_182_;
}
case 1:
{
lean_object* v_fvarId_183_; lean_object* v___x_184_; 
v_fvarId_183_ = lean_ctor_get(v_arg_178_, 0);
v___x_184_ = l_Lean_Compiler_LCNF_FixedParams_evalFVar(v_fvarId_183_, v_a_179_, v_a_180_);
return v___x_184_;
}
default: 
{
lean_object* v_expr_185_; 
v_expr_185_ = lean_ctor_get(v_arg_178_, 0);
if (lean_obj_tag(v_expr_185_) == 1)
{
lean_object* v_fvarId_186_; lean_object* v___x_187_; 
v_fvarId_186_ = lean_ctor_get(v_expr_185_, 0);
v___x_187_ = l_Lean_Compiler_LCNF_FixedParams_evalFVar(v_fvarId_186_, v_a_179_, v_a_180_);
return v___x_187_;
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_box(0);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_a_180_);
return v___x_189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalArg___boxed(lean_object* v_arg_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Compiler_LCNF_FixedParams_evalArg(v_arg_190_, v_a_191_, v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec(v_arg_190_);
return v_res_193_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0(lean_object* v_declName_194_, lean_object* v_as_195_, size_t v_i_196_, size_t v_stop_197_){
_start:
{
uint8_t v___x_198_; 
v___x_198_ = lean_usize_dec_eq(v_i_196_, v_stop_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v_toSignature_200_; lean_object* v_name_201_; uint8_t v___x_202_; 
v___x_199_ = lean_array_uget_borrowed(v_as_195_, v_i_196_);
v_toSignature_200_ = lean_ctor_get(v___x_199_, 0);
v_name_201_ = lean_ctor_get(v_toSignature_200_, 0);
v___x_202_ = lean_name_eq(v_name_201_, v_declName_194_);
if (v___x_202_ == 0)
{
size_t v___x_203_; size_t v___x_204_; 
v___x_203_ = ((size_t)1ULL);
v___x_204_ = lean_usize_add(v_i_196_, v___x_203_);
v_i_196_ = v___x_204_;
goto _start;
}
else
{
return v___x_202_;
}
}
else
{
uint8_t v___x_206_; 
v___x_206_ = 0;
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0___boxed(lean_object* v_declName_207_, lean_object* v_as_208_, lean_object* v_i_209_, lean_object* v_stop_210_){
_start:
{
size_t v_i_boxed_211_; size_t v_stop_boxed_212_; uint8_t v_res_213_; lean_object* v_r_214_; 
v_i_boxed_211_ = lean_unbox_usize(v_i_209_);
lean_dec(v_i_209_);
v_stop_boxed_212_ = lean_unbox_usize(v_stop_210_);
lean_dec(v_stop_210_);
v_res_213_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0(v_declName_207_, v_as_208_, v_i_boxed_211_, v_stop_boxed_212_);
lean_dec_ref(v_as_208_);
lean_dec(v_declName_207_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_inMutualBlock(lean_object* v_declName_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_decls_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v_decls_218_ = lean_ctor_get(v_a_216_, 0);
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_array_get_size(v_decls_218_);
v___x_221_ = lean_nat_dec_lt(v___x_219_, v___x_220_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_box(v___x_221_);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v_a_217_);
return v___x_223_;
}
else
{
if (v___x_221_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_box(v___x_221_);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v_a_217_);
return v___x_225_;
}
else
{
size_t v___x_226_; size_t v___x_227_; uint8_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_226_ = ((size_t)0ULL);
v___x_227_ = lean_usize_of_nat(v___x_220_);
v___x_228_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0(v_declName_215_, v_decls_218_, v___x_226_, v___x_227_);
v___x_229_ = lean_box(v___x_228_);
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v_a_217_);
return v___x_230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_inMutualBlock___boxed(lean_object* v_declName_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_Compiler_LCNF_FixedParams_inMutualBlock(v_declName_231_, v_a_232_, v_a_233_);
lean_dec_ref(v_a_232_);
lean_dec(v_declName_231_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0(lean_object* v_as_235_, size_t v_sz_236_, size_t v_i_237_, lean_object* v_b_238_){
_start:
{
uint8_t v___x_239_; 
v___x_239_ = lean_usize_dec_lt(v_i_237_, v_sz_236_);
if (v___x_239_ == 0)
{
return v_b_238_;
}
else
{
lean_object* v_snd_240_; lean_object* v_fst_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_274_; 
v_snd_240_ = lean_ctor_get(v_b_238_, 1);
v_fst_241_ = lean_ctor_get(v_b_238_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v_b_238_);
if (v_isSharedCheck_274_ == 0)
{
v___x_243_ = v_b_238_;
v_isShared_244_ = v_isSharedCheck_274_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_snd_240_);
lean_inc(v_fst_241_);
lean_dec(v_b_238_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_274_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v_array_245_; lean_object* v_start_246_; lean_object* v_stop_247_; uint8_t v___x_248_; 
v_array_245_ = lean_ctor_get(v_snd_240_, 0);
v_start_246_ = lean_ctor_get(v_snd_240_, 1);
v_stop_247_ = lean_ctor_get(v_snd_240_, 2);
v___x_248_ = lean_nat_dec_lt(v_start_246_, v_stop_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_250_; 
if (v_isShared_244_ == 0)
{
v___x_250_ = v___x_243_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_fst_241_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_snd_240_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
else
{
lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_270_; 
lean_inc(v_stop_247_);
lean_inc(v_start_246_);
lean_inc_ref(v_array_245_);
v_isSharedCheck_270_ = !lean_is_exclusive(v_snd_240_);
if (v_isSharedCheck_270_ == 0)
{
lean_object* v_unused_271_; lean_object* v_unused_272_; lean_object* v_unused_273_; 
v_unused_271_ = lean_ctor_get(v_snd_240_, 2);
lean_dec(v_unused_271_);
v_unused_272_ = lean_ctor_get(v_snd_240_, 1);
lean_dec(v_unused_272_);
v_unused_273_ = lean_ctor_get(v_snd_240_, 0);
lean_dec(v_unused_273_);
v___x_253_ = v_snd_240_;
v_isShared_254_ = v_isSharedCheck_270_;
goto v_resetjp_252_;
}
else
{
lean_dec(v_snd_240_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_270_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v_a_255_; lean_object* v_fvarId_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
v_a_255_ = lean_array_uget_borrowed(v_as_235_, v_i_237_);
v_fvarId_256_ = lean_ctor_get(v_a_255_, 0);
v___x_257_ = lean_array_fget(v_array_245_, v_start_246_);
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = lean_nat_add(v_start_246_, v___x_258_);
lean_dec(v_start_246_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 1, v___x_259_);
v___x_261_ = v___x_253_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_array_245_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v_stop_247_);
v___x_261_ = v_reuseFailAlloc_269_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
lean_inc(v_fvarId_256_);
v___x_262_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_256_, v___x_257_, v_fst_241_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 1, v___x_261_);
lean_ctor_set(v___x_243_, 0, v___x_262_);
v___x_264_ = v___x_243_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___x_261_);
v___x_264_ = v_reuseFailAlloc_268_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
size_t v___x_265_; size_t v___x_266_; 
v___x_265_ = ((size_t)1ULL);
v___x_266_ = lean_usize_add(v_i_237_, v___x_265_);
v_i_237_ = v___x_266_;
v_b_238_ = v___x_264_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0___boxed(lean_object* v_as_275_, lean_object* v_sz_276_, lean_object* v_i_277_, lean_object* v_b_278_){
_start:
{
size_t v_sz_boxed_279_; size_t v_i_boxed_280_; lean_object* v_res_281_; 
v_sz_boxed_279_ = lean_unbox_usize(v_sz_276_);
lean_dec(v_sz_276_);
v_i_boxed_280_ = lean_unbox_usize(v_i_277_);
lean_dec(v_i_277_);
v_res_281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0(v_as_275_, v_sz_boxed_279_, v_i_boxed_280_, v_b_278_);
lean_dec_ref(v_as_275_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkAssignment(lean_object* v_decl_282_, lean_object* v_values_283_){
_start:
{
lean_object* v_toSignature_284_; lean_object* v_params_285_; lean_object* v___x_286_; lean_object* v_assignment_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; size_t v_sz_291_; size_t v___x_292_; lean_object* v___x_293_; lean_object* v_fst_294_; 
v_toSignature_284_ = lean_ctor_get(v_decl_282_, 0);
v_params_285_ = lean_ctor_get(v_toSignature_284_, 3);
v___x_286_ = lean_array_get_size(v_values_283_);
v_assignment_287_ = lean_box(1);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = l_Array_toSubarray___redArg(v_values_283_, v___x_288_, v___x_286_);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v_assignment_287_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v_sz_291_ = lean_array_size(v_params_285_);
v___x_292_ = ((size_t)0ULL);
v___x_293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0(v_params_285_, v_sz_291_, v___x_292_, v___x_290_);
v_fst_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_fst_294_);
lean_dec_ref(v___x_293_);
return v_fst_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkAssignment___boxed(lean_object* v_decl_295_, lean_object* v_values_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(v_decl_295_, v_values_296_);
lean_dec_ref(v_decl_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(lean_object* v_params_306_, lean_object* v_args_307_, uint8_t v___x_308_, lean_object* v_range_309_, lean_object* v_b_310_, lean_object* v_i_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_stop_313_; lean_object* v_step_314_; uint8_t v___x_315_; 
v_stop_313_ = lean_ctor_get(v_range_309_, 1);
v_step_314_ = lean_ctor_get(v_range_309_, 2);
v___x_315_ = lean_nat_dec_lt(v_i_311_, v_stop_313_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
lean_dec(v_i_311_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v_b_310_);
lean_ctor_set(v___x_316_, 1, v___y_312_);
return v___x_316_;
}
else
{
lean_object* v___x_317_; lean_object* v_fvarId_318_; lean_object* v___x_319_; lean_object* v_a_321_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
lean_dec_ref(v_b_310_);
v___x_317_ = lean_array_fget_borrowed(v_params_306_, v_i_311_);
v_fvarId_318_ = lean_ctor_get(v___x_317_, 0);
v___x_319_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__0));
v___x_324_ = lean_box(0);
v___x_325_ = lean_array_get_borrowed(v___x_324_, v_args_307_, v_i_311_);
lean_inc(v_fvarId_318_);
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v_fvarId_318_);
v___x_327_ = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(v___x_325_, v___x_326_);
lean_dec_ref_known(v___x_326_, 1);
if (v___x_327_ == 0)
{
if (v___x_308_ == 0)
{
v_a_321_ = v___y_312_;
goto v___jp_320_;
}
else
{
uint8_t v___x_328_; 
v___x_328_ = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(v___x_325_, v___x_324_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec(v_i_311_);
v___x_329_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__2));
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___y_312_);
return v___x_330_;
}
else
{
v_a_321_ = v___y_312_;
goto v___jp_320_;
}
}
}
else
{
v_a_321_ = v___y_312_;
goto v___jp_320_;
}
v___jp_320_:
{
lean_object* v___x_322_; 
v___x_322_ = lean_nat_add(v_i_311_, v_step_314_);
lean_dec(v_i_311_);
v_b_310_ = v___x_319_;
v_i_311_ = v___x_322_;
v___y_312_ = v_a_321_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___boxed(lean_object* v_params_331_, lean_object* v_args_332_, lean_object* v___x_333_, lean_object* v_range_334_, lean_object* v_b_335_, lean_object* v_i_336_, lean_object* v___y_337_){
_start:
{
uint8_t v___x_3934__boxed_338_; lean_object* v_res_339_; 
v___x_3934__boxed_338_ = lean_unbox(v___x_333_);
v_res_339_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_331_, v_args_332_, v___x_3934__boxed_338_, v_range_334_, v_b_335_, v_i_336_, v___y_337_);
lean_dec_ref(v_range_334_);
lean_dec_ref(v_args_332_);
lean_dec_ref(v_params_331_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(lean_object* v_decl_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v___y_344_; lean_object* v___y_348_; lean_object* v_value_351_; 
v_value_351_ = lean_ctor_get(v_decl_340_, 4);
lean_inc_ref(v_value_351_);
if (lean_obj_tag(v_value_351_) == 0)
{
lean_object* v_decl_352_; lean_object* v_value_353_; 
v_decl_352_ = lean_ctor_get(v_value_351_, 0);
lean_inc_ref(v_decl_352_);
v_value_353_ = lean_ctor_get(v_decl_352_, 3);
lean_inc(v_value_353_);
if (lean_obj_tag(v_value_353_) == 4)
{
lean_object* v_params_354_; lean_object* v_k_355_; lean_object* v_fvarId_356_; lean_object* v_fvarId_357_; lean_object* v_args_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_416_; 
v_params_354_ = lean_ctor_get(v_decl_340_, 2);
lean_inc_ref(v_params_354_);
lean_dec_ref(v_decl_340_);
v_k_355_ = lean_ctor_get(v_value_351_, 1);
lean_inc_ref(v_k_355_);
lean_dec_ref_known(v_value_351_, 2);
v_fvarId_356_ = lean_ctor_get(v_decl_352_, 0);
lean_inc(v_fvarId_356_);
lean_dec_ref(v_decl_352_);
v_fvarId_357_ = lean_ctor_get(v_value_353_, 0);
v_args_358_ = lean_ctor_get(v_value_353_, 1);
v_isSharedCheck_416_ = !lean_is_exclusive(v_value_353_);
if (v_isSharedCheck_416_ == 0)
{
v___x_360_ = v_value_353_;
v_isShared_361_ = v_isSharedCheck_416_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_args_358_);
lean_inc(v_fvarId_357_);
lean_dec(v_value_353_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_416_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_362_ = lean_array_get_size(v_args_358_);
v___x_363_ = lean_array_get_size(v_params_354_);
v___x_364_ = lean_nat_dec_eq(v___x_362_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_367_; 
lean_dec_ref(v_args_358_);
lean_dec(v_fvarId_357_);
lean_dec(v_fvarId_356_);
lean_dec_ref(v_k_355_);
lean_dec_ref(v_params_354_);
v___x_365_ = lean_box(0);
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 0);
lean_ctor_set(v___x_360_, 1, v_a_342_);
lean_ctor_set(v___x_360_, 0, v___x_365_);
v___x_367_ = v___x_360_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_a_342_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
else
{
if (lean_obj_tag(v_k_355_) == 5)
{
lean_object* v_fvarId_369_; uint8_t v___x_370_; 
v_fvarId_369_ = lean_ctor_get(v_k_355_, 0);
lean_inc(v_fvarId_369_);
lean_dec_ref_known(v_k_355_, 1);
v___x_370_ = l_Lean_instBEqFVarId_beq(v_fvarId_369_, v_fvarId_356_);
lean_dec(v_fvarId_356_);
lean_dec(v_fvarId_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_373_; 
lean_dec_ref(v_args_358_);
lean_dec(v_fvarId_357_);
lean_dec_ref(v_params_354_);
v___x_371_ = lean_box(0);
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 0);
lean_ctor_set(v___x_360_, 1, v_a_342_);
lean_ctor_set(v___x_360_, 0, v___x_371_);
v___x_373_ = v___x_360_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_a_342_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
else
{
lean_object* v_assignment_375_; lean_object* v___x_376_; 
lean_del_object(v___x_360_);
v_assignment_375_ = lean_ctor_get(v_a_341_, 2);
v___x_376_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(v_assignment_375_, v_fvarId_357_);
lean_dec(v_fvarId_357_);
if (lean_obj_tag(v___x_376_) == 1)
{
lean_object* v_val_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_411_; 
v_val_377_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_411_ == 0)
{
v___x_379_ = v___x_376_;
v_isShared_380_ = v_isSharedCheck_411_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_val_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_411_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
if (lean_obj_tag(v_val_377_) == 2)
{
lean_object* v_i_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v_a_387_; lean_object* v_fst_388_; 
v_i_381_ = lean_ctor_get(v_val_377_, 0);
lean_inc(v_i_381_);
lean_dec_ref_known(v_val_377_, 1);
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = lean_unsigned_to_nat(1u);
v___x_384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v___x_363_);
lean_ctor_set(v___x_384_, 2, v___x_383_);
v___x_385_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__0));
v___x_386_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_354_, v_args_358_, v___x_370_, v___x_384_, v___x_385_, v___x_382_, v_a_342_);
lean_dec_ref_known(v___x_384_, 3);
lean_dec_ref(v_args_358_);
lean_dec_ref(v_params_354_);
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
v_fst_388_ = lean_ctor_get(v_a_387_, 0);
lean_inc(v_fst_388_);
lean_dec(v_a_387_);
if (lean_obj_tag(v_fst_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_399_; 
v_a_389_ = lean_ctor_get(v___x_386_, 1);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; 
v_unused_400_ = lean_ctor_get(v___x_386_, 0);
lean_dec(v_unused_400_);
v___x_391_ = v___x_386_;
v_isShared_392_ = v_isSharedCheck_399_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_386_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_399_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v_i_381_);
v___x_394_ = v___x_379_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_i_381_);
v___x_394_ = v_reuseFailAlloc_398_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; 
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_394_);
v___x_396_ = v___x_391_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_a_389_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_409_; 
lean_dec(v_i_381_);
lean_del_object(v___x_379_);
v_a_401_ = lean_ctor_get(v___x_386_, 1);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v___x_386_, 0);
lean_dec(v_unused_410_);
v___x_403_ = v___x_386_;
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_386_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_val_405_; lean_object* v___x_407_; 
v_val_405_ = lean_ctor_get(v_fst_388_, 0);
lean_inc(v_val_405_);
lean_dec_ref_known(v_fst_388_, 1);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v_val_405_);
v___x_407_ = v___x_403_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_val_405_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_a_401_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
else
{
lean_del_object(v___x_379_);
lean_dec(v_val_377_);
lean_dec_ref(v_args_358_);
lean_dec_ref(v_params_354_);
v___y_348_ = v_a_342_;
goto v___jp_347_;
}
}
}
else
{
lean_dec(v___x_376_);
lean_dec_ref(v_args_358_);
lean_dec_ref(v_params_354_);
v___y_348_ = v_a_342_;
goto v___jp_347_;
}
}
}
else
{
lean_object* v___x_412_; lean_object* v___x_414_; 
lean_dec_ref(v_args_358_);
lean_dec(v_fvarId_357_);
lean_dec(v_fvarId_356_);
lean_dec_ref(v_k_355_);
lean_dec_ref(v_params_354_);
v___x_412_ = lean_box(0);
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 0);
lean_ctor_set(v___x_360_, 1, v_a_342_);
lean_ctor_set(v___x_360_, 0, v___x_412_);
v___x_414_ = v___x_360_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_a_342_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
else
{
lean_dec(v_value_353_);
lean_dec_ref(v_decl_352_);
lean_dec_ref_known(v_value_351_, 2);
lean_dec_ref(v_decl_340_);
v___y_344_ = v_a_342_;
goto v___jp_343_;
}
}
else
{
lean_dec_ref(v_value_351_);
lean_dec_ref(v_decl_340_);
v___y_344_ = v_a_342_;
goto v___jp_343_;
}
v___jp_343_:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_box(0);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___y_344_);
return v___x_346_;
}
v___jp_347_:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_box(0);
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___y_348_);
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f___boxed(lean_object* v_decl_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(v_decl_417_, v_a_418_, v_a_419_);
lean_dec_ref(v_a_418_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0(lean_object* v_params_421_, lean_object* v_args_422_, uint8_t v___x_423_, lean_object* v_range_424_, lean_object* v_b_425_, lean_object* v_i_426_, lean_object* v_hs_427_, lean_object* v_hl_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_421_, v_args_422_, v___x_423_, v_range_424_, v_b_425_, v_i_426_, v___y_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___boxed(lean_object* v_params_432_, lean_object* v_args_433_, lean_object* v___x_434_, lean_object* v_range_435_, lean_object* v_b_436_, lean_object* v_i_437_, lean_object* v_hs_438_, lean_object* v_hl_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
uint8_t v___x_4138__boxed_442_; lean_object* v_res_443_; 
v___x_4138__boxed_442_ = lean_unbox(v___x_434_);
v_res_443_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0(v_params_432_, v_args_433_, v___x_4138__boxed_442_, v_range_435_, v_b_436_, v_i_437_, v_hs_438_, v_hl_439_, v___y_440_, v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec_ref(v_range_435_);
lean_dec_ref(v_args_433_);
lean_dec_ref(v_params_432_);
return v_res_443_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4_spec__6___redArg(lean_object* v_xs_444_, lean_object* v_ys_445_, lean_object* v_x_446_){
_start:
{
lean_object* v_zero_447_; uint8_t v_isZero_448_; 
v_zero_447_ = lean_unsigned_to_nat(0u);
v_isZero_448_ = lean_nat_dec_eq(v_x_446_, v_zero_447_);
if (v_isZero_448_ == 1)
{
lean_dec(v_x_446_);
return v_isZero_448_;
}
else
{
lean_object* v_one_449_; lean_object* v_n_450_; lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v_one_449_ = lean_unsigned_to_nat(1u);
v_n_450_ = lean_nat_sub(v_x_446_, v_one_449_);
lean_dec(v_x_446_);
v___x_451_ = lean_array_fget_borrowed(v_xs_444_, v_n_450_);
v___x_452_ = lean_array_fget_borrowed(v_ys_445_, v_n_450_);
v___x_453_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_dec(v_n_450_);
return v___x_453_;
}
else
{
v_x_446_ = v_n_450_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_xs_455_, lean_object* v_ys_456_, lean_object* v_x_457_){
_start:
{
uint8_t v_res_458_; lean_object* v_r_459_; 
v_res_458_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4_spec__6___redArg(v_xs_455_, v_ys_456_, v_x_457_);
lean_dec_ref(v_ys_456_);
lean_dec_ref(v_xs_455_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4___redArg(lean_object* v_m_460_, lean_object* v_query_461_, lean_object* v_x_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
lean_object* v_zero_465_; uint8_t v_isZero_466_; 
v_zero_465_ = lean_unsigned_to_nat(0u);
v_isZero_466_ = lean_nat_dec_eq(v_x_463_, v_zero_465_);
if (v_isZero_466_ == 1)
{
lean_dec(v_x_464_);
lean_dec(v_x_463_);
if (lean_obj_tag(v_x_462_) == 0)
{
lean_object* v___x_467_; 
v___x_467_ = lean_box(2);
return v___x_467_;
}
else
{
lean_object* v_val_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
v_val_468_ = lean_ctor_get(v_x_462_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v_x_462_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v_x_462_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_val_468_);
lean_dec(v_x_462_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_val_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
lean_object* v_keyArray_476_; lean_object* v_valueArray_477_; lean_object* v___x_478_; uint8_t v_isSome_479_; 
v_keyArray_476_ = lean_ctor_get(v_m_460_, 1);
v_valueArray_477_ = lean_ctor_get(v_m_460_, 2);
v___x_478_ = lean_array_fget_borrowed(v_keyArray_476_, v_x_464_);
v_isSome_479_ = lean_noption_is_some(v___x_478_);
if (v_isSome_479_ == 0)
{
lean_dec(v_x_463_);
if (lean_obj_tag(v_x_462_) == 0)
{
lean_object* v___x_480_; 
v___x_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_480_, 0, v_x_464_);
return v___x_480_;
}
else
{
lean_object* v_val_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec(v_x_464_);
v_val_481_ = lean_ctor_get(v_x_462_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v_x_462_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v_x_462_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_val_481_);
lean_dec(v_x_462_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_val_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
else
{
lean_object* v_one_489_; lean_object* v_n_490_; lean_object* v___y_492_; 
v_one_489_ = lean_unsigned_to_nat(1u);
v_n_490_ = lean_nat_sub(v_x_463_, v_one_489_);
lean_dec(v_x_463_);
if (v_isSome_479_ == 0)
{
goto v___jp_498_;
}
else
{
lean_object* v___x_506_; uint8_t v_isSome_507_; 
v___x_506_ = lean_array_fget_borrowed(v_valueArray_477_, v_x_464_);
v_isSome_507_ = lean_noption_is_some(v___x_506_);
if (v_isSome_507_ == 0)
{
goto v___jp_498_;
}
else
{
lean_object* v_val_508_; lean_object* v_fst_509_; lean_object* v_snd_510_; lean_object* v_fst_511_; lean_object* v_snd_512_; lean_object* v_val_513_; uint8_t v___y_515_; uint8_t v___x_517_; 
lean_inc(v___x_478_);
v_val_508_ = lean_noption_get(v___x_478_);
v_fst_509_ = lean_ctor_get(v_val_508_, 0);
lean_inc(v_fst_509_);
v_snd_510_ = lean_ctor_get(v_val_508_, 1);
lean_inc(v_snd_510_);
v_fst_511_ = lean_ctor_get(v_query_461_, 0);
v_snd_512_ = lean_ctor_get(v_query_461_, 1);
lean_inc(v___x_506_);
v_val_513_ = lean_noption_get(v___x_506_);
v___x_517_ = lean_name_eq(v_fst_509_, v_fst_511_);
lean_dec(v_fst_509_);
if (v___x_517_ == 0)
{
lean_dec(v_snd_510_);
v___y_515_ = v___x_517_;
goto v___jp_514_;
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_518_ = lean_array_get_size(v_snd_510_);
v___x_519_ = lean_array_get_size(v_snd_512_);
v___x_520_ = lean_nat_dec_eq(v___x_518_, v___x_519_);
if (v___x_520_ == 0)
{
lean_dec(v_val_513_);
lean_dec(v_snd_510_);
lean_dec(v_val_508_);
goto v___jp_500_;
}
else
{
uint8_t v___x_521_; 
v___x_521_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4_spec__6___redArg(v_snd_510_, v_snd_512_, v___x_518_);
lean_dec(v_snd_510_);
v___y_515_ = v___x_521_;
goto v___jp_514_;
}
}
v___jp_514_:
{
if (v___y_515_ == 0)
{
lean_dec(v_val_513_);
lean_dec(v_val_508_);
goto v___jp_500_;
}
else
{
lean_object* v___x_516_; 
lean_dec(v_n_490_);
lean_dec(v_x_462_);
v___x_516_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_516_, 0, v_x_464_);
lean_ctor_set(v___x_516_, 1, v_val_508_);
lean_ctor_set(v___x_516_, 2, v_val_513_);
return v___x_516_;
}
}
}
}
v___jp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_493_ = lean_array_get_size(v_keyArray_476_);
v___x_494_ = lean_nat_add(v_x_464_, v_one_489_);
lean_dec(v_x_464_);
v___x_495_ = lean_nat_dec_lt(v___x_494_, v___x_493_);
if (v___x_495_ == 0)
{
lean_dec(v___x_494_);
v_x_462_ = v___y_492_;
v_x_463_ = v_n_490_;
v_x_464_ = v_zero_465_;
goto _start;
}
else
{
v_x_462_ = v___y_492_;
v_x_463_ = v_n_490_;
v_x_464_ = v___x_494_;
goto _start;
}
}
v___jp_498_:
{
if (lean_obj_tag(v_x_462_) == 0)
{
lean_object* v___x_499_; 
lean_inc(v_x_464_);
v___x_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_499_, 0, v_x_464_);
v___y_492_ = v___x_499_;
goto v___jp_491_;
}
else
{
v___y_492_ = v_x_462_;
goto v___jp_491_;
}
}
v___jp_500_:
{
lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_501_ = lean_array_get_size(v_keyArray_476_);
v___x_502_ = lean_nat_add(v_x_464_, v_one_489_);
lean_dec(v_x_464_);
v___x_503_ = lean_nat_dec_lt(v___x_502_, v___x_501_);
if (v___x_503_ == 0)
{
lean_dec(v___x_502_);
v_x_463_ = v_n_490_;
v_x_464_ = v_zero_465_;
goto _start;
}
else
{
v_x_463_ = v_n_490_;
v_x_464_ = v___x_502_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4___redArg___boxed(lean_object* v_m_522_, lean_object* v_query_523_, lean_object* v_x_524_, lean_object* v_x_525_, lean_object* v_x_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4___redArg(v_m_522_, v_query_523_, v_x_524_, v_x_525_, v_x_526_);
lean_dec_ref(v_query_523_);
lean_dec_ref(v_m_522_);
return v_res_527_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__5(lean_object* v_as_528_, size_t v_i_529_, size_t v_stop_530_, uint64_t v_b_531_){
_start:
{
uint8_t v___x_532_; 
v___x_532_ = lean_usize_dec_eq(v_i_529_, v_stop_530_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; uint64_t v___x_534_; uint64_t v___x_535_; size_t v___x_536_; size_t v___x_537_; 
v___x_533_ = lean_array_uget_borrowed(v_as_528_, v_i_529_);
v___x_534_ = l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash(v___x_533_);
v___x_535_ = lean_uint64_mix_hash(v_b_531_, v___x_534_);
v___x_536_ = ((size_t)1ULL);
v___x_537_ = lean_usize_add(v_i_529_, v___x_536_);
v_i_529_ = v___x_537_;
v_b_531_ = v___x_535_;
goto _start;
}
else
{
return v_b_531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__5___boxed(lean_object* v_as_539_, lean_object* v_i_540_, lean_object* v_stop_541_, lean_object* v_b_542_){
_start:
{
size_t v_i_boxed_543_; size_t v_stop_boxed_544_; uint64_t v_b_boxed_545_; uint64_t v_res_546_; lean_object* v_r_547_; 
v_i_boxed_543_ = lean_unbox_usize(v_i_540_);
lean_dec(v_i_540_);
v_stop_boxed_544_ = lean_unbox_usize(v_stop_541_);
lean_dec(v_stop_541_);
v_b_boxed_545_ = lean_unbox_uint64(v_b_542_);
lean_dec_ref(v_b_542_);
v_res_546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__5(v_as_539_, v_i_boxed_543_, v_stop_boxed_544_, v_b_boxed_545_);
lean_dec_ref(v_as_539_);
v_r_547_ = lean_box_uint64(v_res_546_);
return v_r_547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(lean_object* v_m_548_, lean_object* v_query_549_){
_start:
{
lean_object* v_keyArray_550_; lean_object* v_fst_551_; lean_object* v_snd_552_; lean_object* v___x_553_; uint64_t v___y_555_; uint64_t v___y_556_; uint64_t v___y_573_; 
v_keyArray_550_ = lean_ctor_get(v_m_548_, 1);
v_fst_551_ = lean_ctor_get(v_query_549_, 0);
v_snd_552_ = lean_ctor_get(v_query_549_, 1);
v___x_553_ = lean_array_get_size(v_keyArray_550_);
if (lean_obj_tag(v_fst_551_) == 0)
{
uint64_t v___x_585_; 
v___x_585_ = 1723ULL;
v___y_573_ = v___x_585_;
goto v___jp_572_;
}
else
{
uint64_t v_hash_586_; 
v_hash_586_ = lean_ctor_get_uint64(v_fst_551_, sizeof(void*)*2);
v___y_573_ = v_hash_586_;
goto v___jp_572_;
}
v___jp_554_:
{
uint64_t v___x_557_; uint64_t v___x_558_; uint64_t v___x_559_; uint64_t v_fold_560_; uint64_t v___x_561_; uint64_t v___x_562_; uint64_t v___x_563_; size_t v___x_564_; size_t v___x_565_; size_t v___x_566_; size_t v___x_567_; size_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_557_ = lean_uint64_mix_hash(v___y_555_, v___y_556_);
v___x_558_ = 32ULL;
v___x_559_ = lean_uint64_shift_right(v___x_557_, v___x_558_);
v_fold_560_ = lean_uint64_xor(v___x_557_, v___x_559_);
v___x_561_ = 16ULL;
v___x_562_ = lean_uint64_shift_right(v_fold_560_, v___x_561_);
v___x_563_ = lean_uint64_xor(v_fold_560_, v___x_562_);
v___x_564_ = lean_uint64_to_usize(v___x_563_);
v___x_565_ = lean_usize_of_nat(v___x_553_);
v___x_566_ = ((size_t)1ULL);
v___x_567_ = lean_usize_sub(v___x_565_, v___x_566_);
v___x_568_ = lean_usize_land(v___x_564_, v___x_567_);
v___x_569_ = lean_usize_to_nat(v___x_568_);
v___x_570_ = lean_box(0);
v___x_571_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4___redArg(v_m_548_, v_query_549_, v___x_570_, v___x_553_, v___x_569_);
return v___x_571_;
}
v___jp_572_:
{
uint64_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_574_ = 7ULL;
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_array_get_size(v_snd_552_);
v___x_577_ = lean_nat_dec_lt(v___x_575_, v___x_576_);
if (v___x_577_ == 0)
{
v___y_555_ = v___y_573_;
v___y_556_ = v___x_574_;
goto v___jp_554_;
}
else
{
uint8_t v___x_578_; 
v___x_578_ = lean_nat_dec_le(v___x_576_, v___x_576_);
if (v___x_578_ == 0)
{
if (v___x_577_ == 0)
{
v___y_555_ = v___y_573_;
v___y_556_ = v___x_574_;
goto v___jp_554_;
}
else
{
size_t v___x_579_; size_t v___x_580_; uint64_t v___x_581_; 
v___x_579_ = ((size_t)0ULL);
v___x_580_ = lean_usize_of_nat(v___x_576_);
v___x_581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__5(v_snd_552_, v___x_579_, v___x_580_, v___x_574_);
v___y_555_ = v___y_573_;
v___y_556_ = v___x_581_;
goto v___jp_554_;
}
}
else
{
size_t v___x_582_; size_t v___x_583_; uint64_t v___x_584_; 
v___x_582_ = ((size_t)0ULL);
v___x_583_ = lean_usize_of_nat(v___x_576_);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__5(v_snd_552_, v___x_582_, v___x_583_, v___x_574_);
v___y_555_ = v___y_573_;
v___y_556_ = v___x_584_;
goto v___jp_554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg___boxed(lean_object* v_m_587_, lean_object* v_query_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v_m_587_, v_query_588_);
lean_dec_ref(v_query_588_);
lean_dec_ref(v_m_587_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__2___redArg(lean_object* v_m_590_, lean_object* v_query_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v_m_590_, v_query_591_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_index_593_; lean_object* v_key_594_; lean_object* v_value_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
v_index_593_ = lean_ctor_get(v___x_592_, 0);
v_key_594_ = lean_ctor_get(v___x_592_, 1);
v_value_595_ = lean_ctor_get(v___x_592_, 2);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_592_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_value_595_);
lean_inc(v_key_594_);
lean_inc(v_index_593_);
lean_dec(v___x_592_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_index_593_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_key_594_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v_value_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
else
{
lean_object* v___x_603_; 
lean_dec(v___x_592_);
v___x_603_ = lean_box(1);
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__2___redArg___boxed(lean_object* v_m_604_, lean_object* v_query_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__2___redArg(v_m_604_, v_query_605_);
lean_dec_ref(v_query_605_);
lean_dec_ref(v_m_604_);
return v_res_606_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(lean_object* v_m_607_, lean_object* v_a_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__2___redArg(v_m_607_, v_a_608_);
if (lean_obj_tag(v___x_609_) == 0)
{
uint8_t v___x_610_; 
lean_dec_ref_known(v___x_609_, 3);
v___x_610_ = 1;
return v___x_610_;
}
else
{
uint8_t v___x_611_; 
v___x_611_ = 0;
return v___x_611_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg___boxed(lean_object* v_m_612_, lean_object* v_a_613_){
_start:
{
uint8_t v_res_614_; lean_object* v_r_615_; 
v_res_614_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(v_m_612_, v_a_613_);
lean_dec_ref(v_a_613_);
lean_dec_ref(v_m_612_);
v_r_615_ = lean_box(v_res_614_);
return v_r_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(lean_object* v_f_616_, lean_object* v_v_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
if (lean_obj_tag(v_v_617_) == 0)
{
lean_object* v_code_620_; lean_object* v___x_621_; 
v_code_620_ = lean_ctor_get(v_v_617_, 0);
lean_inc_ref(v_code_620_);
lean_dec_ref_known(v_v_617_, 1);
lean_inc_ref(v___y_618_);
v___x_621_ = lean_apply_3(v_f_616_, v_code_620_, v___y_618_, v___y_619_);
return v___x_621_;
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; 
lean_dec_ref_known(v_v_617_, 1);
lean_dec_ref(v_f_616_);
v___x_622_ = lean_box(0);
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
lean_ctor_set(v___x_623_, 1, v___y_619_);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg___boxed(lean_object* v_f_624_, lean_object* v_v_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_f_624_, v_v_625_, v___y_626_, v___y_627_);
lean_dec_ref(v___y_626_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7_spec__10___redArg(lean_object* v_b_629_, lean_object* v_acc_630_, lean_object* v_i_631_){
_start:
{
lean_object* v___y_633_; lean_object* v_keyArray_641_; lean_object* v_valueArray_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v_keyArray_641_ = lean_ctor_get(v_b_629_, 1);
v_valueArray_642_ = lean_ctor_get(v_b_629_, 2);
v___x_643_ = lean_array_get_size(v_keyArray_641_);
v___x_644_ = lean_nat_dec_lt(v_i_631_, v___x_643_);
if (v___x_644_ == 0)
{
lean_dec(v_i_631_);
return v_acc_630_;
}
else
{
lean_object* v___x_645_; uint8_t v_isSome_646_; 
v___x_645_ = lean_array_fget_borrowed(v_keyArray_641_, v_i_631_);
v_isSome_646_ = lean_noption_is_some(v___x_645_);
if (v_isSome_646_ == 0)
{
goto v___jp_637_;
}
else
{
lean_object* v___x_647_; uint8_t v_isSome_648_; 
v___x_647_ = lean_array_fget_borrowed(v_valueArray_642_, v_i_631_);
v_isSome_648_ = lean_noption_is_some(v___x_647_);
if (v_isSome_648_ == 0)
{
goto v___jp_637_;
}
else
{
lean_object* v_val_649_; lean_object* v_val_650_; lean_object* v_i_652_; lean_object* v___x_657_; 
lean_inc(v___x_645_);
v_val_649_ = lean_noption_get(v___x_645_);
lean_inc(v___x_647_);
v_val_650_ = lean_noption_get(v___x_647_);
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v_acc_630_, v_val_649_);
switch(lean_obj_tag(v___x_657_))
{
case 0:
{
lean_object* v_index_658_; lean_object* v_size_659_; lean_object* v___x_660_; 
v_index_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_index_658_);
lean_dec_ref_known(v___x_657_, 3);
v_size_659_ = lean_ctor_get(v_acc_630_, 0);
lean_inc(v_size_659_);
v___x_660_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_630_, v_size_659_, v_index_658_, v_val_649_, v_val_650_);
lean_dec(v_index_658_);
v___y_633_ = v___x_660_;
goto v___jp_632_;
}
case 1:
{
lean_object* v_index_661_; 
v_index_661_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_index_661_);
lean_dec_ref_known(v___x_657_, 1);
v_i_652_ = v_index_661_;
goto v___jp_651_;
}
default: 
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_630_, v___x_662_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_index_664_; 
v_index_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_index_664_);
lean_dec_ref_known(v___x_663_, 1);
v_i_652_ = v_index_664_;
goto v___jp_651_;
}
else
{
lean_dec(v_val_650_);
lean_dec(v_val_649_);
v___y_633_ = v_acc_630_;
goto v___jp_632_;
}
}
}
v___jp_651_:
{
lean_object* v_size_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_size_653_ = lean_ctor_get(v_acc_630_, 0);
v___x_654_ = lean_unsigned_to_nat(1u);
v___x_655_ = lean_nat_add(v_size_653_, v___x_654_);
v___x_656_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_630_, v___x_655_, v_i_652_, v_val_649_, v_val_650_);
lean_dec(v_i_652_);
v___y_633_ = v___x_656_;
goto v___jp_632_;
}
}
}
}
v___jp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_unsigned_to_nat(1u);
v___x_635_ = lean_nat_add(v_i_631_, v___x_634_);
lean_dec(v_i_631_);
v_acc_630_ = v___y_633_;
v_i_631_ = v___x_635_;
goto _start;
}
v___jp_637_:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = lean_nat_add(v_i_631_, v___x_638_);
lean_dec(v_i_631_);
v_i_631_ = v___x_639_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_b_665_, lean_object* v_acc_666_, lean_object* v_i_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7_spec__10___redArg(v_b_665_, v_acc_666_, v_i_667_);
lean_dec_ref(v_b_665_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7___redArg(lean_object* v_init_669_, lean_object* v_b_670_){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7_spec__10___redArg(v_b_670_, v_init_669_, v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7___redArg___boxed(lean_object* v_init_673_, lean_object* v_b_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7___redArg(v_init_673_, v_b_674_);
lean_dec_ref(v_b_674_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(lean_object* v_m_676_){
_start:
{
lean_object* v_keyArray_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v_cellCount_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v_target_684_; lean_object* v___x_685_; 
v_keyArray_677_ = lean_ctor_get(v_m_676_, 1);
v___x_678_ = lean_array_get_size(v_keyArray_677_);
v___x_679_ = lean_unsigned_to_nat(2u);
v_cellCount_680_ = lean_nat_mul(v___x_678_, v___x_679_);
v___x_681_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_680_);
v___x_682_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_680_);
v___x_683_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_680_);
v_target_684_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_684_, 0, v___x_681_);
lean_ctor_set(v_target_684_, 1, v___x_682_);
lean_ctor_set(v_target_684_, 2, v___x_683_);
v___x_685_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7___redArg(v_target_684_, v_m_676_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg___boxed(lean_object* v_m_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v_m_686_);
lean_dec_ref(v_m_686_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___redArg(lean_object* v_upperBound_688_, lean_object* v_args_689_, lean_object* v_a_690_, lean_object* v_b_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_a_695_; lean_object* v_a_696_; uint8_t v___x_700_; 
v___x_700_ = lean_nat_dec_lt(v_a_690_, v_upperBound_688_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; 
lean_dec(v_a_690_);
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v_b_691_);
lean_ctor_set(v___x_701_, 1, v___y_693_);
return v___x_701_;
}
else
{
lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_702_ = lean_array_get_size(v_args_689_);
v___x_703_ = lean_nat_dec_lt(v_a_690_, v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_box(0);
v___x_705_ = lean_array_push(v_b_691_, v___x_704_);
v_a_695_ = v___x_705_;
v_a_696_ = v___y_693_;
goto v___jp_694_;
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = lean_array_fget_borrowed(v_args_689_, v_a_690_);
v___x_707_ = l_Lean_Compiler_LCNF_FixedParams_evalArg(v___x_706_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v_a_709_; lean_object* v___x_710_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
v_a_709_ = lean_ctor_get(v___x_707_, 1);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_707_, 2);
v___x_710_ = lean_array_push(v_b_691_, v_a_708_);
v_a_695_ = v___x_710_;
v_a_696_ = v_a_709_;
goto v___jp_694_;
}
else
{
lean_object* v_a_711_; lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec_ref(v_b_691_);
lean_dec(v_a_690_);
v_a_711_ = lean_ctor_get(v___x_707_, 0);
v_a_712_ = lean_ctor_get(v___x_707_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_707_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_inc(v_a_711_);
lean_dec(v___x_707_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_711_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
v___jp_694_:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_unsigned_to_nat(1u);
v___x_698_ = lean_nat_add(v_a_690_, v___x_697_);
lean_dec(v_a_690_);
v_a_690_ = v___x_698_;
v_b_691_ = v_a_695_;
v___y_693_ = v_a_696_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___redArg___boxed(lean_object* v_upperBound_720_, lean_object* v_args_721_, lean_object* v_a_722_, lean_object* v_b_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___redArg(v_upperBound_720_, v_args_721_, v_a_722_, v_b_723_, v___y_724_, v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec_ref(v_args_721_);
lean_dec(v_upperBound_720_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__8___redArg(lean_object* v_upperBound_727_, lean_object* v_args_728_, lean_object* v_a_729_, lean_object* v_b_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_a_734_; lean_object* v_a_735_; uint8_t v___x_739_; 
v___x_739_ = lean_nat_dec_lt(v_a_729_, v_upperBound_727_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
lean_dec(v_a_729_);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v_b_730_);
lean_ctor_set(v___x_740_, 1, v___y_732_);
return v___x_740_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_741_ = lean_box(0);
v___x_742_ = lean_array_get_size(v_args_728_);
v___x_743_ = lean_nat_dec_lt(v_a_729_, v___x_742_);
if (v___x_743_ == 0)
{
lean_object* v_visited_744_; lean_object* v_fixed_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_754_; 
v_visited_744_ = lean_ctor_get(v___y_732_, 0);
v_fixed_745_ = lean_ctor_get(v___y_732_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v___y_732_);
if (v_isSharedCheck_754_ == 0)
{
v___x_747_ = v___y_732_;
v_isShared_748_ = v_isSharedCheck_754_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_fixed_745_);
lean_inc(v_visited_744_);
lean_dec(v___y_732_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_754_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_749_ = lean_box(v___x_743_);
v___x_750_ = lean_array_set(v_fixed_745_, v_a_729_, v___x_749_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v___x_750_);
v___x_752_ = v___x_747_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_visited_744_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
v_a_734_ = v___x_741_;
v_a_735_ = v___x_752_;
goto v___jp_733_;
}
}
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_array_fget_borrowed(v_args_728_, v_a_729_);
v___x_756_ = l_Lean_Compiler_LCNF_FixedParams_evalArg(v___x_755_, v___y_731_, v___y_732_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v_a_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
v_a_758_ = lean_ctor_get(v___x_756_, 1);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_756_, 2);
lean_inc(v_a_729_);
v___x_759_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_759_, 0, v_a_729_);
v___x_760_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v_a_757_, v___x_759_);
lean_dec_ref_known(v___x_759_, 1);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_761_ = lean_box(1);
v___x_762_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v_a_757_, v___x_761_);
lean_dec(v_a_757_);
if (v___x_762_ == 0)
{
lean_object* v_visited_763_; lean_object* v_fixed_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_773_; 
v_visited_763_ = lean_ctor_get(v_a_758_, 0);
v_fixed_764_ = lean_ctor_get(v_a_758_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_a_758_);
if (v_isSharedCheck_773_ == 0)
{
v___x_766_ = v_a_758_;
v_isShared_767_ = v_isSharedCheck_773_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_fixed_764_);
lean_inc(v_visited_763_);
lean_dec(v_a_758_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_773_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_768_ = lean_box(v___x_762_);
v___x_769_ = lean_array_set(v_fixed_764_, v_a_729_, v___x_768_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v___x_769_);
v___x_771_ = v___x_766_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_visited_763_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
v_a_734_ = v___x_741_;
v_a_735_ = v___x_771_;
goto v___jp_733_;
}
}
}
else
{
v_a_734_ = v___x_741_;
v_a_735_ = v_a_758_;
goto v___jp_733_;
}
}
else
{
lean_dec(v_a_757_);
v_a_734_ = v___x_741_;
v_a_735_ = v_a_758_;
goto v___jp_733_;
}
}
else
{
lean_object* v_a_774_; lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec(v_a_729_);
v_a_774_ = lean_ctor_get(v___x_756_, 0);
v_a_775_ = lean_ctor_get(v___x_756_, 1);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_756_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_inc(v_a_774_);
lean_dec(v___x_756_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_774_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
v___jp_733_:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_unsigned_to_nat(1u);
v___x_737_ = lean_nat_add(v_a_729_, v___x_736_);
lean_dec(v_a_729_);
v_a_729_ = v___x_737_;
v_b_730_ = v_a_734_;
v___y_732_ = v_a_735_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__8___redArg___boxed(lean_object* v_upperBound_783_, lean_object* v_args_784_, lean_object* v_a_785_, lean_object* v_b_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__8___redArg(v_upperBound_783_, v_args_784_, v_a_785_, v_b_786_, v___y_787_, v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec_ref(v_args_784_);
lean_dec(v_upperBound_783_);
return v_res_789_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7_spec__11(uint8_t v_a_790_, lean_object* v_as_791_, size_t v_i_792_, size_t v_stop_793_){
_start:
{
uint8_t v___x_798_; 
v___x_798_ = lean_usize_dec_eq(v_i_792_, v_stop_793_);
if (v___x_798_ == 0)
{
uint8_t v___x_799_; lean_object* v___x_800_; 
v___x_799_ = 1;
v___x_800_ = lean_array_uget_borrowed(v_as_791_, v_i_792_);
if (v_a_790_ == 0)
{
uint8_t v___x_801_; 
v___x_801_ = lean_unbox(v___x_800_);
if (v___x_801_ == 0)
{
return v___x_799_;
}
else
{
goto v___jp_794_;
}
}
else
{
uint8_t v___x_802_; 
v___x_802_ = lean_unbox(v___x_800_);
if (v___x_802_ == 0)
{
goto v___jp_794_;
}
else
{
return v___x_799_;
}
}
}
else
{
uint8_t v___x_803_; 
v___x_803_ = 0;
return v___x_803_;
}
v___jp_794_:
{
size_t v___x_795_; size_t v___x_796_; 
v___x_795_ = ((size_t)1ULL);
v___x_796_ = lean_usize_add(v_i_792_, v___x_795_);
v_i_792_ = v___x_796_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7_spec__11___boxed(lean_object* v_a_804_, lean_object* v_as_805_, lean_object* v_i_806_, lean_object* v_stop_807_){
_start:
{
uint8_t v_a_boxed_808_; size_t v_i_boxed_809_; size_t v_stop_boxed_810_; uint8_t v_res_811_; lean_object* v_r_812_; 
v_a_boxed_808_ = lean_unbox(v_a_804_);
v_i_boxed_809_ = lean_unbox_usize(v_i_806_);
lean_dec(v_i_806_);
v_stop_boxed_810_ = lean_unbox_usize(v_stop_807_);
lean_dec(v_stop_807_);
v_res_811_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7_spec__11(v_a_boxed_808_, v_as_805_, v_i_boxed_809_, v_stop_boxed_810_);
lean_dec_ref(v_as_805_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7(lean_object* v_as_813_, uint8_t v_a_814_){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = lean_array_get_size(v_as_813_);
v___x_817_ = lean_nat_dec_lt(v___x_815_, v___x_816_);
if (v___x_817_ == 0)
{
return v___x_817_;
}
else
{
if (v___x_817_ == 0)
{
return v___x_817_;
}
else
{
size_t v___x_818_; size_t v___x_819_; uint8_t v___x_820_; 
v___x_818_ = ((size_t)0ULL);
v___x_819_ = lean_usize_of_nat(v___x_816_);
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7_spec__11(v_a_814_, v_as_813_, v___x_818_, v___x_819_);
return v___x_820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___boxed(lean_object* v_as_821_, lean_object* v_a_822_){
_start:
{
uint8_t v_a_boxed_823_; uint8_t v_res_824_; lean_object* v_r_825_; 
v_a_boxed_823_ = lean_unbox(v_a_822_);
v_res_824_ = l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7(v_as_821_, v_a_boxed_823_);
lean_dec_ref(v_as_821_);
v_r_825_ = lean_box(v_res_824_);
return v_r_825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___lam__0___boxed(lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_c_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___lam__0(v_a_828_, v_a_829_, v_c_830_, v___y_831_, v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec_ref(v_a_828_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(lean_object* v_declName_834_, lean_object* v_args_835_, lean_object* v_as_836_, size_t v_sz_837_, size_t v_i_838_, lean_object* v_b_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_a_843_; lean_object* v_a_844_; uint8_t v___x_848_; 
v___x_848_ = lean_usize_dec_lt(v_i_838_, v_sz_837_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; 
lean_dec(v_declName_834_);
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v_b_839_);
lean_ctor_set(v___x_849_, 1, v___y_841_);
return v___x_849_;
}
else
{
lean_object* v_a_850_; lean_object* v_toSignature_851_; lean_object* v_value_852_; lean_object* v_name_853_; lean_object* v_params_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v_a_850_ = lean_array_uget_borrowed(v_as_836_, v_i_838_);
v_toSignature_851_ = lean_ctor_get(v_a_850_, 0);
v_value_852_ = lean_ctor_get(v_a_850_, 1);
v_name_853_ = lean_ctor_get(v_toSignature_851_, 0);
v_params_854_ = lean_ctor_get(v_toSignature_851_, 3);
v___x_855_ = lean_box(0);
v___x_856_ = lean_name_eq(v_declName_834_, v_name_853_);
if (v___x_856_ == 0)
{
v_a_843_ = v___x_855_;
v_a_844_ = v___y_841_;
goto v___jp_842_;
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_857_ = lean_array_get_size(v_params_854_);
v___x_858_ = lean_unsigned_to_nat(0u);
v___x_859_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___closed__0));
v___x_860_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___redArg(v___x_857_, v_args_835_, v___x_858_, v___x_859_, v___y_840_, v___y_841_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v_a_862_; lean_object* v_visited_863_; lean_object* v_fixed_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v_a_861_ = lean_ctor_get(v___x_860_, 1);
lean_inc(v_a_861_);
v_a_862_ = lean_ctor_get(v___x_860_, 0);
lean_inc_n(v_a_862_, 2);
lean_dec_ref_known(v___x_860_, 2);
v_visited_863_ = lean_ctor_get(v_a_861_, 0);
v_fixed_864_ = lean_ctor_get(v_a_861_, 1);
lean_inc(v_declName_834_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v_declName_834_);
lean_ctor_set(v___x_865_, 1, v_a_862_);
v___x_866_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(v_visited_863_, v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_937_; 
lean_inc_ref(v_fixed_864_);
lean_inc_ref(v_visited_863_);
v_isSharedCheck_937_ = !lean_is_exclusive(v_a_861_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; lean_object* v_unused_939_; 
v_unused_938_ = lean_ctor_get(v_a_861_, 1);
lean_dec(v_unused_938_);
v_unused_939_ = lean_ctor_get(v_a_861_, 0);
lean_dec(v_unused_939_);
v___x_868_ = v_a_861_;
v_isShared_869_ = v_isSharedCheck_937_;
goto v_resetjp_867_;
}
else
{
lean_dec(v_a_861_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_937_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___f_870_; lean_object* v___y_872_; lean_object* v___y_879_; lean_object* v_i_880_; lean_object* v___y_895_; lean_object* v_i_896_; lean_object* v___y_902_; lean_object* v___x_910_; 
lean_inc(v_a_850_);
v___f_870_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___lam__0___boxed), 5, 2);
lean_closure_set(v___f_870_, 0, v_a_850_);
lean_closure_set(v___f_870_, 1, v_a_862_);
v___x_910_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v_visited_863_, v___x_865_);
switch(lean_obj_tag(v___x_910_))
{
case 0:
{
lean_dec_ref_known(v___x_910_, 3);
lean_dec_ref_known(v___x_865_, 2);
v___y_872_ = v_visited_863_;
goto v___jp_871_;
}
case 1:
{
lean_object* v_index_911_; lean_object* v_size_912_; lean_object* v_keyArray_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v_index_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_index_911_);
lean_dec_ref_known(v___x_910_, 1);
v_size_912_ = lean_ctor_get(v_visited_863_, 0);
v_keyArray_913_ = lean_ctor_get(v_visited_863_, 1);
v___x_914_ = lean_unsigned_to_nat(1u);
v___x_915_ = lean_nat_add(v_size_912_, v___x_914_);
v___x_916_ = lean_array_get_size(v_keyArray_913_);
v___x_917_ = lean_nat_dec_lt(v___x_915_, v___x_916_);
if (v___x_917_ == 0)
{
lean_dec(v___x_915_);
lean_dec(v_index_911_);
goto v___jp_885_;
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_918_ = lean_unsigned_to_nat(4u);
v___x_919_ = lean_nat_mul(v___x_915_, v___x_918_);
v___x_920_ = lean_unsigned_to_nat(3u);
v___x_921_ = lean_nat_mul(v___x_916_, v___x_920_);
v___x_922_ = lean_nat_dec_le(v___x_919_, v___x_921_);
lean_dec(v___x_921_);
lean_dec(v___x_919_);
if (v___x_922_ == 0)
{
lean_dec(v___x_915_);
lean_dec(v_index_911_);
goto v___jp_885_;
}
else
{
lean_object* v___x_923_; 
v___x_923_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visited_863_, v___x_915_, v_index_911_, v___x_865_, v___x_855_);
lean_dec(v_index_911_);
v___y_872_ = v___x_923_;
goto v___jp_871_;
}
}
}
default: 
{
lean_object* v_size_924_; lean_object* v_keyArray_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v_size_924_ = lean_ctor_get(v_visited_863_, 0);
v_keyArray_925_ = lean_ctor_get(v_visited_863_, 1);
v___x_926_ = lean_unsigned_to_nat(1u);
v___x_927_ = lean_nat_add(v_size_924_, v___x_926_);
v___x_928_ = lean_array_get_size(v_keyArray_925_);
v___x_929_ = lean_nat_dec_lt(v___x_927_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; 
lean_dec(v___x_927_);
v___x_930_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v_visited_863_);
lean_dec_ref(v_visited_863_);
v___y_902_ = v___x_930_;
goto v___jp_901_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_931_ = lean_unsigned_to_nat(4u);
v___x_932_ = lean_nat_mul(v___x_927_, v___x_931_);
lean_dec(v___x_927_);
v___x_933_ = lean_unsigned_to_nat(3u);
v___x_934_ = lean_nat_mul(v___x_928_, v___x_933_);
v___x_935_ = lean_nat_dec_le(v___x_932_, v___x_934_);
lean_dec(v___x_934_);
lean_dec(v___x_932_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; 
v___x_936_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v_visited_863_);
lean_dec_ref(v_visited_863_);
v___y_902_ = v___x_936_;
goto v___jp_901_;
}
else
{
v___y_902_ = v_visited_863_;
goto v___jp_901_;
}
}
}
}
v___jp_871_:
{
lean_object* v___x_874_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___y_872_);
v___x_874_ = v___x_868_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___y_872_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_fixed_864_);
v___x_874_ = v_reuseFailAlloc_877_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_875_; 
lean_inc_ref(v_value_852_);
v___x_875_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v___f_870_, v_value_852_, v___y_840_, v___x_874_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; 
v_a_876_ = lean_ctor_get(v___x_875_, 1);
lean_inc(v_a_876_);
lean_dec_ref_known(v___x_875_, 2);
v_a_843_ = v___x_855_;
v_a_844_ = v_a_876_;
goto v___jp_842_;
}
else
{
lean_dec(v_declName_834_);
return v___x_875_;
}
}
}
v___jp_878_:
{
lean_object* v_size_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_size_881_ = lean_ctor_get(v___y_879_, 0);
v___x_882_ = lean_unsigned_to_nat(1u);
v___x_883_ = lean_nat_add(v_size_881_, v___x_882_);
v___x_884_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_879_, v___x_883_, v_i_880_, v___x_865_, v___x_855_);
lean_dec(v_i_880_);
v___y_872_ = v___x_884_;
goto v___jp_871_;
}
v___jp_885_:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v_visited_863_);
lean_dec_ref(v_visited_863_);
v___x_887_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v___x_886_, v___x_865_);
switch(lean_obj_tag(v___x_887_))
{
case 0:
{
lean_object* v_index_888_; lean_object* v_size_889_; lean_object* v___x_890_; 
v_index_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_index_888_);
lean_dec_ref_known(v___x_887_, 3);
v_size_889_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_size_889_);
v___x_890_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_886_, v_size_889_, v_index_888_, v___x_865_, v___x_855_);
lean_dec(v_index_888_);
v___y_872_ = v___x_890_;
goto v___jp_871_;
}
case 1:
{
lean_object* v_index_891_; 
v_index_891_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_index_891_);
lean_dec_ref_known(v___x_887_, 1);
v___y_879_ = v___x_886_;
v_i_880_ = v_index_891_;
goto v___jp_878_;
}
default: 
{
lean_object* v___x_892_; 
v___x_892_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_886_, v___x_858_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_index_893_; 
v_index_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_index_893_);
lean_dec_ref_known(v___x_892_, 1);
v___y_879_ = v___x_886_;
v_i_880_ = v_index_893_;
goto v___jp_878_;
}
else
{
lean_dec_ref_known(v___x_865_, 2);
v___y_872_ = v___x_886_;
goto v___jp_871_;
}
}
}
}
v___jp_894_:
{
lean_object* v_size_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_size_897_ = lean_ctor_get(v___y_895_, 0);
v___x_898_ = lean_unsigned_to_nat(1u);
v___x_899_ = lean_nat_add(v_size_897_, v___x_898_);
v___x_900_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_895_, v___x_899_, v_i_896_, v___x_865_, v___x_855_);
lean_dec(v_i_896_);
v___y_872_ = v___x_900_;
goto v___jp_871_;
}
v___jp_901_:
{
lean_object* v___x_903_; 
v___x_903_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v___y_902_, v___x_865_);
switch(lean_obj_tag(v___x_903_))
{
case 0:
{
lean_object* v_index_904_; lean_object* v_size_905_; lean_object* v___x_906_; 
v_index_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_index_904_);
lean_dec_ref_known(v___x_903_, 3);
v_size_905_ = lean_ctor_get(v___y_902_, 0);
lean_inc(v_size_905_);
v___x_906_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_902_, v_size_905_, v_index_904_, v___x_865_, v___x_855_);
lean_dec(v_index_904_);
v___y_872_ = v___x_906_;
goto v___jp_871_;
}
case 1:
{
lean_object* v_index_907_; 
v_index_907_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_index_907_);
lean_dec_ref_known(v___x_903_, 1);
v___y_895_ = v___y_902_;
v_i_896_ = v_index_907_;
goto v___jp_894_;
}
default: 
{
lean_object* v___x_908_; 
v___x_908_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_902_, v___x_858_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_index_909_; 
v_index_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_index_909_);
lean_dec_ref_known(v___x_908_, 1);
v___y_895_ = v___y_902_;
v_i_896_ = v_index_909_;
goto v___jp_894_;
}
else
{
lean_dec_ref_known(v___x_865_, 2);
v___y_872_ = v___y_902_;
goto v___jp_871_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_865_, 2);
lean_dec(v_a_862_);
v_a_843_ = v___x_855_;
v_a_844_ = v_a_861_;
goto v___jp_842_;
}
}
else
{
lean_object* v_a_940_; lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec(v_declName_834_);
v_a_940_ = lean_ctor_get(v___x_860_, 0);
v_a_941_ = lean_ctor_get(v___x_860_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_860_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_inc(v_a_940_);
lean_dec(v___x_860_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_940_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
v___jp_842_:
{
size_t v___x_845_; size_t v___x_846_; 
v___x_845_ = ((size_t)1ULL);
v___x_846_ = lean_usize_add(v_i_838_, v___x_845_);
v_i_838_ = v___x_846_;
v_b_839_ = v_a_843_;
v___y_841_ = v_a_844_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp(lean_object* v_declName_949_, lean_object* v_args_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v___y_954_; lean_object* v_decls_955_; lean_object* v___y_956_; lean_object* v_main_970_; lean_object* v_toSignature_971_; lean_object* v_decls_972_; lean_object* v_name_973_; lean_object* v_params_974_; uint8_t v___x_975_; 
v_main_970_ = lean_ctor_get(v_a_951_, 1);
v_toSignature_971_ = lean_ctor_get(v_main_970_, 0);
v_decls_972_ = lean_ctor_get(v_a_951_, 0);
v_name_973_ = lean_ctor_get(v_toSignature_971_, 0);
v_params_974_ = lean_ctor_get(v_toSignature_971_, 3);
v___x_975_ = lean_name_eq(v_declName_949_, v_name_973_);
if (v___x_975_ == 0)
{
v___y_954_ = v_a_951_;
v_decls_955_ = v_decls_972_;
v___y_956_ = v_a_952_;
goto v___jp_953_;
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_976_ = lean_array_get_size(v_params_974_);
v___x_977_ = lean_unsigned_to_nat(0u);
v___x_978_ = lean_box(0);
v___x_979_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__8___redArg(v___x_976_, v_args_950_, v___x_977_, v___x_978_, v_a_951_, v_a_952_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_989_; 
v_a_980_ = lean_ctor_get(v___x_979_, 1);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_989_ == 0)
{
lean_object* v_unused_990_; 
v_unused_990_ = lean_ctor_get(v___x_979_, 0);
lean_dec(v_unused_990_);
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_989_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_989_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v_fixed_984_; uint8_t v___x_985_; 
v_fixed_984_ = lean_ctor_get(v_a_980_, 1);
v___x_985_ = l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7(v_fixed_984_, v___x_975_);
if (v___x_985_ == 0)
{
lean_object* v___x_987_; 
lean_dec(v_declName_949_);
if (v_isShared_983_ == 0)
{
lean_ctor_set_tag(v___x_982_, 1);
lean_ctor_set(v___x_982_, 0, v___x_978_);
v___x_987_ = v___x_982_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_a_980_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
else
{
lean_del_object(v___x_982_);
v___y_954_ = v_a_951_;
v_decls_955_ = v_decls_972_;
v___y_956_ = v_a_980_;
goto v___jp_953_;
}
}
}
else
{
lean_dec(v_declName_949_);
return v___x_979_;
}
}
v___jp_953_:
{
lean_object* v___x_957_; size_t v_sz_958_; size_t v___x_959_; lean_object* v___x_960_; 
v___x_957_ = lean_box(0);
v_sz_958_ = lean_array_size(v_decls_955_);
v___x_959_ = ((size_t)0ULL);
v___x_960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(v_declName_949_, v_args_950_, v_decls_955_, v_sz_958_, v___x_959_, v___x_957_, v___y_954_, v___y_956_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
v_a_961_ = lean_ctor_get(v___x_960_, 1);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; 
v_unused_969_ = lean_ctor_get(v___x_960_, 0);
lean_dec(v_unused_969_);
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_957_);
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
else
{
return v___x_960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalLetValue(lean_object* v_e_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
if (lean_obj_tag(v_e_991_) == 3)
{
lean_object* v_declName_994_; lean_object* v_args_995_; lean_object* v___x_996_; 
v_declName_994_ = lean_ctor_get(v_e_991_, 0);
lean_inc(v_declName_994_);
v_args_995_ = lean_ctor_get(v_e_991_, 2);
lean_inc_ref(v_args_995_);
lean_dec_ref_known(v_e_991_, 3);
v___x_996_ = l_Lean_Compiler_LCNF_FixedParams_evalApp(v_declName_994_, v_args_995_, v_a_992_, v_a_993_);
lean_dec_ref(v_args_995_);
return v___x_996_;
}
else
{
lean_object* v___x_997_; lean_object* v___x_998_; 
lean_dec(v_e_991_);
v___x_997_ = lean_box(0);
v___x_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v_a_993_);
return v___x_998_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__10(lean_object* v_as_999_, size_t v_i_1000_, size_t v_stop_1001_, lean_object* v_b_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___y_1006_; uint8_t v___x_1013_; 
v___x_1013_ = lean_usize_dec_eq(v_i_1000_, v_stop_1001_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_array_uget_borrowed(v_as_999_, v_i_1000_);
switch(lean_obj_tag(v___x_1014_))
{
case 0:
{
lean_object* v_code_1015_; 
v_code_1015_ = lean_ctor_get(v___x_1014_, 2);
lean_inc_ref(v_code_1015_);
v___y_1006_ = v_code_1015_;
goto v___jp_1005_;
}
case 1:
{
lean_object* v_code_1016_; 
v_code_1016_ = lean_ctor_get(v___x_1014_, 1);
lean_inc_ref(v_code_1016_);
v___y_1006_ = v_code_1016_;
goto v___jp_1005_;
}
default: 
{
lean_object* v_code_1017_; 
v_code_1017_ = lean_ctor_get(v___x_1014_, 0);
lean_inc_ref(v_code_1017_);
v___y_1006_ = v_code_1017_;
goto v___jp_1005_;
}
}
}
else
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v_b_1002_);
lean_ctor_set(v___x_1018_, 1, v___y_1004_);
return v___x_1018_;
}
v___jp_1005_:
{
lean_object* v___x_1007_; 
lean_inc_ref(v___y_1003_);
v___x_1007_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v___y_1006_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v_a_1009_; size_t v___x_1010_; size_t v___x_1011_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
v_a_1009_ = lean_ctor_get(v___x_1007_, 1);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1007_, 2);
v___x_1010_ = ((size_t)1ULL);
v___x_1011_ = lean_usize_add(v_i_1000_, v___x_1010_);
v_i_1000_ = v___x_1011_;
v_b_1002_ = v_a_1008_;
v___y_1004_ = v_a_1009_;
goto _start;
}
else
{
return v___x_1007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalCode(lean_object* v_code_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
switch(lean_obj_tag(v_code_1019_))
{
case 0:
{
lean_object* v_decl_1022_; lean_object* v_k_1023_; lean_object* v_value_1024_; lean_object* v___x_1025_; 
v_decl_1022_ = lean_ctor_get(v_code_1019_, 0);
lean_inc_ref(v_decl_1022_);
v_k_1023_ = lean_ctor_get(v_code_1019_, 1);
lean_inc_ref(v_k_1023_);
lean_dec_ref_known(v_code_1019_, 2);
v_value_1024_ = lean_ctor_get(v_decl_1022_, 3);
lean_inc(v_value_1024_);
lean_dec_ref(v_decl_1022_);
v___x_1025_ = l_Lean_Compiler_LCNF_FixedParams_evalLetValue(v_value_1024_, v_a_1020_, v_a_1021_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 1);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 2);
v_code_1019_ = v_k_1023_;
v_a_1021_ = v_a_1026_;
goto _start;
}
else
{
lean_dec_ref(v_k_1023_);
lean_dec_ref(v_a_1020_);
return v___x_1025_;
}
}
case 1:
{
lean_object* v_decl_1028_; lean_object* v_k_1029_; lean_object* v___x_1030_; 
v_decl_1028_ = lean_ctor_get(v_code_1019_, 0);
lean_inc_ref_n(v_decl_1028_, 2);
v_k_1029_ = lean_ctor_get(v_code_1019_, 1);
lean_inc_ref(v_k_1029_);
lean_dec_ref_known(v_code_1019_, 2);
v___x_1030_ = l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(v_decl_1028_, v_a_1020_, v_a_1021_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1031_);
if (lean_obj_tag(v_a_1031_) == 1)
{
lean_object* v_a_1032_; lean_object* v_val_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1047_; 
v_a_1032_ = lean_ctor_get(v___x_1030_, 1);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1030_, 2);
v_val_1033_ = lean_ctor_get(v_a_1031_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_a_1031_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1035_ = v_a_1031_;
v_isShared_1036_ = v_isSharedCheck_1047_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_val_1033_);
lean_dec(v_a_1031_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1047_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v_fvarId_1037_; lean_object* v_decls_1038_; lean_object* v_main_1039_; lean_object* v_assignment_1040_; lean_object* v___x_1042_; 
v_fvarId_1037_ = lean_ctor_get(v_decl_1028_, 0);
lean_inc(v_fvarId_1037_);
lean_dec_ref(v_decl_1028_);
v_decls_1038_ = lean_ctor_get(v_a_1020_, 0);
lean_inc_ref(v_decls_1038_);
v_main_1039_ = lean_ctor_get(v_a_1020_, 1);
lean_inc_ref(v_main_1039_);
v_assignment_1040_ = lean_ctor_get(v_a_1020_, 2);
lean_inc(v_assignment_1040_);
lean_dec_ref(v_a_1020_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set_tag(v___x_1035_, 2);
v___x_1042_ = v___x_1035_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_val_1033_);
v___x_1042_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1037_, v___x_1042_, v_assignment_1040_);
v___x_1044_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1044_, 0, v_decls_1038_);
lean_ctor_set(v___x_1044_, 1, v_main_1039_);
lean_ctor_set(v___x_1044_, 2, v___x_1043_);
v_code_1019_ = v_k_1029_;
v_a_1020_ = v___x_1044_;
v_a_1021_ = v_a_1032_;
goto _start;
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v_value_1049_; lean_object* v___x_1050_; 
lean_dec(v_a_1031_);
v_a_1048_ = lean_ctor_get(v___x_1030_, 1);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1030_, 2);
v_value_1049_ = lean_ctor_get(v_decl_1028_, 4);
lean_inc_ref(v_value_1049_);
lean_dec_ref(v_decl_1028_);
lean_inc_ref(v_a_1020_);
v___x_1050_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_value_1049_, v_a_1020_, v_a_1048_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 1);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 2);
v_code_1019_ = v_k_1029_;
v_a_1021_ = v_a_1051_;
goto _start;
}
else
{
lean_dec_ref(v_k_1029_);
lean_dec_ref(v_a_1020_);
return v___x_1050_;
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_dec_ref(v_k_1029_);
lean_dec_ref(v_decl_1028_);
lean_dec_ref(v_a_1020_);
v_a_1053_ = lean_ctor_get(v___x_1030_, 0);
v_a_1054_ = lean_ctor_get(v___x_1030_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1030_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_inc(v_a_1053_);
lean_dec(v___x_1030_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1053_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
case 2:
{
lean_object* v_decl_1062_; lean_object* v_k_1063_; lean_object* v_value_1064_; lean_object* v___x_1065_; 
v_decl_1062_ = lean_ctor_get(v_code_1019_, 0);
lean_inc_ref(v_decl_1062_);
v_k_1063_ = lean_ctor_get(v_code_1019_, 1);
lean_inc_ref(v_k_1063_);
lean_dec_ref_known(v_code_1019_, 2);
v_value_1064_ = lean_ctor_get(v_decl_1062_, 4);
lean_inc_ref(v_value_1064_);
lean_dec_ref(v_decl_1062_);
lean_inc_ref(v_a_1020_);
v___x_1065_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_value_1064_, v_a_1020_, v_a_1021_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 1);
lean_inc(v_a_1066_);
lean_dec_ref_known(v___x_1065_, 2);
v_code_1019_ = v_k_1063_;
v_a_1021_ = v_a_1066_;
goto _start;
}
else
{
lean_dec_ref(v_k_1063_);
lean_dec_ref(v_a_1020_);
return v___x_1065_;
}
}
case 3:
{
lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1075_; 
lean_dec_ref(v_a_1020_);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_code_1019_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; lean_object* v_unused_1077_; 
v_unused_1076_ = lean_ctor_get(v_code_1019_, 1);
lean_dec(v_unused_1076_);
v_unused_1077_ = lean_ctor_get(v_code_1019_, 0);
lean_dec(v_unused_1077_);
v___x_1069_ = v_code_1019_;
v_isShared_1070_ = v_isSharedCheck_1075_;
goto v_resetjp_1068_;
}
else
{
lean_dec(v_code_1019_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1075_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1071_ = lean_box(0);
if (v_isShared_1070_ == 0)
{
lean_ctor_set_tag(v___x_1069_, 0);
lean_ctor_set(v___x_1069_, 1, v_a_1021_);
lean_ctor_set(v___x_1069_, 0, v___x_1071_);
v___x_1073_ = v___x_1069_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_a_1021_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
case 4:
{
lean_object* v_cases_1078_; lean_object* v_alts_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v_cases_1078_ = lean_ctor_get(v_code_1019_, 0);
lean_inc_ref(v_cases_1078_);
lean_dec_ref_known(v_code_1019_, 1);
v_alts_1079_ = lean_ctor_get(v_cases_1078_, 3);
lean_inc_ref(v_alts_1079_);
lean_dec_ref(v_cases_1078_);
v___x_1080_ = lean_unsigned_to_nat(0u);
v___x_1081_ = lean_array_get_size(v_alts_1079_);
v___x_1082_ = lean_box(0);
v___x_1083_ = lean_nat_dec_lt(v___x_1080_, v___x_1081_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
lean_dec_ref(v_alts_1079_);
lean_dec_ref(v_a_1020_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v_a_1021_);
return v___x_1084_;
}
else
{
uint8_t v___x_1085_; 
v___x_1085_ = lean_nat_dec_le(v___x_1081_, v___x_1081_);
if (v___x_1085_ == 0)
{
if (v___x_1083_ == 0)
{
lean_object* v___x_1086_; 
lean_dec_ref(v_alts_1079_);
lean_dec_ref(v_a_1020_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1082_);
lean_ctor_set(v___x_1086_, 1, v_a_1021_);
return v___x_1086_;
}
else
{
size_t v___x_1087_; size_t v___x_1088_; lean_object* v___x_1089_; 
v___x_1087_ = ((size_t)0ULL);
v___x_1088_ = lean_usize_of_nat(v___x_1081_);
v___x_1089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__10(v_alts_1079_, v___x_1087_, v___x_1088_, v___x_1082_, v_a_1020_, v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec_ref(v_alts_1079_);
return v___x_1089_;
}
}
else
{
size_t v___x_1090_; size_t v___x_1091_; lean_object* v___x_1092_; 
v___x_1090_ = ((size_t)0ULL);
v___x_1091_ = lean_usize_of_nat(v___x_1081_);
v___x_1092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__10(v_alts_1079_, v___x_1090_, v___x_1091_, v___x_1082_, v_a_1020_, v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec_ref(v_alts_1079_);
return v___x_1092_;
}
}
}
default: 
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_dec_ref(v_a_1020_);
lean_dec_ref(v_code_1019_);
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v_a_1021_);
return v___x_1094_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___lam__0(lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_c_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_decls_1100_; lean_object* v_main_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v_decls_1100_ = lean_ctor_get(v___y_1098_, 0);
v_main_1101_ = lean_ctor_get(v___y_1098_, 1);
v___x_1102_ = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(v_a_1095_, v_a_1096_);
lean_inc_ref(v_main_1101_);
lean_inc_ref(v_decls_1100_);
v___x_1103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1103_, 0, v_decls_1100_);
lean_ctor_set(v___x_1103_, 1, v_main_1101_);
lean_ctor_set(v___x_1103_, 2, v___x_1102_);
v___x_1104_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_c_1097_, v___x_1103_, v___y_1099_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalLetValue___boxed(lean_object* v_e_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_Compiler_LCNF_FixedParams_evalLetValue(v_e_1105_, v_a_1106_, v_a_1107_);
lean_dec_ref(v_a_1106_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__10___boxed(lean_object* v_as_1109_, lean_object* v_i_1110_, lean_object* v_stop_1111_, lean_object* v_b_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
size_t v_i_boxed_1115_; size_t v_stop_boxed_1116_; lean_object* v_res_1117_; 
v_i_boxed_1115_ = lean_unbox_usize(v_i_1110_);
lean_dec(v_i_1110_);
v_stop_boxed_1116_ = lean_unbox_usize(v_stop_1111_);
lean_dec(v_stop_1111_);
v_res_1117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__10(v_as_1109_, v_i_boxed_1115_, v_stop_boxed_1116_, v_b_1112_, v___y_1113_, v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec_ref(v_as_1109_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp___boxed(lean_object* v_declName_1118_, lean_object* v_args_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_Compiler_LCNF_FixedParams_evalApp(v_declName_1118_, v_args_1119_, v_a_1120_, v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec_ref(v_args_1119_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___boxed(lean_object* v_declName_1123_, lean_object* v_args_1124_, lean_object* v_as_1125_, lean_object* v_sz_1126_, lean_object* v_i_1127_, lean_object* v_b_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
size_t v_sz_boxed_1131_; size_t v_i_boxed_1132_; lean_object* v_res_1133_; 
v_sz_boxed_1131_ = lean_unbox_usize(v_sz_1126_);
lean_dec(v_sz_1126_);
v_i_boxed_1132_ = lean_unbox_usize(v_i_1127_);
lean_dec(v_i_1127_);
v_res_1133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(v_declName_1123_, v_args_1124_, v_as_1125_, v_sz_boxed_1131_, v_i_boxed_1132_, v_b_1128_, v___y_1129_, v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec_ref(v_as_1125_);
lean_dec_ref(v_args_1124_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1(uint8_t v_pu_1134_, lean_object* v_f_1135_, lean_object* v_v_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_f_1135_, v_v_1136_, v___y_1137_, v___y_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___boxed(lean_object* v_pu_1140_, lean_object* v_f_1141_, lean_object* v_v_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
uint8_t v_pu_boxed_1145_; lean_object* v_res_1146_; 
v_pu_boxed_1145_ = lean_unbox(v_pu_1140_);
v_res_1146_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1(v_pu_boxed_1145_, v_f_1141_, v_v_1142_, v___y_1143_, v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1146_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2(lean_object* v_00_u03b2_1147_, lean_object* v_m_1148_, lean_object* v_a_1149_){
_start:
{
uint8_t v___x_1150_; 
v___x_1150_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(v_m_1148_, v_a_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___boxed(lean_object* v_00_u03b2_1151_, lean_object* v_m_1152_, lean_object* v_a_1153_){
_start:
{
uint8_t v_res_1154_; lean_object* v_r_1155_; 
v_res_1154_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2(v_00_u03b2_1151_, v_m_1152_, v_a_1153_);
lean_dec_ref(v_a_1153_);
lean_dec_ref(v_m_1152_);
v_r_1155_ = lean_box(v_res_1154_);
return v_r_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3(lean_object* v_00_u03b2_1156_, lean_object* v_m_1157_, lean_object* v_query_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v_m_1157_, v_query_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___boxed(lean_object* v_00_u03b2_1160_, lean_object* v_m_1161_, lean_object* v_query_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3(v_00_u03b2_1160_, v_m_1161_, v_query_1162_);
lean_dec_ref(v_query_1162_);
lean_dec_ref(v_m_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4(lean_object* v_00_u03b2_1164_, lean_object* v_m_1165_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v_m_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___boxed(lean_object* v_00_u03b2_1167_, lean_object* v_m_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4(v_00_u03b2_1167_, v_m_1168_);
lean_dec_ref(v_m_1168_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(lean_object* v_upperBound_1170_, lean_object* v_args_1171_, lean_object* v_inst_1172_, lean_object* v_R_1173_, lean_object* v_a_1174_, lean_object* v_b_1175_, lean_object* v_c_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___redArg(v_upperBound_1170_, v_args_1171_, v_a_1174_, v_b_1175_, v___y_1177_, v___y_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___boxed(lean_object* v_upperBound_1180_, lean_object* v_args_1181_, lean_object* v_inst_1182_, lean_object* v_R_1183_, lean_object* v_a_1184_, lean_object* v_b_1185_, lean_object* v_c_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(v_upperBound_1180_, v_args_1181_, v_inst_1182_, v_R_1183_, v_a_1184_, v_b_1185_, v_c_1186_, v___y_1187_, v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v_args_1181_);
lean_dec(v_upperBound_1180_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__8(lean_object* v_upperBound_1190_, lean_object* v_args_1191_, lean_object* v_inst_1192_, lean_object* v_R_1193_, lean_object* v_a_1194_, lean_object* v_b_1195_, lean_object* v_c_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__8___redArg(v_upperBound_1190_, v_args_1191_, v_a_1194_, v_b_1195_, v___y_1197_, v___y_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__8___boxed(lean_object* v_upperBound_1200_, lean_object* v_args_1201_, lean_object* v_inst_1202_, lean_object* v_R_1203_, lean_object* v_a_1204_, lean_object* v_b_1205_, lean_object* v_c_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__8(v_upperBound_1200_, v_args_1201_, v_inst_1202_, v_R_1203_, v_a_1204_, v_b_1205_, v_c_1206_, v___y_1207_, v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec_ref(v_args_1201_);
lean_dec(v_upperBound_1200_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__2(lean_object* v_00_u03b2_1210_, lean_object* v_m_1211_, lean_object* v_query_1212_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__2___redArg(v_m_1211_, v_query_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1214_, lean_object* v_m_1215_, lean_object* v_query_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__2(v_00_u03b2_1214_, v_m_1215_, v_query_1216_);
lean_dec_ref(v_query_1216_);
lean_dec_ref(v_m_1215_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4(lean_object* v_00_u03b2_1218_, lean_object* v_m_1219_, lean_object* v_query_1220_, lean_object* v_x_1221_, lean_object* v_x_1222_, lean_object* v_x_1223_, lean_object* v_x_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4___redArg(v_m_1219_, v_query_1220_, v_x_1221_, v_x_1222_, v_x_1223_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1226_, lean_object* v_m_1227_, lean_object* v_query_1228_, lean_object* v_x_1229_, lean_object* v_x_1230_, lean_object* v_x_1231_, lean_object* v_x_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4(v_00_u03b2_1226_, v_m_1227_, v_query_1228_, v_x_1229_, v_x_1230_, v_x_1231_, v_x_1232_);
lean_dec_ref(v_query_1228_);
lean_dec_ref(v_m_1227_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7(lean_object* v_00_u03b2_1234_, lean_object* v_init_1235_, lean_object* v_b_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7___redArg(v_init_1235_, v_b_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1238_, lean_object* v_init_1239_, lean_object* v_b_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7(v_00_u03b2_1238_, v_init_1239_, v_b_1240_);
lean_dec_ref(v_b_1240_);
return v_res_1241_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4_spec__6(lean_object* v_xs_1242_, lean_object* v_ys_1243_, lean_object* v_hsz_1244_, lean_object* v_x_1245_, lean_object* v_x_1246_){
_start:
{
uint8_t v___x_1247_; 
v___x_1247_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4_spec__6___redArg(v_xs_1242_, v_ys_1243_, v_x_1245_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4_spec__6___boxed(lean_object* v_xs_1248_, lean_object* v_ys_1249_, lean_object* v_hsz_1250_, lean_object* v_x_1251_, lean_object* v_x_1252_){
_start:
{
uint8_t v_res_1253_; lean_object* v_r_1254_; 
v_res_1253_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_spec__4_spec__6(v_xs_1248_, v_ys_1249_, v_hsz_1250_, v_x_1251_, v_x_1252_);
lean_dec_ref(v_ys_1249_);
lean_dec_ref(v_xs_1248_);
v_r_1254_ = lean_box(v_res_1253_);
return v_r_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_1255_, lean_object* v_b_1256_, lean_object* v_acc_1257_, lean_object* v_i_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7_spec__10___redArg(v_b_1256_, v_acc_1257_, v_i_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_1260_, lean_object* v_b_1261_, lean_object* v_acc_1262_, lean_object* v_i_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4_spec__7_spec__10(v_00_u03b2_1260_, v_b_1261_, v_acc_1262_, v_i_1263_);
lean_dec_ref(v_b_1261_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(lean_object* v_upperBound_1265_, lean_object* v_a_1266_, lean_object* v_b_1267_){
_start:
{
uint8_t v___x_1268_; 
v___x_1268_ = lean_nat_dec_lt(v_a_1266_, v_upperBound_1265_);
if (v___x_1268_ == 0)
{
lean_dec(v_a_1266_);
return v_b_1267_;
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
lean_inc(v_a_1266_);
v___x_1269_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1269_, 0, v_a_1266_);
v___x_1270_ = lean_array_push(v_b_1267_, v___x_1269_);
v___x_1271_ = lean_unsigned_to_nat(1u);
v___x_1272_ = lean_nat_add(v_a_1266_, v___x_1271_);
lean_dec(v_a_1266_);
v_a_1266_ = v___x_1272_;
v_b_1267_ = v___x_1270_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg___boxed(lean_object* v_upperBound_1274_, lean_object* v_a_1275_, lean_object* v_b_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_upperBound_1274_, v_a_1275_, v_b_1276_);
lean_dec(v_upperBound_1274_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(lean_object* v_numParams_1278_){
_start:
{
lean_object* v___x_1279_; lean_object* v_values_1280_; lean_object* v___x_1281_; 
v___x_1279_ = lean_unsigned_to_nat(0u);
v_values_1280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___closed__0));
v___x_1281_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_numParams_1278_, v___x_1279_, v_values_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkInitialValues___boxed(lean_object* v_numParams_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(v_numParams_1282_);
lean_dec(v_numParams_1282_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0(lean_object* v_upperBound_1284_, lean_object* v_inst_1285_, lean_object* v_R_1286_, lean_object* v_a_1287_, lean_object* v_b_1288_, lean_object* v_c_1289_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_upperBound_1284_, v_a_1287_, v_b_1288_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___boxed(lean_object* v_upperBound_1291_, lean_object* v_inst_1292_, lean_object* v_R_1293_, lean_object* v_a_1294_, lean_object* v_b_1295_, lean_object* v_c_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0(v_upperBound_1291_, v_inst_1292_, v_R_1293_, v_a_1294_, v_b_1295_, v_c_1296_);
lean_dec(v_upperBound_1291_);
return v_res_1297_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0(void){
_start:
{
lean_object* v_cellCount_1298_; lean_object* v___x_1299_; 
v_cellCount_1298_ = lean_unsigned_to_nat(16u);
v___x_1299_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1298_);
return v___x_1299_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1(void){
_start:
{
lean_object* v_cellCount_1300_; lean_object* v___x_1301_; 
v_cellCount_1300_ = lean_unsigned_to_nat(16u);
v___x_1301_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1300_);
return v___x_1301_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1302_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1);
v___x_1303_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0);
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v___x_1303_);
lean_ctor_set(v___x_1305_, 2, v___x_1302_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(lean_object* v_decls_1306_, lean_object* v_as_1307_, size_t v_sz_1308_, size_t v_i_1309_, lean_object* v_b_1310_){
_start:
{
lean_object* v_a_1312_; uint8_t v___x_1316_; 
v___x_1316_ = lean_usize_dec_lt(v_i_1309_, v_sz_1308_);
if (v___x_1316_ == 0)
{
lean_dec_ref(v_decls_1306_);
return v_b_1310_;
}
else
{
lean_object* v_a_1317_; lean_object* v_toSignature_1318_; lean_object* v_value_1319_; lean_object* v_name_1320_; lean_object* v_params_1321_; lean_object* v_s_1323_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v_a_1317_ = lean_array_uget_borrowed(v_as_1307_, v_i_1309_);
v_toSignature_1318_ = lean_ctor_get(v_a_1317_, 0);
v_value_1319_ = lean_ctor_get(v_a_1317_, 1);
v_name_1320_ = lean_ctor_get(v_toSignature_1318_, 0);
v_params_1321_ = lean_ctor_get(v_toSignature_1318_, 3);
v___x_1326_ = lean_array_get_size(v_params_1321_);
v___x_1327_ = l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(v___x_1326_);
v___x_1328_ = lean_box(v___x_1316_);
v___x_1329_ = lean_mk_array(v___x_1326_, v___x_1328_);
if (lean_obj_tag(v_value_1319_) == 0)
{
lean_object* v_code_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v_a_1336_; 
v_code_1330_ = lean_ctor_get(v_value_1319_, 0);
v___x_1331_ = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(v_a_1317_, v___x_1327_);
lean_inc(v_a_1317_);
lean_inc_ref(v_decls_1306_);
v___x_1332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1332_, 0, v_decls_1306_);
lean_ctor_set(v___x_1332_, 1, v_a_1317_);
lean_ctor_set(v___x_1332_, 2, v___x_1331_);
v___x_1333_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__2);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v___x_1329_);
lean_inc_ref(v_code_1330_);
v___x_1335_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_code_1330_, v___x_1332_, v___x_1334_);
v_a_1336_ = lean_ctor_get(v___x_1335_, 1);
lean_inc(v_a_1336_);
lean_dec_ref(v___x_1335_);
v_s_1323_ = v_a_1336_;
goto v___jp_1322_;
}
else
{
lean_object* v___x_1337_; 
lean_dec_ref(v___x_1327_);
lean_inc(v_name_1320_);
v___x_1337_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1320_, v___x_1329_, v_b_1310_);
v_a_1312_ = v___x_1337_;
goto v___jp_1311_;
}
v___jp_1322_:
{
lean_object* v_fixed_1324_; lean_object* v___x_1325_; 
v_fixed_1324_ = lean_ctor_get(v_s_1323_, 1);
lean_inc_ref(v_fixed_1324_);
lean_dec_ref(v_s_1323_);
lean_inc(v_name_1320_);
v___x_1325_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1320_, v_fixed_1324_, v_b_1310_);
v_a_1312_ = v___x_1325_;
goto v___jp_1311_;
}
}
v___jp_1311_:
{
size_t v___x_1313_; size_t v___x_1314_; 
v___x_1313_ = ((size_t)1ULL);
v___x_1314_ = lean_usize_add(v_i_1309_, v___x_1313_);
v_i_1309_ = v___x_1314_;
v_b_1310_ = v_a_1312_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___boxed(lean_object* v_decls_1338_, lean_object* v_as_1339_, lean_object* v_sz_1340_, lean_object* v_i_1341_, lean_object* v_b_1342_){
_start:
{
size_t v_sz_boxed_1343_; size_t v_i_boxed_1344_; lean_object* v_res_1345_; 
v_sz_boxed_1343_ = lean_unbox_usize(v_sz_1340_);
lean_dec(v_sz_1340_);
v_i_boxed_1344_ = lean_unbox_usize(v_i_1341_);
lean_dec(v_i_1341_);
v_res_1345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(v_decls_1338_, v_as_1339_, v_sz_boxed_1343_, v_i_boxed_1344_, v_b_1342_);
lean_dec_ref(v_as_1339_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFixedParamsMap(lean_object* v_decls_1346_){
_start:
{
lean_object* v_result_1347_; size_t v_sz_1348_; size_t v___x_1349_; lean_object* v___x_1350_; 
v_result_1347_ = lean_box(1);
v_sz_1348_ = lean_array_size(v_decls_1346_);
v___x_1349_ = ((size_t)0ULL);
lean_inc_ref(v_decls_1346_);
v___x_1350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(v_decls_1346_, v_decls_1346_, v_sz_1348_, v___x_1349_, v_result_1347_);
lean_dec_ref(v_decls_1346_);
return v___x_1350_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_FixedParams(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue_default = _init_l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue_default();
lean_mark_persistent(l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue_default);
l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue = _init_l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue();
lean_mark_persistent(l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_FixedParams(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_FixedParams(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_FixedParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_FixedParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_FixedParams(builtin);
}
#ifdef __cplusplus
}
#endif
