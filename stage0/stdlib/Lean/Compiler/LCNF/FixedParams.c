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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(uint8_t, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalLetValue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalCode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalLetValue___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFixedParamsMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 2)
{
lean_object* v_i_7_; lean_object* v___x_8_; 
v_i_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_i_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_i_7_);
return v___x_8_;
}
else
{
lean_dec(v_t_5_);
return v_k_6_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_top_elim___redArg(lean_object* v_t_21_, lean_object* v_top_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_21_, v_top_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_top_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_top_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_25_, v_top_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_erased_elim___redArg(lean_object* v_t_29_, lean_object* v_erased_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_29_, v_erased_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_erased_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_erased_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_33_, v_erased_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_val_elim___redArg(lean_object* v_t_37_, lean_object* v_val_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_37_, v_val_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_AbsValue_val_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_val_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_41_, v_val_43_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue_default(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue(void){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_box(0);
return v___x_46_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(lean_object* v_x_47_, lean_object* v_x_48_){
_start:
{
switch(lean_obj_tag(v_x_47_))
{
case 0:
{
if (lean_obj_tag(v_x_48_) == 0)
{
uint8_t v___x_49_; 
v___x_49_ = 1;
return v___x_49_;
}
else
{
uint8_t v___x_50_; 
v___x_50_ = 0;
return v___x_50_;
}
}
case 1:
{
if (lean_obj_tag(v_x_48_) == 1)
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
default: 
{
if (lean_obj_tag(v_x_48_) == 2)
{
lean_object* v_i_53_; lean_object* v_i_54_; uint8_t v___x_55_; 
v_i_53_ = lean_ctor_get(v_x_47_, 0);
v_i_54_ = lean_ctor_get(v_x_48_, 0);
v___x_55_ = lean_nat_dec_eq(v_i_53_, v_i_54_);
return v___x_55_;
}
else
{
uint8_t v___x_56_; 
v___x_56_ = 0;
return v___x_56_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq___boxed(lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v_x_57_, v_x_58_);
lean_dec(v_x_58_);
lean_dec(v_x_57_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash(lean_object* v_x_63_){
_start:
{
switch(lean_obj_tag(v_x_63_))
{
case 0:
{
uint64_t v___x_64_; 
v___x_64_ = 0ULL;
return v___x_64_;
}
case 1:
{
uint64_t v___x_65_; 
v___x_65_ = 1ULL;
return v___x_65_;
}
default: 
{
lean_object* v_i_66_; uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v___x_69_; 
v_i_66_ = lean_ctor_get(v_x_63_, 0);
v___x_67_ = 2ULL;
v___x_68_ = lean_uint64_of_nat(v_i_66_);
v___x_69_ = lean_uint64_mix_hash(v___x_67_, v___x_68_);
return v___x_69_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash___boxed(lean_object* v_x_70_){
_start:
{
uint64_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash(v_x_70_);
lean_dec(v_x_70_);
v_r_72_ = lean_box_uint64(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FixedParams_abort___redArg___lam__0(uint8_t v_x_75_){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = 0;
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___redArg___lam__0___boxed(lean_object* v_x_77_){
_start:
{
uint8_t v_x_273__boxed_78_; uint8_t v_res_79_; lean_object* v_r_80_; 
v_x_273__boxed_78_ = lean_unbox(v_x_77_);
v_res_79_ = l_Lean_Compiler_LCNF_FixedParams_abort___redArg___lam__0(v_x_273__boxed_78_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___redArg(lean_object* v_a_101_){
_start:
{
lean_object* v_visited_102_; lean_object* v_fixed_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_117_; 
v_visited_102_ = lean_ctor_get(v_a_101_, 0);
v_fixed_103_ = lean_ctor_get(v_a_101_, 1);
v_isSharedCheck_117_ = !lean_is_exclusive(v_a_101_);
if (v_isSharedCheck_117_ == 0)
{
v___x_105_ = v_a_101_;
v_isShared_106_ = v_isSharedCheck_117_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_fixed_103_);
lean_inc(v_visited_102_);
lean_dec(v_a_101_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_117_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___f_107_; lean_object* v___x_108_; size_t v_sz_109_; size_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
v___f_107_ = ((lean_object*)(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__0));
v___x_108_ = ((lean_object*)(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__10));
v_sz_109_ = lean_array_size(v_fixed_103_);
v___x_110_ = ((size_t)0ULL);
v___x_111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_108_, v___f_107_, v_sz_109_, v___x_110_, v_fixed_103_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v___x_111_);
v___x_113_ = v___x_105_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_visited_102_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v___x_111_);
v___x_113_ = v_reuseFailAlloc_116_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_box(0);
v___x_115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_113_);
return v___x_115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort(lean_object* v_00_u03b1_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_visited_121_; lean_object* v_fixed_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_136_; 
v_visited_121_ = lean_ctor_get(v_a_120_, 0);
v_fixed_122_ = lean_ctor_get(v_a_120_, 1);
v_isSharedCheck_136_ = !lean_is_exclusive(v_a_120_);
if (v_isSharedCheck_136_ == 0)
{
v___x_124_ = v_a_120_;
v_isShared_125_ = v_isSharedCheck_136_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_fixed_122_);
lean_inc(v_visited_121_);
lean_dec(v_a_120_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_136_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___f_126_; lean_object* v___x_127_; size_t v_sz_128_; size_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_132_; 
v___f_126_ = ((lean_object*)(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__0));
v___x_127_ = ((lean_object*)(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__10));
v_sz_128_ = lean_array_size(v_fixed_122_);
v___x_129_ = ((size_t)0ULL);
v___x_130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_127_, v___f_126_, v_sz_128_, v___x_129_, v_fixed_122_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v___x_130_);
v___x_132_ = v___x_124_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_visited_121_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___x_130_);
v___x_132_ = v_reuseFailAlloc_135_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_box(0);
v___x_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_132_);
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___boxed(lean_object* v_00_u03b1_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Compiler_LCNF_FixedParams_abort(v_00_u03b1_137_, v_a_138_, v_a_139_);
lean_dec_ref(v_a_138_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(lean_object* v_t_141_, lean_object* v_k_142_){
_start:
{
if (lean_obj_tag(v_t_141_) == 0)
{
lean_object* v_k_143_; lean_object* v_v_144_; lean_object* v_l_145_; lean_object* v_r_146_; uint8_t v___x_147_; 
v_k_143_ = lean_ctor_get(v_t_141_, 1);
v_v_144_ = lean_ctor_get(v_t_141_, 2);
v_l_145_ = lean_ctor_get(v_t_141_, 3);
v_r_146_ = lean_ctor_get(v_t_141_, 4);
v___x_147_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_142_, v_k_143_);
switch(v___x_147_)
{
case 0:
{
v_t_141_ = v_l_145_;
goto _start;
}
case 1:
{
lean_object* v___x_149_; 
lean_inc(v_v_144_);
v___x_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_149_, 0, v_v_144_);
return v___x_149_;
}
default: 
{
v_t_141_ = v_r_146_;
goto _start;
}
}
}
else
{
lean_object* v___x_151_; 
v___x_151_ = lean_box(0);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg___boxed(lean_object* v_t_152_, lean_object* v_k_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(v_t_152_, v_k_153_);
lean_dec(v_k_153_);
lean_dec(v_t_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalFVar(lean_object* v_fvarId_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_assignment_158_; lean_object* v___x_159_; 
v_assignment_158_ = lean_ctor_get(v_a_156_, 2);
v___x_159_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(v_assignment_158_, v_fvarId_155_);
if (lean_obj_tag(v___x_159_) == 1)
{
lean_object* v_val_160_; lean_object* v___x_161_; 
v_val_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_val_160_);
lean_dec_ref_known(v___x_159_, 1);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v_val_160_);
lean_ctor_set(v___x_161_, 1, v_a_157_);
return v___x_161_;
}
else
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec(v___x_159_);
v___x_162_ = lean_box(0);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v_a_157_);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalFVar___boxed(lean_object* v_fvarId_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_Compiler_LCNF_FixedParams_evalFVar(v_fvarId_164_, v_a_165_, v_a_166_);
lean_dec_ref(v_a_165_);
lean_dec(v_fvarId_164_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0(lean_object* v_00_u03b4_168_, lean_object* v_t_169_, lean_object* v_k_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(v_t_169_, v_k_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___boxed(lean_object* v_00_u03b4_172_, lean_object* v_t_173_, lean_object* v_k_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0(v_00_u03b4_172_, v_t_173_, v_k_174_);
lean_dec(v_k_174_);
lean_dec(v_t_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalArg(lean_object* v_arg_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
switch(lean_obj_tag(v_arg_176_))
{
case 0:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_box(1);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v_a_178_);
return v___x_180_;
}
case 1:
{
lean_object* v_fvarId_181_; lean_object* v___x_182_; 
v_fvarId_181_ = lean_ctor_get(v_arg_176_, 0);
v___x_182_ = l_Lean_Compiler_LCNF_FixedParams_evalFVar(v_fvarId_181_, v_a_177_, v_a_178_);
return v___x_182_;
}
default: 
{
lean_object* v_expr_183_; 
v_expr_183_ = lean_ctor_get(v_arg_176_, 0);
if (lean_obj_tag(v_expr_183_) == 1)
{
lean_object* v_fvarId_184_; lean_object* v___x_185_; 
v_fvarId_184_ = lean_ctor_get(v_expr_183_, 0);
v___x_185_ = l_Lean_Compiler_LCNF_FixedParams_evalFVar(v_fvarId_184_, v_a_177_, v_a_178_);
return v___x_185_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_box(0);
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v_a_178_);
return v___x_187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalArg___boxed(lean_object* v_arg_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Compiler_LCNF_FixedParams_evalArg(v_arg_188_, v_a_189_, v_a_190_);
lean_dec_ref(v_a_189_);
lean_dec(v_arg_188_);
return v_res_191_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0(lean_object* v_declName_192_, lean_object* v_as_193_, size_t v_i_194_, size_t v_stop_195_){
_start:
{
uint8_t v___x_196_; 
v___x_196_ = lean_usize_dec_eq(v_i_194_, v_stop_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v_toSignature_198_; lean_object* v_name_199_; uint8_t v___x_200_; 
v___x_197_ = lean_array_uget_borrowed(v_as_193_, v_i_194_);
v_toSignature_198_ = lean_ctor_get(v___x_197_, 0);
v_name_199_ = lean_ctor_get(v_toSignature_198_, 0);
v___x_200_ = lean_name_eq(v_name_199_, v_declName_192_);
if (v___x_200_ == 0)
{
size_t v___x_201_; size_t v___x_202_; 
v___x_201_ = ((size_t)1ULL);
v___x_202_ = lean_usize_add(v_i_194_, v___x_201_);
v_i_194_ = v___x_202_;
goto _start;
}
else
{
return v___x_200_;
}
}
else
{
uint8_t v___x_204_; 
v___x_204_ = 0;
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0___boxed(lean_object* v_declName_205_, lean_object* v_as_206_, lean_object* v_i_207_, lean_object* v_stop_208_){
_start:
{
size_t v_i_boxed_209_; size_t v_stop_boxed_210_; uint8_t v_res_211_; lean_object* v_r_212_; 
v_i_boxed_209_ = lean_unbox_usize(v_i_207_);
lean_dec(v_i_207_);
v_stop_boxed_210_ = lean_unbox_usize(v_stop_208_);
lean_dec(v_stop_208_);
v_res_211_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0(v_declName_205_, v_as_206_, v_i_boxed_209_, v_stop_boxed_210_);
lean_dec_ref(v_as_206_);
lean_dec(v_declName_205_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_inMutualBlock(lean_object* v_declName_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_decls_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v_decls_216_ = lean_ctor_get(v_a_214_, 0);
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_array_get_size(v_decls_216_);
v___x_219_ = lean_nat_dec_lt(v___x_217_, v___x_218_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_box(v___x_219_);
v___x_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v_a_215_);
return v___x_221_;
}
else
{
if (v___x_219_ == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_box(v___x_219_);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v_a_215_);
return v___x_223_;
}
else
{
size_t v___x_224_; size_t v___x_225_; uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_224_ = ((size_t)0ULL);
v___x_225_ = lean_usize_of_nat(v___x_218_);
v___x_226_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0(v_declName_213_, v_decls_216_, v___x_224_, v___x_225_);
v___x_227_ = lean_box(v___x_226_);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v_a_215_);
return v___x_228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_inMutualBlock___boxed(lean_object* v_declName_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Compiler_LCNF_FixedParams_inMutualBlock(v_declName_229_, v_a_230_, v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_declName_229_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0(lean_object* v_as_233_, size_t v_sz_234_, size_t v_i_235_, lean_object* v_b_236_){
_start:
{
uint8_t v___x_237_; 
v___x_237_ = lean_usize_dec_lt(v_i_235_, v_sz_234_);
if (v___x_237_ == 0)
{
return v_b_236_;
}
else
{
lean_object* v_snd_238_; lean_object* v_fst_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_272_; 
v_snd_238_ = lean_ctor_get(v_b_236_, 1);
v_fst_239_ = lean_ctor_get(v_b_236_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v_b_236_);
if (v_isSharedCheck_272_ == 0)
{
v___x_241_ = v_b_236_;
v_isShared_242_ = v_isSharedCheck_272_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_snd_238_);
lean_inc(v_fst_239_);
lean_dec(v_b_236_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_272_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v_array_243_; lean_object* v_start_244_; lean_object* v_stop_245_; uint8_t v___x_246_; 
v_array_243_ = lean_ctor_get(v_snd_238_, 0);
v_start_244_ = lean_ctor_get(v_snd_238_, 1);
v_stop_245_ = lean_ctor_get(v_snd_238_, 2);
v___x_246_ = lean_nat_dec_lt(v_start_244_, v_stop_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_248_; 
if (v_isShared_242_ == 0)
{
v___x_248_ = v___x_241_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_fst_239_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_snd_238_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
else
{
lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_268_; 
lean_inc(v_stop_245_);
lean_inc(v_start_244_);
lean_inc_ref(v_array_243_);
v_isSharedCheck_268_ = !lean_is_exclusive(v_snd_238_);
if (v_isSharedCheck_268_ == 0)
{
lean_object* v_unused_269_; lean_object* v_unused_270_; lean_object* v_unused_271_; 
v_unused_269_ = lean_ctor_get(v_snd_238_, 2);
lean_dec(v_unused_269_);
v_unused_270_ = lean_ctor_get(v_snd_238_, 1);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v_snd_238_, 0);
lean_dec(v_unused_271_);
v___x_251_ = v_snd_238_;
v_isShared_252_ = v_isSharedCheck_268_;
goto v_resetjp_250_;
}
else
{
lean_dec(v_snd_238_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_268_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v_a_253_; lean_object* v_fvarId_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v_a_253_ = lean_array_uget_borrowed(v_as_233_, v_i_235_);
v_fvarId_254_ = lean_ctor_get(v_a_253_, 0);
v___x_255_ = lean_array_fget(v_array_243_, v_start_244_);
v___x_256_ = lean_unsigned_to_nat(1u);
v___x_257_ = lean_nat_add(v_start_244_, v___x_256_);
lean_dec(v_start_244_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v___x_257_);
v___x_259_ = v___x_251_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_array_243_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_267_, 2, v_stop_245_);
v___x_259_ = v_reuseFailAlloc_267_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; lean_object* v___x_262_; 
lean_inc(v_fvarId_254_);
v___x_260_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_254_, v___x_255_, v_fst_239_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v___x_259_);
lean_ctor_set(v___x_241_, 0, v___x_260_);
v___x_262_ = v___x_241_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v___x_259_);
v___x_262_ = v_reuseFailAlloc_266_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
size_t v___x_263_; size_t v___x_264_; 
v___x_263_ = ((size_t)1ULL);
v___x_264_ = lean_usize_add(v_i_235_, v___x_263_);
v_i_235_ = v___x_264_;
v_b_236_ = v___x_262_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0___boxed(lean_object* v_as_273_, lean_object* v_sz_274_, lean_object* v_i_275_, lean_object* v_b_276_){
_start:
{
size_t v_sz_boxed_277_; size_t v_i_boxed_278_; lean_object* v_res_279_; 
v_sz_boxed_277_ = lean_unbox_usize(v_sz_274_);
lean_dec(v_sz_274_);
v_i_boxed_278_ = lean_unbox_usize(v_i_275_);
lean_dec(v_i_275_);
v_res_279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0(v_as_273_, v_sz_boxed_277_, v_i_boxed_278_, v_b_276_);
lean_dec_ref(v_as_273_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkAssignment(lean_object* v_decl_280_, lean_object* v_values_281_){
_start:
{
lean_object* v_toSignature_282_; lean_object* v_params_283_; lean_object* v___x_284_; lean_object* v_assignment_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; size_t v_sz_289_; size_t v___x_290_; lean_object* v___x_291_; lean_object* v_fst_292_; 
v_toSignature_282_ = lean_ctor_get(v_decl_280_, 0);
v_params_283_ = lean_ctor_get(v_toSignature_282_, 3);
v___x_284_ = lean_array_get_size(v_values_281_);
v_assignment_285_ = lean_box(1);
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = l_Array_toSubarray___redArg(v_values_281_, v___x_286_, v___x_284_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v_assignment_285_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v_sz_289_ = lean_array_size(v_params_283_);
v___x_290_ = ((size_t)0ULL);
v___x_291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0(v_params_283_, v_sz_289_, v___x_290_, v___x_288_);
v_fst_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_fst_292_);
lean_dec_ref(v___x_291_);
return v_fst_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkAssignment___boxed(lean_object* v_decl_293_, lean_object* v_values_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(v_decl_293_, v_values_294_);
lean_dec_ref(v_decl_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(lean_object* v_params_304_, lean_object* v_args_305_, lean_object* v_range_306_, lean_object* v_b_307_, lean_object* v_i_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_stop_310_; lean_object* v_step_311_; uint8_t v___x_312_; 
v_stop_310_ = lean_ctor_get(v_range_306_, 1);
v_step_311_ = lean_ctor_get(v_range_306_, 2);
v___x_312_ = lean_nat_dec_lt(v_i_308_, v_stop_310_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; 
lean_dec(v_i_308_);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v_b_307_);
lean_ctor_set(v___x_313_, 1, v___y_309_);
return v___x_313_;
}
else
{
lean_object* v___x_314_; lean_object* v_fvarId_315_; lean_object* v___x_316_; lean_object* v_a_318_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
lean_dec_ref(v_b_307_);
v___x_314_ = lean_array_fget_borrowed(v_params_304_, v_i_308_);
v_fvarId_315_ = lean_ctor_get(v___x_314_, 0);
v___x_316_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__0));
v___x_321_ = lean_box(0);
v___x_322_ = lean_array_get_borrowed(v___x_321_, v_args_305_, v_i_308_);
lean_inc(v_fvarId_315_);
v___x_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_323_, 0, v_fvarId_315_);
v___x_324_ = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(v___x_322_, v___x_323_);
lean_dec_ref_known(v___x_323_, 1);
if (v___x_324_ == 0)
{
uint8_t v___x_325_; 
v___x_325_ = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(v___x_322_, v___x_321_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; 
lean_dec(v_i_308_);
v___x_326_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__2));
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v___y_309_);
return v___x_327_;
}
else
{
v_a_318_ = v___y_309_;
goto v___jp_317_;
}
}
else
{
v_a_318_ = v___y_309_;
goto v___jp_317_;
}
v___jp_317_:
{
lean_object* v___x_319_; 
v___x_319_ = lean_nat_add(v_i_308_, v_step_311_);
lean_dec(v_i_308_);
v_b_307_ = v___x_316_;
v_i_308_ = v___x_319_;
v___y_309_ = v_a_318_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___boxed(lean_object* v_params_328_, lean_object* v_args_329_, lean_object* v_range_330_, lean_object* v_b_331_, lean_object* v_i_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_328_, v_args_329_, v_range_330_, v_b_331_, v_i_332_, v___y_333_);
lean_dec_ref(v_range_330_);
lean_dec_ref(v_args_329_);
lean_dec_ref(v_params_328_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(lean_object* v_decl_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v___y_339_; lean_object* v___y_343_; lean_object* v_value_346_; 
v_value_346_ = lean_ctor_get(v_decl_335_, 4);
lean_inc_ref(v_value_346_);
if (lean_obj_tag(v_value_346_) == 0)
{
lean_object* v_decl_347_; lean_object* v_value_348_; 
v_decl_347_ = lean_ctor_get(v_value_346_, 0);
lean_inc_ref(v_decl_347_);
v_value_348_ = lean_ctor_get(v_decl_347_, 3);
lean_inc(v_value_348_);
if (lean_obj_tag(v_value_348_) == 4)
{
lean_object* v_params_349_; lean_object* v_k_350_; lean_object* v_fvarId_351_; lean_object* v_fvarId_352_; lean_object* v_args_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_411_; 
v_params_349_ = lean_ctor_get(v_decl_335_, 2);
lean_inc_ref(v_params_349_);
lean_dec_ref(v_decl_335_);
v_k_350_ = lean_ctor_get(v_value_346_, 1);
lean_inc_ref(v_k_350_);
lean_dec_ref_known(v_value_346_, 2);
v_fvarId_351_ = lean_ctor_get(v_decl_347_, 0);
lean_inc(v_fvarId_351_);
lean_dec_ref(v_decl_347_);
v_fvarId_352_ = lean_ctor_get(v_value_348_, 0);
v_args_353_ = lean_ctor_get(v_value_348_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v_value_348_);
if (v_isSharedCheck_411_ == 0)
{
v___x_355_ = v_value_348_;
v_isShared_356_ = v_isSharedCheck_411_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_args_353_);
lean_inc(v_fvarId_352_);
lean_dec(v_value_348_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_411_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_357_ = lean_array_get_size(v_args_353_);
v___x_358_ = lean_array_get_size(v_params_349_);
v___x_359_ = lean_nat_dec_eq(v___x_357_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_362_; 
lean_dec_ref(v_args_353_);
lean_dec(v_fvarId_352_);
lean_dec(v_fvarId_351_);
lean_dec_ref(v_k_350_);
lean_dec_ref(v_params_349_);
v___x_360_ = lean_box(0);
if (v_isShared_356_ == 0)
{
lean_ctor_set_tag(v___x_355_, 0);
lean_ctor_set(v___x_355_, 1, v_a_337_);
lean_ctor_set(v___x_355_, 0, v___x_360_);
v___x_362_ = v___x_355_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_a_337_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
else
{
if (lean_obj_tag(v_k_350_) == 5)
{
lean_object* v_fvarId_364_; uint8_t v___x_365_; 
v_fvarId_364_ = lean_ctor_get(v_k_350_, 0);
lean_inc(v_fvarId_364_);
lean_dec_ref_known(v_k_350_, 1);
v___x_365_ = l_Lean_instBEqFVarId_beq(v_fvarId_364_, v_fvarId_351_);
lean_dec(v_fvarId_351_);
lean_dec(v_fvarId_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; lean_object* v___x_368_; 
lean_dec_ref(v_args_353_);
lean_dec(v_fvarId_352_);
lean_dec_ref(v_params_349_);
v___x_366_ = lean_box(0);
if (v_isShared_356_ == 0)
{
lean_ctor_set_tag(v___x_355_, 0);
lean_ctor_set(v___x_355_, 1, v_a_337_);
lean_ctor_set(v___x_355_, 0, v___x_366_);
v___x_368_ = v___x_355_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_a_337_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
else
{
lean_object* v_assignment_370_; lean_object* v___x_371_; 
lean_del_object(v___x_355_);
v_assignment_370_ = lean_ctor_get(v_a_336_, 2);
v___x_371_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(v_assignment_370_, v_fvarId_352_);
lean_dec(v_fvarId_352_);
if (lean_obj_tag(v___x_371_) == 1)
{
lean_object* v_val_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_406_; 
v_val_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_406_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_406_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_val_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_406_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
if (lean_obj_tag(v_val_372_) == 2)
{
lean_object* v_i_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v_a_382_; lean_object* v_fst_383_; 
v_i_376_ = lean_ctor_get(v_val_372_, 0);
lean_inc(v_i_376_);
lean_dec_ref_known(v_val_372_, 1);
v___x_377_ = lean_unsigned_to_nat(0u);
v___x_378_ = lean_unsigned_to_nat(1u);
v___x_379_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_379_, 0, v___x_377_);
lean_ctor_set(v___x_379_, 1, v___x_358_);
lean_ctor_set(v___x_379_, 2, v___x_378_);
v___x_380_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__0));
v___x_381_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_349_, v_args_353_, v___x_379_, v___x_380_, v___x_377_, v_a_337_);
lean_dec_ref_known(v___x_379_, 3);
lean_dec_ref(v_args_353_);
lean_dec_ref(v_params_349_);
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_fst_383_ = lean_ctor_get(v_a_382_, 0);
if (lean_obj_tag(v_fst_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_394_; 
v_a_384_ = lean_ctor_get(v___x_381_, 1);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_394_ == 0)
{
lean_object* v_unused_395_; 
v_unused_395_ = lean_ctor_get(v___x_381_, 0);
lean_dec(v_unused_395_);
v___x_386_ = v___x_381_;
v_isShared_387_ = v_isSharedCheck_394_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_381_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_394_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v_i_376_);
v___x_389_ = v___x_374_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_i_376_);
v___x_389_ = v_reuseFailAlloc_393_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_391_; 
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v___x_389_);
v___x_391_ = v___x_386_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_389_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_a_384_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_404_; 
lean_inc_ref(v_fst_383_);
lean_dec(v_i_376_);
lean_del_object(v___x_374_);
v_a_396_ = lean_ctor_get(v___x_381_, 1);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_404_ == 0)
{
lean_object* v_unused_405_; 
v_unused_405_ = lean_ctor_get(v___x_381_, 0);
lean_dec(v_unused_405_);
v___x_398_ = v___x_381_;
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_381_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v_val_400_; lean_object* v___x_402_; 
v_val_400_ = lean_ctor_get(v_fst_383_, 0);
lean_inc(v_val_400_);
lean_dec_ref_known(v_fst_383_, 1);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v_val_400_);
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_val_400_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_a_396_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
else
{
lean_del_object(v___x_374_);
lean_dec(v_val_372_);
lean_dec_ref(v_args_353_);
lean_dec_ref(v_params_349_);
v___y_343_ = v_a_337_;
goto v___jp_342_;
}
}
}
else
{
lean_dec(v___x_371_);
lean_dec_ref(v_args_353_);
lean_dec_ref(v_params_349_);
v___y_343_ = v_a_337_;
goto v___jp_342_;
}
}
}
else
{
lean_object* v___x_407_; lean_object* v___x_409_; 
lean_dec_ref(v_args_353_);
lean_dec(v_fvarId_352_);
lean_dec(v_fvarId_351_);
lean_dec_ref(v_k_350_);
lean_dec_ref(v_params_349_);
v___x_407_ = lean_box(0);
if (v_isShared_356_ == 0)
{
lean_ctor_set_tag(v___x_355_, 0);
lean_ctor_set(v___x_355_, 1, v_a_337_);
lean_ctor_set(v___x_355_, 0, v___x_407_);
v___x_409_ = v___x_355_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_a_337_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
else
{
lean_dec(v_value_348_);
lean_dec_ref_known(v_value_346_, 2);
lean_dec_ref(v_decl_347_);
lean_dec_ref(v_decl_335_);
v___y_339_ = v_a_337_;
goto v___jp_338_;
}
}
else
{
lean_dec_ref(v_value_346_);
lean_dec_ref(v_decl_335_);
v___y_339_ = v_a_337_;
goto v___jp_338_;
}
v___jp_338_:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_box(0);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___y_339_);
return v___x_341_;
}
v___jp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_box(0);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___y_343_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f___boxed(lean_object* v_decl_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(v_decl_412_, v_a_413_, v_a_414_);
lean_dec_ref(v_a_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0(lean_object* v_params_416_, lean_object* v_args_417_, lean_object* v_range_418_, lean_object* v_b_419_, lean_object* v_i_420_, lean_object* v_hs_421_, lean_object* v_hl_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_416_, v_args_417_, v_range_418_, v_b_419_, v_i_420_, v___y_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___boxed(lean_object* v_params_426_, lean_object* v_args_427_, lean_object* v_range_428_, lean_object* v_b_429_, lean_object* v_i_430_, lean_object* v_hs_431_, lean_object* v_hl_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0(v_params_426_, v_args_427_, v_range_428_, v_b_429_, v_i_430_, v_hs_431_, v_hl_432_, v___y_433_, v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec_ref(v_range_428_);
lean_dec_ref(v_args_427_);
lean_dec_ref(v_params_426_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(lean_object* v_upperBound_436_, lean_object* v_args_437_, lean_object* v_a_438_, lean_object* v_b_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_a_443_; lean_object* v_a_444_; uint8_t v___x_448_; 
v___x_448_ = lean_nat_dec_lt(v_a_438_, v_upperBound_436_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; 
lean_dec(v_a_438_);
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v_b_439_);
lean_ctor_set(v___x_449_, 1, v___y_441_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_450_ = lean_box(0);
v___x_451_ = lean_array_get_size(v_args_437_);
v___x_452_ = lean_nat_dec_lt(v_a_438_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v_visited_453_; lean_object* v_fixed_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_463_; 
v_visited_453_ = lean_ctor_get(v___y_441_, 0);
v_fixed_454_ = lean_ctor_get(v___y_441_, 1);
v_isSharedCheck_463_ = !lean_is_exclusive(v___y_441_);
if (v_isSharedCheck_463_ == 0)
{
v___x_456_ = v___y_441_;
v_isShared_457_ = v_isSharedCheck_463_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_fixed_454_);
lean_inc(v_visited_453_);
lean_dec(v___y_441_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_463_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_458_ = lean_box(v___x_452_);
v___x_459_ = lean_array_set(v_fixed_454_, v_a_438_, v___x_458_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 1, v___x_459_);
v___x_461_ = v___x_456_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_visited_453_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
v_a_443_ = v___x_450_;
v_a_444_ = v___x_461_;
goto v___jp_442_;
}
}
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_array_fget_borrowed(v_args_437_, v_a_438_);
v___x_465_ = l_Lean_Compiler_LCNF_FixedParams_evalArg(v___x_464_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v_a_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
v_a_467_ = lean_ctor_get(v___x_465_, 1);
lean_inc(v_a_467_);
lean_dec_ref_known(v___x_465_, 2);
lean_inc(v_a_438_);
v___x_468_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_468_, 0, v_a_438_);
v___x_469_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v_a_466_, v___x_468_);
lean_dec_ref_known(v___x_468_, 1);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = lean_box(1);
v___x_471_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v_a_466_, v___x_470_);
lean_dec(v_a_466_);
if (v___x_471_ == 0)
{
lean_object* v_visited_472_; lean_object* v_fixed_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_482_; 
v_visited_472_ = lean_ctor_get(v_a_467_, 0);
v_fixed_473_ = lean_ctor_get(v_a_467_, 1);
v_isSharedCheck_482_ = !lean_is_exclusive(v_a_467_);
if (v_isSharedCheck_482_ == 0)
{
v___x_475_ = v_a_467_;
v_isShared_476_ = v_isSharedCheck_482_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_fixed_473_);
lean_inc(v_visited_472_);
lean_dec(v_a_467_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_482_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_477_ = lean_box(v___x_471_);
v___x_478_ = lean_array_set(v_fixed_473_, v_a_438_, v___x_477_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 1, v___x_478_);
v___x_480_ = v___x_475_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_visited_472_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
v_a_443_ = v___x_450_;
v_a_444_ = v___x_480_;
goto v___jp_442_;
}
}
}
else
{
v_a_443_ = v___x_450_;
v_a_444_ = v_a_467_;
goto v___jp_442_;
}
}
else
{
lean_dec(v_a_466_);
v_a_443_ = v___x_450_;
v_a_444_ = v_a_467_;
goto v___jp_442_;
}
}
else
{
lean_object* v_a_483_; lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec(v_a_438_);
v_a_483_ = lean_ctor_get(v___x_465_, 0);
v_a_484_ = lean_ctor_get(v___x_465_, 1);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_465_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_inc(v_a_483_);
lean_dec(v___x_465_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_483_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
v___jp_442_:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = lean_nat_add(v_a_438_, v___x_445_);
lean_dec(v_a_438_);
v_a_438_ = v___x_446_;
v_b_439_ = v_a_443_;
v___y_441_ = v_a_444_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg___boxed(lean_object* v_upperBound_492_, lean_object* v_args_493_, lean_object* v_a_494_, lean_object* v_b_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(v_upperBound_492_, v_args_493_, v_a_494_, v_b_495_, v___y_496_, v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec_ref(v_args_493_);
lean_dec(v_upperBound_492_);
return v_res_498_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(lean_object* v_xs_499_, lean_object* v_ys_500_, lean_object* v_x_501_){
_start:
{
lean_object* v_zero_502_; uint8_t v_isZero_503_; 
v_zero_502_ = lean_unsigned_to_nat(0u);
v_isZero_503_ = lean_nat_dec_eq(v_x_501_, v_zero_502_);
if (v_isZero_503_ == 1)
{
lean_dec(v_x_501_);
return v_isZero_503_;
}
else
{
lean_object* v_one_504_; lean_object* v_n_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_one_504_ = lean_unsigned_to_nat(1u);
v_n_505_ = lean_nat_sub(v_x_501_, v_one_504_);
lean_dec(v_x_501_);
v___x_506_ = lean_array_fget_borrowed(v_xs_499_, v_n_505_);
v___x_507_ = lean_array_fget_borrowed(v_ys_500_, v_n_505_);
v___x_508_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_dec(v_n_505_);
return v___x_508_;
}
else
{
v_x_501_ = v_n_505_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_xs_510_, lean_object* v_ys_511_, lean_object* v_x_512_){
_start:
{
uint8_t v_res_513_; lean_object* v_r_514_; 
v_res_513_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(v_xs_510_, v_ys_511_, v_x_512_);
lean_dec_ref(v_ys_511_);
lean_dec_ref(v_xs_510_);
v_r_514_ = lean_box(v_res_513_);
return v_r_514_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(lean_object* v_a_515_, lean_object* v_x_516_){
_start:
{
if (lean_obj_tag(v_x_516_) == 0)
{
uint8_t v___x_517_; 
v___x_517_ = 0;
return v___x_517_;
}
else
{
lean_object* v_key_518_; lean_object* v_tail_519_; lean_object* v_fst_520_; lean_object* v_snd_521_; lean_object* v_fst_522_; lean_object* v_snd_523_; uint8_t v___x_524_; 
v_key_518_ = lean_ctor_get(v_x_516_, 0);
v_tail_519_ = lean_ctor_get(v_x_516_, 2);
v_fst_520_ = lean_ctor_get(v_key_518_, 0);
v_snd_521_ = lean_ctor_get(v_key_518_, 1);
v_fst_522_ = lean_ctor_get(v_a_515_, 0);
v_snd_523_ = lean_ctor_get(v_a_515_, 1);
v___x_524_ = lean_name_eq(v_fst_520_, v_fst_522_);
if (v___x_524_ == 0)
{
v_x_516_ = v_tail_519_;
goto _start;
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_526_ = lean_array_get_size(v_snd_521_);
v___x_527_ = lean_array_get_size(v_snd_523_);
v___x_528_ = lean_nat_dec_eq(v___x_526_, v___x_527_);
if (v___x_528_ == 0)
{
v_x_516_ = v_tail_519_;
goto _start;
}
else
{
uint8_t v___x_530_; 
v___x_530_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(v_snd_521_, v_snd_523_, v___x_526_);
if (v___x_530_ == 0)
{
v_x_516_ = v_tail_519_;
goto _start;
}
else
{
return v___x_530_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg___boxed(lean_object* v_a_532_, lean_object* v_x_533_){
_start:
{
uint8_t v_res_534_; lean_object* v_r_535_; 
v_res_534_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_532_, v_x_533_);
lean_dec(v_x_533_);
lean_dec_ref(v_a_532_);
v_r_535_ = lean_box(v_res_534_);
return v_r_535_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(lean_object* v_as_536_, size_t v_i_537_, size_t v_stop_538_, uint64_t v_b_539_){
_start:
{
uint8_t v___x_540_; 
v___x_540_ = lean_usize_dec_eq(v_i_537_, v_stop_538_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; uint64_t v___x_542_; uint64_t v___x_543_; size_t v___x_544_; size_t v___x_545_; 
v___x_541_ = lean_array_uget_borrowed(v_as_536_, v_i_537_);
v___x_542_ = l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash(v___x_541_);
v___x_543_ = lean_uint64_mix_hash(v_b_539_, v___x_542_);
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_add(v_i_537_, v___x_544_);
v_i_537_ = v___x_545_;
v_b_539_ = v___x_543_;
goto _start;
}
else
{
return v_b_539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2___boxed(lean_object* v_as_547_, lean_object* v_i_548_, lean_object* v_stop_549_, lean_object* v_b_550_){
_start:
{
size_t v_i_boxed_551_; size_t v_stop_boxed_552_; uint64_t v_b_boxed_553_; uint64_t v_res_554_; lean_object* v_r_555_; 
v_i_boxed_551_ = lean_unbox_usize(v_i_548_);
lean_dec(v_i_548_);
v_stop_boxed_552_ = lean_unbox_usize(v_stop_549_);
lean_dec(v_stop_549_);
v_b_boxed_553_ = lean_unbox_uint64(v_b_550_);
lean_dec_ref(v_b_550_);
v_res_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_as_547_, v_i_boxed_551_, v_stop_boxed_552_, v_b_boxed_553_);
lean_dec_ref(v_as_547_);
v_r_555_ = lean_box_uint64(v_res_554_);
return v_r_555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(lean_object* v_x_556_, lean_object* v_x_557_){
_start:
{
if (lean_obj_tag(v_x_557_) == 0)
{
return v_x_556_;
}
else
{
lean_object* v_key_558_; lean_object* v_value_559_; lean_object* v_tail_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_599_; 
v_key_558_ = lean_ctor_get(v_x_557_, 0);
v_value_559_ = lean_ctor_get(v_x_557_, 1);
v_tail_560_ = lean_ctor_get(v_x_557_, 2);
v_isSharedCheck_599_ = !lean_is_exclusive(v_x_557_);
if (v_isSharedCheck_599_ == 0)
{
v___x_562_ = v_x_557_;
v_isShared_563_ = v_isSharedCheck_599_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_tail_560_);
lean_inc(v_value_559_);
lean_inc(v_key_558_);
lean_dec(v_x_557_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_599_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v_fst_564_; lean_object* v_snd_565_; lean_object* v___x_566_; uint64_t v___y_568_; uint64_t v___y_569_; uint64_t v___y_589_; 
v_fst_564_ = lean_ctor_get(v_key_558_, 0);
v_snd_565_ = lean_ctor_get(v_key_558_, 1);
v___x_566_ = lean_array_get_size(v_x_556_);
if (lean_obj_tag(v_fst_564_) == 0)
{
uint64_t v___x_597_; 
v___x_597_ = 1723ULL;
v___y_589_ = v___x_597_;
goto v___jp_588_;
}
else
{
uint64_t v_hash_598_; 
v_hash_598_ = lean_ctor_get_uint64(v_fst_564_, sizeof(void*)*2);
v___y_589_ = v_hash_598_;
goto v___jp_588_;
}
v___jp_567_:
{
uint64_t v___x_570_; uint64_t v___x_571_; uint64_t v___x_572_; uint64_t v_fold_573_; uint64_t v___x_574_; uint64_t v___x_575_; uint64_t v___x_576_; size_t v___x_577_; size_t v___x_578_; size_t v___x_579_; size_t v___x_580_; size_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_570_ = lean_uint64_mix_hash(v___y_568_, v___y_569_);
v___x_571_ = 32ULL;
v___x_572_ = lean_uint64_shift_right(v___x_570_, v___x_571_);
v_fold_573_ = lean_uint64_xor(v___x_570_, v___x_572_);
v___x_574_ = 16ULL;
v___x_575_ = lean_uint64_shift_right(v_fold_573_, v___x_574_);
v___x_576_ = lean_uint64_xor(v_fold_573_, v___x_575_);
v___x_577_ = lean_uint64_to_usize(v___x_576_);
v___x_578_ = lean_usize_of_nat(v___x_566_);
v___x_579_ = ((size_t)1ULL);
v___x_580_ = lean_usize_sub(v___x_578_, v___x_579_);
v___x_581_ = lean_usize_land(v___x_577_, v___x_580_);
v___x_582_ = lean_array_uget_borrowed(v_x_556_, v___x_581_);
lean_inc(v___x_582_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 2, v___x_582_);
v___x_584_ = v___x_562_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_key_558_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_value_559_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v___x_582_);
v___x_584_ = v_reuseFailAlloc_587_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_585_; 
v___x_585_ = lean_array_uset(v_x_556_, v___x_581_, v___x_584_);
v_x_556_ = v___x_585_;
v_x_557_ = v_tail_560_;
goto _start;
}
}
v___jp_588_:
{
uint64_t v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_590_ = 7ULL;
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = lean_array_get_size(v_snd_565_);
v___x_593_ = lean_nat_dec_lt(v___x_591_, v___x_592_);
if (v___x_593_ == 0)
{
v___y_568_ = v___y_589_;
v___y_569_ = v___x_590_;
goto v___jp_567_;
}
else
{
size_t v___x_594_; size_t v___x_595_; uint64_t v___x_596_; 
v___x_594_ = ((size_t)0ULL);
v___x_595_ = lean_usize_of_nat(v___x_592_);
v___x_596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_565_, v___x_594_, v___x_595_, v___x_590_);
v___y_568_ = v___y_589_;
v___y_569_ = v___x_596_;
goto v___jp_567_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(lean_object* v_i_600_, lean_object* v_source_601_, lean_object* v_target_602_){
_start:
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = lean_array_get_size(v_source_601_);
v___x_604_ = lean_nat_dec_lt(v_i_600_, v___x_603_);
if (v___x_604_ == 0)
{
lean_dec_ref(v_source_601_);
lean_dec(v_i_600_);
return v_target_602_;
}
else
{
lean_object* v_es_605_; lean_object* v___x_606_; lean_object* v_source_607_; lean_object* v_target_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_es_605_ = lean_array_fget(v_source_601_, v_i_600_);
v___x_606_ = lean_box(0);
v_source_607_ = lean_array_fset(v_source_601_, v_i_600_, v___x_606_);
v_target_608_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(v_target_602_, v_es_605_);
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = lean_nat_add(v_i_600_, v___x_609_);
lean_dec(v_i_600_);
v_i_600_ = v___x_610_;
v_source_601_ = v_source_607_;
v_target_602_ = v_target_608_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(lean_object* v_data_612_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v_nbuckets_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_613_ = lean_array_get_size(v_data_612_);
v___x_614_ = lean_unsigned_to_nat(2u);
v_nbuckets_615_ = lean_nat_mul(v___x_613_, v___x_614_);
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = lean_box(0);
v___x_618_ = lean_mk_array(v_nbuckets_615_, v___x_617_);
v___x_619_ = lean_array_propagate_mark(v_data_612_, v___x_618_);
v___x_620_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(v___x_616_, v_data_612_, v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(lean_object* v_m_621_, lean_object* v_a_622_, lean_object* v_b_623_){
_start:
{
lean_object* v_size_624_; lean_object* v_buckets_625_; lean_object* v_fst_626_; lean_object* v_snd_627_; lean_object* v___x_628_; uint64_t v___y_630_; uint64_t v___y_631_; uint64_t v___y_670_; 
v_size_624_ = lean_ctor_get(v_m_621_, 0);
v_buckets_625_ = lean_ctor_get(v_m_621_, 1);
v_fst_626_ = lean_ctor_get(v_a_622_, 0);
v_snd_627_ = lean_ctor_get(v_a_622_, 1);
v___x_628_ = lean_array_get_size(v_buckets_625_);
if (lean_obj_tag(v_fst_626_) == 0)
{
uint64_t v___x_678_; 
v___x_678_ = 1723ULL;
v___y_670_ = v___x_678_;
goto v___jp_669_;
}
else
{
uint64_t v_hash_679_; 
v_hash_679_ = lean_ctor_get_uint64(v_fst_626_, sizeof(void*)*2);
v___y_670_ = v_hash_679_;
goto v___jp_669_;
}
v___jp_629_:
{
uint64_t v___x_632_; uint64_t v___x_633_; uint64_t v___x_634_; uint64_t v_fold_635_; uint64_t v___x_636_; uint64_t v___x_637_; uint64_t v___x_638_; size_t v___x_639_; size_t v___x_640_; size_t v___x_641_; size_t v___x_642_; size_t v___x_643_; lean_object* v_bkt_644_; uint8_t v___x_645_; 
v___x_632_ = lean_uint64_mix_hash(v___y_630_, v___y_631_);
v___x_633_ = 32ULL;
v___x_634_ = lean_uint64_shift_right(v___x_632_, v___x_633_);
v_fold_635_ = lean_uint64_xor(v___x_632_, v___x_634_);
v___x_636_ = 16ULL;
v___x_637_ = lean_uint64_shift_right(v_fold_635_, v___x_636_);
v___x_638_ = lean_uint64_xor(v_fold_635_, v___x_637_);
v___x_639_ = lean_uint64_to_usize(v___x_638_);
v___x_640_ = lean_usize_of_nat(v___x_628_);
v___x_641_ = ((size_t)1ULL);
v___x_642_ = lean_usize_sub(v___x_640_, v___x_641_);
v___x_643_ = lean_usize_land(v___x_639_, v___x_642_);
v_bkt_644_ = lean_array_uget_borrowed(v_buckets_625_, v___x_643_);
v___x_645_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_622_, v_bkt_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_666_; 
lean_inc_ref(v_buckets_625_);
lean_inc(v_size_624_);
v_isSharedCheck_666_ = !lean_is_exclusive(v_m_621_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; lean_object* v_unused_668_; 
v_unused_667_ = lean_ctor_get(v_m_621_, 1);
lean_dec(v_unused_667_);
v_unused_668_ = lean_ctor_get(v_m_621_, 0);
lean_dec(v_unused_668_);
v___x_647_ = v_m_621_;
v_isShared_648_ = v_isSharedCheck_666_;
goto v_resetjp_646_;
}
else
{
lean_dec(v_m_621_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_666_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v_size_x27_650_; lean_object* v___x_651_; lean_object* v_buckets_x27_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_649_ = lean_unsigned_to_nat(1u);
v_size_x27_650_ = lean_nat_add(v_size_624_, v___x_649_);
lean_dec(v_size_624_);
lean_inc(v_bkt_644_);
v___x_651_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_651_, 0, v_a_622_);
lean_ctor_set(v___x_651_, 1, v_b_623_);
lean_ctor_set(v___x_651_, 2, v_bkt_644_);
v_buckets_x27_652_ = lean_array_uset(v_buckets_625_, v___x_643_, v___x_651_);
v___x_653_ = lean_unsigned_to_nat(4u);
v___x_654_ = lean_nat_mul(v_size_x27_650_, v___x_653_);
v___x_655_ = lean_unsigned_to_nat(3u);
v___x_656_ = lean_nat_div(v___x_654_, v___x_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_array_get_size(v_buckets_x27_652_);
v___x_658_ = lean_nat_dec_le(v___x_656_, v___x_657_);
lean_dec(v___x_656_);
if (v___x_658_ == 0)
{
lean_object* v_val_659_; lean_object* v___x_661_; 
v_val_659_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(v_buckets_x27_652_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v_val_659_);
lean_ctor_set(v___x_647_, 0, v_size_x27_650_);
v___x_661_ = v___x_647_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_size_x27_650_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v_val_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
else
{
lean_object* v___x_664_; 
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v_buckets_x27_652_);
lean_ctor_set(v___x_647_, 0, v_size_x27_650_);
v___x_664_ = v___x_647_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_size_x27_650_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_buckets_x27_652_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
else
{
lean_dec(v_b_623_);
lean_dec_ref(v_a_622_);
return v_m_621_;
}
}
v___jp_669_:
{
uint64_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_671_ = 7ULL;
v___x_672_ = lean_unsigned_to_nat(0u);
v___x_673_ = lean_array_get_size(v_snd_627_);
v___x_674_ = lean_nat_dec_lt(v___x_672_, v___x_673_);
if (v___x_674_ == 0)
{
v___y_630_ = v___y_670_;
v___y_631_ = v___x_671_;
goto v___jp_629_;
}
else
{
size_t v___x_675_; size_t v___x_676_; uint64_t v___x_677_; 
v___x_675_ = ((size_t)0ULL);
v___x_676_ = lean_usize_of_nat(v___x_673_);
v___x_677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_627_, v___x_675_, v___x_676_, v___x_671_);
v___y_630_ = v___y_670_;
v___y_631_ = v___x_677_;
goto v___jp_629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(lean_object* v_f_680_, lean_object* v_v_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
if (lean_obj_tag(v_v_681_) == 0)
{
lean_object* v_code_684_; lean_object* v___x_685_; 
v_code_684_ = lean_ctor_get(v_v_681_, 0);
lean_inc_ref(v_code_684_);
lean_dec_ref_known(v_v_681_, 1);
lean_inc_ref(v___y_682_);
v___x_685_ = lean_apply_3(v_f_680_, v_code_684_, v___y_682_, v___y_683_);
return v___x_685_;
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec_ref_known(v_v_681_, 1);
lean_dec_ref(v_f_680_);
v___x_686_ = lean_box(0);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v___y_683_);
return v___x_687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg___boxed(lean_object* v_f_688_, lean_object* v_v_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v_f_688_, v_v_689_, v___y_690_, v___y_691_);
lean_dec_ref(v___y_690_);
return v_res_692_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(lean_object* v_m_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_buckets_695_; lean_object* v_fst_696_; lean_object* v_snd_697_; lean_object* v___x_698_; uint64_t v___y_700_; uint64_t v___y_701_; uint64_t v___y_717_; 
v_buckets_695_ = lean_ctor_get(v_m_693_, 1);
v_fst_696_ = lean_ctor_get(v_a_694_, 0);
v_snd_697_ = lean_ctor_get(v_a_694_, 1);
v___x_698_ = lean_array_get_size(v_buckets_695_);
if (lean_obj_tag(v_fst_696_) == 0)
{
uint64_t v___x_725_; 
v___x_725_ = 1723ULL;
v___y_717_ = v___x_725_;
goto v___jp_716_;
}
else
{
uint64_t v_hash_726_; 
v_hash_726_ = lean_ctor_get_uint64(v_fst_696_, sizeof(void*)*2);
v___y_717_ = v_hash_726_;
goto v___jp_716_;
}
v___jp_699_:
{
uint64_t v___x_702_; uint64_t v___x_703_; uint64_t v___x_704_; uint64_t v_fold_705_; uint64_t v___x_706_; uint64_t v___x_707_; uint64_t v___x_708_; size_t v___x_709_; size_t v___x_710_; size_t v___x_711_; size_t v___x_712_; size_t v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_702_ = lean_uint64_mix_hash(v___y_700_, v___y_701_);
v___x_703_ = 32ULL;
v___x_704_ = lean_uint64_shift_right(v___x_702_, v___x_703_);
v_fold_705_ = lean_uint64_xor(v___x_702_, v___x_704_);
v___x_706_ = 16ULL;
v___x_707_ = lean_uint64_shift_right(v_fold_705_, v___x_706_);
v___x_708_ = lean_uint64_xor(v_fold_705_, v___x_707_);
v___x_709_ = lean_uint64_to_usize(v___x_708_);
v___x_710_ = lean_usize_of_nat(v___x_698_);
v___x_711_ = ((size_t)1ULL);
v___x_712_ = lean_usize_sub(v___x_710_, v___x_711_);
v___x_713_ = lean_usize_land(v___x_709_, v___x_712_);
v___x_714_ = lean_array_uget_borrowed(v_buckets_695_, v___x_713_);
v___x_715_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_694_, v___x_714_);
return v___x_715_;
}
v___jp_716_:
{
uint64_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_718_ = 7ULL;
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = lean_array_get_size(v_snd_697_);
v___x_721_ = lean_nat_dec_lt(v___x_719_, v___x_720_);
if (v___x_721_ == 0)
{
v___y_700_ = v___y_717_;
v___y_701_ = v___x_718_;
goto v___jp_699_;
}
else
{
size_t v___x_722_; size_t v___x_723_; uint64_t v___x_724_; 
v___x_722_ = ((size_t)0ULL);
v___x_723_ = lean_usize_of_nat(v___x_720_);
v___x_724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_697_, v___x_722_, v___x_723_, v___x_718_);
v___y_700_ = v___y_717_;
v___y_701_ = v___x_724_;
goto v___jp_699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg___boxed(lean_object* v_m_727_, lean_object* v_a_728_){
_start:
{
uint8_t v_res_729_; lean_object* v_r_730_; 
v_res_729_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_m_727_, v_a_728_);
lean_dec_ref(v_a_728_);
lean_dec_ref(v_m_727_);
v_r_730_ = lean_box(v_res_729_);
return v_r_730_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(lean_object* v_upperBound_731_, lean_object* v_args_732_, lean_object* v_a_733_, lean_object* v_b_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_a_738_; lean_object* v_a_739_; uint8_t v___x_743_; 
v___x_743_ = lean_nat_dec_lt(v_a_733_, v_upperBound_731_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; 
lean_dec(v_a_733_);
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v_b_734_);
lean_ctor_set(v___x_744_, 1, v___y_736_);
return v___x_744_;
}
else
{
lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_745_ = lean_array_get_size(v_args_732_);
v___x_746_ = lean_nat_dec_lt(v_a_733_, v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_box(0);
v___x_748_ = lean_array_push(v_b_734_, v___x_747_);
v_a_738_ = v___x_748_;
v_a_739_ = v___y_736_;
goto v___jp_737_;
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_array_fget_borrowed(v_args_732_, v_a_733_);
v___x_750_ = l_Lean_Compiler_LCNF_FixedParams_evalArg(v___x_749_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v_a_752_; lean_object* v___x_753_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
v_a_752_ = lean_ctor_get(v___x_750_, 1);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_750_, 2);
v___x_753_ = lean_array_push(v_b_734_, v_a_751_);
v_a_738_ = v___x_753_;
v_a_739_ = v_a_752_;
goto v___jp_737_;
}
else
{
lean_object* v_a_754_; lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec_ref(v_b_734_);
lean_dec(v_a_733_);
v_a_754_ = lean_ctor_get(v___x_750_, 0);
v_a_755_ = lean_ctor_get(v___x_750_, 1);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_750_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_inc(v_a_754_);
lean_dec(v___x_750_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_754_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
v___jp_737_:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_nat_add(v_a_733_, v___x_740_);
lean_dec(v_a_733_);
v_a_733_ = v___x_741_;
v_b_734_ = v_a_738_;
v___y_736_ = v_a_739_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg___boxed(lean_object* v_upperBound_763_, lean_object* v_args_764_, lean_object* v_a_765_, lean_object* v_b_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v_upperBound_763_, v_args_764_, v_a_765_, v_b_766_, v___y_767_, v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec_ref(v_args_764_);
lean_dec(v_upperBound_763_);
return v_res_769_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(uint8_t v_a_770_, uint8_t v___x_771_, lean_object* v_as_772_, size_t v_i_773_, size_t v_stop_774_){
_start:
{
uint8_t v___x_779_; 
v___x_779_ = lean_usize_dec_eq(v_i_773_, v_stop_774_);
if (v___x_779_ == 0)
{
uint8_t v___x_780_; uint8_t v___y_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_780_ = 1;
v___x_783_ = lean_array_uget_borrowed(v_as_772_, v_i_773_);
v___x_784_ = lean_unbox(v___x_783_);
if (v___x_784_ == 0)
{
if (v_a_770_ == 0)
{
v___y_782_ = v___x_771_;
goto v___jp_781_;
}
else
{
goto v___jp_775_;
}
}
else
{
v___y_782_ = v_a_770_;
goto v___jp_781_;
}
v___jp_781_:
{
if (v___y_782_ == 0)
{
goto v___jp_775_;
}
else
{
return v___x_780_;
}
}
}
else
{
uint8_t v___x_785_; 
v___x_785_ = 0;
return v___x_785_;
}
v___jp_775_:
{
size_t v___x_776_; size_t v___x_777_; 
v___x_776_ = ((size_t)1ULL);
v___x_777_ = lean_usize_add(v_i_773_, v___x_776_);
v_i_773_ = v___x_777_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9___boxed(lean_object* v_a_786_, lean_object* v___x_787_, lean_object* v_as_788_, lean_object* v_i_789_, lean_object* v_stop_790_){
_start:
{
uint8_t v_a_boxed_791_; uint8_t v___x_13268__boxed_792_; size_t v_i_boxed_793_; size_t v_stop_boxed_794_; uint8_t v_res_795_; lean_object* v_r_796_; 
v_a_boxed_791_ = lean_unbox(v_a_786_);
v___x_13268__boxed_792_ = lean_unbox(v___x_787_);
v_i_boxed_793_ = lean_unbox_usize(v_i_789_);
lean_dec(v_i_789_);
v_stop_boxed_794_ = lean_unbox_usize(v_stop_790_);
lean_dec(v_stop_790_);
v_res_795_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(v_a_boxed_791_, v___x_13268__boxed_792_, v_as_788_, v_i_boxed_793_, v_stop_boxed_794_);
lean_dec_ref(v_as_788_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(uint8_t v___x_797_, lean_object* v_as_798_, uint8_t v_a_799_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_array_get_size(v_as_798_);
v___x_802_ = lean_nat_dec_lt(v___x_800_, v___x_801_);
if (v___x_802_ == 0)
{
return v___x_802_;
}
else
{
size_t v___x_803_; size_t v___x_804_; uint8_t v___x_805_; 
v___x_803_ = ((size_t)0ULL);
v___x_804_ = lean_usize_of_nat(v___x_801_);
v___x_805_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(v_a_799_, v___x_797_, v_as_798_, v___x_803_, v___x_804_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___boxed(lean_object* v___x_806_, lean_object* v_as_807_, lean_object* v_a_808_){
_start:
{
uint8_t v___x_13293__boxed_809_; uint8_t v_a_boxed_810_; uint8_t v_res_811_; lean_object* v_r_812_; 
v___x_13293__boxed_809_ = lean_unbox(v___x_806_);
v_a_boxed_810_ = lean_unbox(v_a_808_);
v_res_811_ = l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(v___x_13293__boxed_809_, v_as_807_, v_a_boxed_810_);
lean_dec_ref(v_as_807_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0___boxed(lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_c_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0(v_a_815_, v_a_816_, v_c_817_, v___y_818_, v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec_ref(v_a_815_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(lean_object* v_declName_821_, lean_object* v_args_822_, lean_object* v_as_823_, size_t v_sz_824_, size_t v_i_825_, lean_object* v_b_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_a_830_; lean_object* v_a_831_; uint8_t v___x_835_; 
v___x_835_ = lean_usize_dec_lt(v_i_825_, v_sz_824_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
lean_dec(v_declName_821_);
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v_b_826_);
lean_ctor_set(v___x_836_, 1, v___y_828_);
return v___x_836_;
}
else
{
lean_object* v_a_837_; lean_object* v_toSignature_838_; lean_object* v_value_839_; lean_object* v_name_840_; lean_object* v_params_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v_a_837_ = lean_array_uget_borrowed(v_as_823_, v_i_825_);
v_toSignature_838_ = lean_ctor_get(v_a_837_, 0);
v_value_839_ = lean_ctor_get(v_a_837_, 1);
v_name_840_ = lean_ctor_get(v_toSignature_838_, 0);
v_params_841_ = lean_ctor_get(v_toSignature_838_, 3);
v___x_842_ = lean_box(0);
v___x_843_ = lean_name_eq(v_declName_821_, v_name_840_);
if (v___x_843_ == 0)
{
v_a_830_ = v___x_842_;
v_a_831_ = v___y_828_;
goto v___jp_829_;
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_844_ = lean_array_get_size(v_params_841_);
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0));
v___x_847_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v___x_844_, v_args_822_, v___x_845_, v___x_846_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v_a_849_; lean_object* v_visited_850_; lean_object* v_fixed_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v_a_848_ = lean_ctor_get(v___x_847_, 1);
lean_inc(v_a_848_);
v_a_849_ = lean_ctor_get(v___x_847_, 0);
lean_inc_n(v_a_849_, 2);
lean_dec_ref_known(v___x_847_, 2);
v_visited_850_ = lean_ctor_get(v_a_848_, 0);
v_fixed_851_ = lean_ctor_get(v_a_848_, 1);
lean_inc(v_declName_821_);
v___x_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_852_, 0, v_declName_821_);
lean_ctor_set(v___x_852_, 1, v_a_849_);
v___x_853_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_visited_850_, v___x_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_864_; 
lean_inc_ref(v_fixed_851_);
lean_inc_ref(v_visited_850_);
v_isSharedCheck_864_ = !lean_is_exclusive(v_a_848_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; lean_object* v_unused_866_; 
v_unused_865_ = lean_ctor_get(v_a_848_, 1);
lean_dec(v_unused_865_);
v_unused_866_ = lean_ctor_get(v_a_848_, 0);
lean_dec(v_unused_866_);
v___x_855_ = v_a_848_;
v_isShared_856_ = v_isSharedCheck_864_;
goto v_resetjp_854_;
}
else
{
lean_dec(v_a_848_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_864_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___f_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
lean_inc(v_a_837_);
v___f_857_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0___boxed), 5, 2);
lean_closure_set(v___f_857_, 0, v_a_837_);
lean_closure_set(v___f_857_, 1, v_a_849_);
v___x_858_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(v_visited_850_, v___x_852_, v___x_842_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_858_);
v___x_860_ = v___x_855_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_fixed_851_);
v___x_860_ = v_reuseFailAlloc_863_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; 
lean_inc_ref(v_value_839_);
v___x_861_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v___f_857_, v_value_839_, v___y_827_, v___x_860_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; 
v_a_862_ = lean_ctor_get(v___x_861_, 1);
lean_inc(v_a_862_);
lean_dec_ref_known(v___x_861_, 2);
v_a_830_ = v___x_842_;
v_a_831_ = v_a_862_;
goto v___jp_829_;
}
else
{
lean_dec(v_declName_821_);
return v___x_861_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_852_, 2);
lean_dec(v_a_849_);
v_a_830_ = v___x_842_;
v_a_831_ = v_a_848_;
goto v___jp_829_;
}
}
else
{
lean_object* v_a_867_; lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec(v_declName_821_);
v_a_867_ = lean_ctor_get(v___x_847_, 0);
v_a_868_ = lean_ctor_get(v___x_847_, 1);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_847_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_inc(v_a_867_);
lean_dec(v___x_847_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_867_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
v___jp_829_:
{
size_t v___x_832_; size_t v___x_833_; 
v___x_832_ = ((size_t)1ULL);
v___x_833_ = lean_usize_add(v_i_825_, v___x_832_);
v_i_825_ = v___x_833_;
v_b_826_ = v_a_830_;
v___y_828_ = v_a_831_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp(lean_object* v_declName_876_, lean_object* v_args_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v___y_881_; lean_object* v_decls_882_; lean_object* v___y_883_; lean_object* v_main_897_; lean_object* v_toSignature_898_; lean_object* v_decls_899_; lean_object* v_name_900_; lean_object* v_params_901_; uint8_t v___x_902_; 
v_main_897_ = lean_ctor_get(v_a_878_, 1);
v_toSignature_898_ = lean_ctor_get(v_main_897_, 0);
v_decls_899_ = lean_ctor_get(v_a_878_, 0);
v_name_900_ = lean_ctor_get(v_toSignature_898_, 0);
v_params_901_ = lean_ctor_get(v_toSignature_898_, 3);
v___x_902_ = lean_name_eq(v_declName_876_, v_name_900_);
if (v___x_902_ == 0)
{
v___y_881_ = v_a_878_;
v_decls_882_ = v_decls_899_;
v___y_883_ = v_a_879_;
goto v___jp_880_;
}
else
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_903_ = lean_array_get_size(v_params_901_);
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = lean_box(0);
v___x_906_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(v___x_903_, v_args_877_, v___x_904_, v___x_905_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_916_; 
v_a_907_ = lean_ctor_get(v___x_906_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; 
v_unused_917_ = lean_ctor_get(v___x_906_, 0);
lean_dec(v_unused_917_);
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_916_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_916_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v_fixed_911_; uint8_t v___x_912_; 
v_fixed_911_ = lean_ctor_get(v_a_907_, 1);
v___x_912_ = l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(v___x_902_, v_fixed_911_, v___x_902_);
if (v___x_912_ == 0)
{
lean_object* v___x_914_; 
lean_dec(v_declName_876_);
if (v_isShared_910_ == 0)
{
lean_ctor_set_tag(v___x_909_, 1);
lean_ctor_set(v___x_909_, 0, v___x_905_);
v___x_914_ = v___x_909_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_a_907_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
else
{
lean_del_object(v___x_909_);
v___y_881_ = v_a_878_;
v_decls_882_ = v_decls_899_;
v___y_883_ = v_a_907_;
goto v___jp_880_;
}
}
}
else
{
lean_dec(v_declName_876_);
return v___x_906_;
}
}
v___jp_880_:
{
lean_object* v___x_884_; size_t v_sz_885_; size_t v___x_886_; lean_object* v___x_887_; 
v___x_884_ = lean_box(0);
v_sz_885_ = lean_array_size(v_decls_882_);
v___x_886_ = ((size_t)0ULL);
v___x_887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(v_declName_876_, v_args_877_, v_decls_882_, v_sz_885_, v___x_886_, v___x_884_, v___y_881_, v___y_883_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
v_a_888_ = lean_ctor_get(v___x_887_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; 
v_unused_896_ = lean_ctor_get(v___x_887_, 0);
lean_dec(v_unused_896_);
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_884_);
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
else
{
return v___x_887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalLetValue(lean_object* v_e_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
if (lean_obj_tag(v_e_918_) == 3)
{
lean_object* v_declName_921_; lean_object* v_args_922_; lean_object* v___x_923_; 
v_declName_921_ = lean_ctor_get(v_e_918_, 0);
lean_inc(v_declName_921_);
v_args_922_ = lean_ctor_get(v_e_918_, 2);
lean_inc_ref(v_args_922_);
lean_dec_ref_known(v_e_918_, 3);
v___x_923_ = l_Lean_Compiler_LCNF_FixedParams_evalApp(v_declName_921_, v_args_922_, v_a_919_, v_a_920_);
lean_dec_ref(v_args_922_);
return v___x_923_;
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; 
lean_dec(v_e_918_);
v___x_924_ = lean_box(0);
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v_a_920_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(lean_object* v_as_926_, size_t v_i_927_, size_t v_stop_928_, lean_object* v_b_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___y_933_; uint8_t v___x_940_; 
v___x_940_ = lean_usize_dec_eq(v_i_927_, v_stop_928_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; 
v___x_941_ = lean_array_uget_borrowed(v_as_926_, v_i_927_);
switch(lean_obj_tag(v___x_941_))
{
case 0:
{
lean_object* v_code_942_; 
v_code_942_ = lean_ctor_get(v___x_941_, 2);
lean_inc_ref(v_code_942_);
v___y_933_ = v_code_942_;
goto v___jp_932_;
}
case 1:
{
lean_object* v_code_943_; 
v_code_943_ = lean_ctor_get(v___x_941_, 1);
lean_inc_ref(v_code_943_);
v___y_933_ = v_code_943_;
goto v___jp_932_;
}
default: 
{
lean_object* v_code_944_; 
v_code_944_ = lean_ctor_get(v___x_941_, 0);
lean_inc_ref(v_code_944_);
v___y_933_ = v_code_944_;
goto v___jp_932_;
}
}
}
else
{
lean_object* v___x_945_; 
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v_b_929_);
lean_ctor_set(v___x_945_, 1, v___y_931_);
return v___x_945_;
}
v___jp_932_:
{
lean_object* v___x_934_; 
lean_inc_ref(v___y_930_);
v___x_934_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v___y_933_, v___y_930_, v___y_931_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v_a_936_; size_t v___x_937_; size_t v___x_938_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
v_a_936_ = lean_ctor_get(v___x_934_, 1);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_934_, 2);
v___x_937_ = ((size_t)1ULL);
v___x_938_ = lean_usize_add(v_i_927_, v___x_937_);
v_i_927_ = v___x_938_;
v_b_929_ = v_a_935_;
v___y_931_ = v_a_936_;
goto _start;
}
else
{
return v___x_934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalCode(lean_object* v_code_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
switch(lean_obj_tag(v_code_946_))
{
case 0:
{
lean_object* v_decl_949_; lean_object* v_k_950_; lean_object* v_value_951_; lean_object* v___x_952_; 
v_decl_949_ = lean_ctor_get(v_code_946_, 0);
lean_inc_ref(v_decl_949_);
v_k_950_ = lean_ctor_get(v_code_946_, 1);
lean_inc_ref(v_k_950_);
lean_dec_ref_known(v_code_946_, 2);
v_value_951_ = lean_ctor_get(v_decl_949_, 3);
lean_inc(v_value_951_);
lean_dec_ref(v_decl_949_);
v___x_952_ = l_Lean_Compiler_LCNF_FixedParams_evalLetValue(v_value_951_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; 
v_a_953_ = lean_ctor_get(v___x_952_, 1);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_952_, 2);
v_code_946_ = v_k_950_;
v_a_948_ = v_a_953_;
goto _start;
}
else
{
lean_dec_ref(v_k_950_);
lean_dec_ref(v_a_947_);
return v___x_952_;
}
}
case 1:
{
lean_object* v_decl_955_; lean_object* v_k_956_; lean_object* v___x_957_; 
v_decl_955_ = lean_ctor_get(v_code_946_, 0);
lean_inc_ref_n(v_decl_955_, 2);
v_k_956_ = lean_ctor_get(v_code_946_, 1);
lean_inc_ref(v_k_956_);
lean_dec_ref_known(v_code_946_, 2);
v___x_957_ = l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(v_decl_955_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
if (lean_obj_tag(v_a_958_) == 1)
{
lean_object* v_a_959_; lean_object* v_val_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_974_; 
v_a_959_ = lean_ctor_get(v___x_957_, 1);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_957_, 2);
v_val_960_ = lean_ctor_get(v_a_958_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v_a_958_);
if (v_isSharedCheck_974_ == 0)
{
v___x_962_ = v_a_958_;
v_isShared_963_ = v_isSharedCheck_974_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_val_960_);
lean_dec(v_a_958_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_974_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v_fvarId_964_; lean_object* v_decls_965_; lean_object* v_main_966_; lean_object* v_assignment_967_; lean_object* v___x_969_; 
v_fvarId_964_ = lean_ctor_get(v_decl_955_, 0);
lean_inc(v_fvarId_964_);
lean_dec_ref(v_decl_955_);
v_decls_965_ = lean_ctor_get(v_a_947_, 0);
lean_inc_ref(v_decls_965_);
v_main_966_ = lean_ctor_get(v_a_947_, 1);
lean_inc_ref(v_main_966_);
v_assignment_967_ = lean_ctor_get(v_a_947_, 2);
lean_inc(v_assignment_967_);
lean_dec_ref(v_a_947_);
if (v_isShared_963_ == 0)
{
lean_ctor_set_tag(v___x_962_, 2);
v___x_969_ = v___x_962_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_val_960_);
v___x_969_ = v_reuseFailAlloc_973_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_964_, v___x_969_, v_assignment_967_);
v___x_971_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_971_, 0, v_decls_965_);
lean_ctor_set(v___x_971_, 1, v_main_966_);
lean_ctor_set(v___x_971_, 2, v___x_970_);
v_code_946_ = v_k_956_;
v_a_947_ = v___x_971_;
v_a_948_ = v_a_959_;
goto _start;
}
}
}
else
{
lean_object* v_a_975_; lean_object* v_value_976_; lean_object* v___x_977_; 
lean_dec(v_a_958_);
v_a_975_ = lean_ctor_get(v___x_957_, 1);
lean_inc(v_a_975_);
lean_dec_ref_known(v___x_957_, 2);
v_value_976_ = lean_ctor_get(v_decl_955_, 4);
lean_inc_ref(v_value_976_);
lean_dec_ref(v_decl_955_);
lean_inc_ref(v_a_947_);
v___x_977_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_value_976_, v_a_947_, v_a_975_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; 
v_a_978_ = lean_ctor_get(v___x_977_, 1);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 2);
v_code_946_ = v_k_956_;
v_a_948_ = v_a_978_;
goto _start;
}
else
{
lean_dec_ref(v_k_956_);
lean_dec_ref(v_a_947_);
return v___x_977_;
}
}
}
else
{
lean_object* v_a_980_; lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec_ref(v_k_956_);
lean_dec_ref(v_decl_955_);
lean_dec_ref(v_a_947_);
v_a_980_ = lean_ctor_get(v___x_957_, 0);
v_a_981_ = lean_ctor_get(v___x_957_, 1);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_957_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_inc(v_a_980_);
lean_dec(v___x_957_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_980_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
case 2:
{
lean_object* v_decl_989_; lean_object* v_k_990_; lean_object* v_value_991_; lean_object* v___x_992_; 
v_decl_989_ = lean_ctor_get(v_code_946_, 0);
lean_inc_ref(v_decl_989_);
v_k_990_ = lean_ctor_get(v_code_946_, 1);
lean_inc_ref(v_k_990_);
lean_dec_ref_known(v_code_946_, 2);
v_value_991_ = lean_ctor_get(v_decl_989_, 4);
lean_inc_ref(v_value_991_);
lean_dec_ref(v_decl_989_);
lean_inc_ref(v_a_947_);
v___x_992_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_value_991_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; 
v_a_993_ = lean_ctor_get(v___x_992_, 1);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_992_, 2);
v_code_946_ = v_k_990_;
v_a_948_ = v_a_993_;
goto _start;
}
else
{
lean_dec_ref(v_k_990_);
lean_dec_ref(v_a_947_);
return v___x_992_;
}
}
case 3:
{
lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1002_; 
lean_dec_ref(v_a_947_);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_code_946_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; lean_object* v_unused_1004_; 
v_unused_1003_ = lean_ctor_get(v_code_946_, 1);
lean_dec(v_unused_1003_);
v_unused_1004_ = lean_ctor_get(v_code_946_, 0);
lean_dec(v_unused_1004_);
v___x_996_ = v_code_946_;
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
else
{
lean_dec(v_code_946_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_998_ = lean_box(0);
if (v_isShared_997_ == 0)
{
lean_ctor_set_tag(v___x_996_, 0);
lean_ctor_set(v___x_996_, 1, v_a_948_);
lean_ctor_set(v___x_996_, 0, v___x_998_);
v___x_1000_ = v___x_996_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_a_948_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
case 4:
{
lean_object* v_cases_1005_; lean_object* v_alts_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v_cases_1005_ = lean_ctor_get(v_code_946_, 0);
lean_inc_ref(v_cases_1005_);
lean_dec_ref_known(v_code_946_, 1);
v_alts_1006_ = lean_ctor_get(v_cases_1005_, 3);
lean_inc_ref(v_alts_1006_);
lean_dec_ref(v_cases_1005_);
v___x_1007_ = lean_unsigned_to_nat(0u);
v___x_1008_ = lean_array_get_size(v_alts_1006_);
v___x_1009_ = lean_box(0);
v___x_1010_ = lean_nat_dec_lt(v___x_1007_, v___x_1008_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; 
lean_dec_ref(v_alts_1006_);
lean_dec_ref(v_a_947_);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v_a_948_);
return v___x_1011_;
}
else
{
size_t v___x_1012_; size_t v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = ((size_t)0ULL);
v___x_1013_ = lean_usize_of_nat(v___x_1008_);
v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(v_alts_1006_, v___x_1012_, v___x_1013_, v___x_1009_, v_a_947_, v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec_ref(v_alts_1006_);
return v___x_1014_;
}
}
default: 
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
lean_dec_ref(v_a_947_);
lean_dec_ref(v_code_946_);
v___x_1015_ = lean_box(0);
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v_a_948_);
return v___x_1016_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0(lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_c_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_decls_1022_; lean_object* v_main_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_decls_1022_ = lean_ctor_get(v___y_1020_, 0);
v_main_1023_ = lean_ctor_get(v___y_1020_, 1);
v___x_1024_ = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(v_a_1017_, v_a_1018_);
lean_inc_ref(v_main_1023_);
lean_inc_ref(v_decls_1022_);
v___x_1025_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1025_, 0, v_decls_1022_);
lean_ctor_set(v___x_1025_, 1, v_main_1023_);
lean_ctor_set(v___x_1025_, 2, v___x_1024_);
v___x_1026_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_c_1019_, v___x_1025_, v___y_1021_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalLetValue___boxed(lean_object* v_e_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_Compiler_LCNF_FixedParams_evalLetValue(v_e_1027_, v_a_1028_, v_a_1029_);
lean_dec_ref(v_a_1028_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9___boxed(lean_object* v_as_1031_, lean_object* v_i_1032_, lean_object* v_stop_1033_, lean_object* v_b_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
size_t v_i_boxed_1037_; size_t v_stop_boxed_1038_; lean_object* v_res_1039_; 
v_i_boxed_1037_ = lean_unbox_usize(v_i_1032_);
lean_dec(v_i_1032_);
v_stop_boxed_1038_ = lean_unbox_usize(v_stop_1033_);
lean_dec(v_stop_1033_);
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(v_as_1031_, v_i_boxed_1037_, v_stop_boxed_1038_, v_b_1034_, v___y_1035_, v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec_ref(v_as_1031_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp___boxed(lean_object* v_declName_1040_, lean_object* v_args_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_Compiler_LCNF_FixedParams_evalApp(v_declName_1040_, v_args_1041_, v_a_1042_, v_a_1043_);
lean_dec_ref(v_a_1042_);
lean_dec_ref(v_args_1041_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___boxed(lean_object* v_declName_1045_, lean_object* v_args_1046_, lean_object* v_as_1047_, lean_object* v_sz_1048_, lean_object* v_i_1049_, lean_object* v_b_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
size_t v_sz_boxed_1053_; size_t v_i_boxed_1054_; lean_object* v_res_1055_; 
v_sz_boxed_1053_ = lean_unbox_usize(v_sz_1048_);
lean_dec(v_sz_1048_);
v_i_boxed_1054_ = lean_unbox_usize(v_i_1049_);
lean_dec(v_i_1049_);
v_res_1055_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(v_declName_1045_, v_args_1046_, v_as_1047_, v_sz_boxed_1053_, v_i_boxed_1054_, v_b_1050_, v___y_1051_, v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec_ref(v_as_1047_);
lean_dec_ref(v_args_1046_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3(uint8_t v_pu_1056_, lean_object* v_f_1057_, lean_object* v_v_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v_f_1057_, v_v_1058_, v___y_1059_, v___y_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___boxed(lean_object* v_pu_1062_, lean_object* v_f_1063_, lean_object* v_v_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
uint8_t v_pu_boxed_1067_; lean_object* v_res_1068_; 
v_pu_boxed_1067_ = lean_unbox(v_pu_1062_);
v_res_1068_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3(v_pu_boxed_1067_, v_f_1063_, v_v_1064_, v___y_1065_, v___y_1066_);
lean_dec_ref(v___y_1065_);
return v_res_1068_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1(lean_object* v_00_u03b2_1069_, lean_object* v_m_1070_, lean_object* v_a_1071_){
_start:
{
uint8_t v___x_1072_; 
v___x_1072_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_m_1070_, v_a_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___boxed(lean_object* v_00_u03b2_1073_, lean_object* v_m_1074_, lean_object* v_a_1075_){
_start:
{
uint8_t v_res_1076_; lean_object* v_r_1077_; 
v_res_1076_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1(v_00_u03b2_1073_, v_m_1074_, v_a_1075_);
lean_dec_ref(v_a_1075_);
lean_dec_ref(v_m_1074_);
v_r_1077_ = lean_box(v_res_1076_);
return v_r_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2(lean_object* v_00_u03b2_1078_, lean_object* v_m_1079_, lean_object* v_a_1080_, lean_object* v_b_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(v_m_1079_, v_a_1080_, v_b_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4(lean_object* v_upperBound_1083_, lean_object* v_args_1084_, lean_object* v_inst_1085_, lean_object* v_R_1086_, lean_object* v_a_1087_, lean_object* v_b_1088_, lean_object* v_c_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v_upperBound_1083_, v_args_1084_, v_a_1087_, v_b_1088_, v___y_1090_, v___y_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___boxed(lean_object* v_upperBound_1093_, lean_object* v_args_1094_, lean_object* v_inst_1095_, lean_object* v_R_1096_, lean_object* v_a_1097_, lean_object* v_b_1098_, lean_object* v_c_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4(v_upperBound_1093_, v_args_1094_, v_inst_1095_, v_R_1096_, v_a_1097_, v_b_1098_, v_c_1099_, v___y_1100_, v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec_ref(v_args_1094_);
lean_dec(v_upperBound_1093_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7(lean_object* v_upperBound_1103_, lean_object* v_args_1104_, lean_object* v_inst_1105_, lean_object* v_R_1106_, lean_object* v_a_1107_, lean_object* v_b_1108_, lean_object* v_c_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(v_upperBound_1103_, v_args_1104_, v_a_1107_, v_b_1108_, v___y_1110_, v___y_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___boxed(lean_object* v_upperBound_1113_, lean_object* v_args_1114_, lean_object* v_inst_1115_, lean_object* v_R_1116_, lean_object* v_a_1117_, lean_object* v_b_1118_, lean_object* v_c_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7(v_upperBound_1113_, v_args_1114_, v_inst_1115_, v_R_1116_, v_a_1117_, v_b_1118_, v_c_1119_, v___y_1120_, v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec_ref(v_args_1114_);
lean_dec(v_upperBound_1113_);
return v_res_1122_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1(lean_object* v_00_u03b2_1123_, lean_object* v_a_1124_, lean_object* v_x_1125_){
_start:
{
uint8_t v___x_1126_; 
v___x_1126_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_1124_, v_x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1127_, lean_object* v_a_1128_, lean_object* v_x_1129_){
_start:
{
uint8_t v_res_1130_; lean_object* v_r_1131_; 
v_res_1130_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1(v_00_u03b2_1127_, v_a_1128_, v_x_1129_);
lean_dec(v_x_1129_);
lean_dec_ref(v_a_1128_);
v_r_1131_ = lean_box(v_res_1130_);
return v_r_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4(lean_object* v_00_u03b2_1132_, lean_object* v_data_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(v_data_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4(lean_object* v_xs_1135_, lean_object* v_ys_1136_, lean_object* v_hsz_1137_, lean_object* v_x_1138_, lean_object* v_x_1139_){
_start:
{
uint8_t v___x_1140_; 
v___x_1140_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(v_xs_1135_, v_ys_1136_, v_x_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___boxed(lean_object* v_xs_1141_, lean_object* v_ys_1142_, lean_object* v_hsz_1143_, lean_object* v_x_1144_, lean_object* v_x_1145_){
_start:
{
uint8_t v_res_1146_; lean_object* v_r_1147_; 
v_res_1146_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4(v_xs_1141_, v_ys_1142_, v_hsz_1143_, v_x_1144_, v_x_1145_);
lean_dec_ref(v_ys_1142_);
lean_dec_ref(v_xs_1141_);
v_r_1147_ = lean_box(v_res_1146_);
return v_r_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_1148_, lean_object* v_i_1149_, lean_object* v_source_1150_, lean_object* v_target_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(v_i_1149_, v_source_1150_, v_target_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14(lean_object* v_00_u03b2_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(v_x_1154_, v_x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(lean_object* v_upperBound_1157_, lean_object* v_a_1158_, lean_object* v_b_1159_){
_start:
{
uint8_t v___x_1160_; 
v___x_1160_ = lean_nat_dec_lt(v_a_1158_, v_upperBound_1157_);
if (v___x_1160_ == 0)
{
lean_dec(v_a_1158_);
return v_b_1159_;
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_inc(v_a_1158_);
v___x_1161_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1161_, 0, v_a_1158_);
v___x_1162_ = lean_array_push(v_b_1159_, v___x_1161_);
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_nat_add(v_a_1158_, v___x_1163_);
lean_dec(v_a_1158_);
v_a_1158_ = v___x_1164_;
v_b_1159_ = v___x_1162_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg___boxed(lean_object* v_upperBound_1166_, lean_object* v_a_1167_, lean_object* v_b_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_upperBound_1166_, v_a_1167_, v_b_1168_);
lean_dec(v_upperBound_1166_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(lean_object* v_numParams_1170_){
_start:
{
lean_object* v___x_1171_; lean_object* v_values_1172_; lean_object* v___x_1173_; 
v___x_1171_ = lean_unsigned_to_nat(0u);
v_values_1172_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0));
v___x_1173_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_numParams_1170_, v___x_1171_, v_values_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkInitialValues___boxed(lean_object* v_numParams_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(v_numParams_1174_);
lean_dec(v_numParams_1174_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0(lean_object* v_upperBound_1176_, lean_object* v_inst_1177_, lean_object* v_R_1178_, lean_object* v_a_1179_, lean_object* v_b_1180_, lean_object* v_c_1181_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_upperBound_1176_, v_a_1179_, v_b_1180_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___boxed(lean_object* v_upperBound_1183_, lean_object* v_inst_1184_, lean_object* v_R_1185_, lean_object* v_a_1186_, lean_object* v_b_1187_, lean_object* v_c_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0(v_upperBound_1183_, v_inst_1184_, v_R_1185_, v_a_1186_, v_b_1187_, v_c_1188_);
lean_dec(v_upperBound_1183_);
return v_res_1189_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = lean_box(0);
v___x_1191_ = lean_unsigned_to_nat(16u);
v___x_1192_ = lean_mk_array(v___x_1191_, v___x_1190_);
return v___x_1192_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1193_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0);
v___x_1194_ = lean_unsigned_to_nat(0u);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
lean_ctor_set(v___x_1195_, 1, v___x_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(lean_object* v_decls_1196_, lean_object* v_as_1197_, size_t v_sz_1198_, size_t v_i_1199_, lean_object* v_b_1200_){
_start:
{
lean_object* v_a_1202_; uint8_t v___x_1206_; 
v___x_1206_ = lean_usize_dec_lt(v_i_1199_, v_sz_1198_);
if (v___x_1206_ == 0)
{
lean_dec_ref(v_decls_1196_);
return v_b_1200_;
}
else
{
lean_object* v_a_1207_; lean_object* v_toSignature_1208_; lean_object* v_value_1209_; lean_object* v_name_1210_; lean_object* v_params_1211_; lean_object* v_s_1213_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_a_1207_ = lean_array_uget_borrowed(v_as_1197_, v_i_1199_);
v_toSignature_1208_ = lean_ctor_get(v_a_1207_, 0);
v_value_1209_ = lean_ctor_get(v_a_1207_, 1);
v_name_1210_ = lean_ctor_get(v_toSignature_1208_, 0);
v_params_1211_ = lean_ctor_get(v_toSignature_1208_, 3);
v___x_1216_ = lean_array_get_size(v_params_1211_);
v___x_1217_ = l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(v___x_1216_);
v___x_1218_ = lean_box(v___x_1206_);
v___x_1219_ = lean_mk_array(v___x_1216_, v___x_1218_);
if (lean_obj_tag(v_value_1209_) == 0)
{
lean_object* v_code_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v_a_1226_; 
v_code_1220_ = lean_ctor_get(v_value_1209_, 0);
v___x_1221_ = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(v_a_1207_, v___x_1217_);
lean_inc(v_a_1207_);
lean_inc_ref(v_decls_1196_);
v___x_1222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1222_, 0, v_decls_1196_);
lean_ctor_set(v___x_1222_, 1, v_a_1207_);
lean_ctor_set(v___x_1222_, 2, v___x_1221_);
v___x_1223_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1);
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
lean_ctor_set(v___x_1224_, 1, v___x_1219_);
lean_inc_ref(v_code_1220_);
v___x_1225_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_code_1220_, v___x_1222_, v___x_1224_);
v_a_1226_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_a_1226_);
lean_dec_ref(v___x_1225_);
v_s_1213_ = v_a_1226_;
goto v___jp_1212_;
}
else
{
lean_object* v___x_1227_; 
lean_dec_ref(v___x_1217_);
lean_inc(v_name_1210_);
v___x_1227_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1210_, v___x_1219_, v_b_1200_);
v_a_1202_ = v___x_1227_;
goto v___jp_1201_;
}
v___jp_1212_:
{
lean_object* v_fixed_1214_; lean_object* v___x_1215_; 
v_fixed_1214_ = lean_ctor_get(v_s_1213_, 1);
lean_inc_ref(v_fixed_1214_);
lean_dec_ref(v_s_1213_);
lean_inc(v_name_1210_);
v___x_1215_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1210_, v_fixed_1214_, v_b_1200_);
v_a_1202_ = v___x_1215_;
goto v___jp_1201_;
}
}
v___jp_1201_:
{
size_t v___x_1203_; size_t v___x_1204_; 
v___x_1203_ = ((size_t)1ULL);
v___x_1204_ = lean_usize_add(v_i_1199_, v___x_1203_);
v_i_1199_ = v___x_1204_;
v_b_1200_ = v_a_1202_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___boxed(lean_object* v_decls_1228_, lean_object* v_as_1229_, lean_object* v_sz_1230_, lean_object* v_i_1231_, lean_object* v_b_1232_){
_start:
{
size_t v_sz_boxed_1233_; size_t v_i_boxed_1234_; lean_object* v_res_1235_; 
v_sz_boxed_1233_ = lean_unbox_usize(v_sz_1230_);
lean_dec(v_sz_1230_);
v_i_boxed_1234_ = lean_unbox_usize(v_i_1231_);
lean_dec(v_i_1231_);
v_res_1235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(v_decls_1228_, v_as_1229_, v_sz_boxed_1233_, v_i_boxed_1234_, v_b_1232_);
lean_dec_ref(v_as_1229_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFixedParamsMap(lean_object* v_decls_1236_){
_start:
{
lean_object* v_result_1237_; size_t v_sz_1238_; size_t v___x_1239_; lean_object* v___x_1240_; 
v_result_1237_ = lean_box(1);
v_sz_1238_ = lean_array_size(v_decls_1236_);
v___x_1239_ = ((size_t)0ULL);
lean_inc_ref(v_decls_1236_);
v___x_1240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(v_decls_1236_, v_decls_1236_, v_sz_1238_, v___x_1239_, v_result_1237_);
lean_dec_ref(v_decls_1236_);
return v___x_1240_;
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
