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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(lean_object* v_params_304_, lean_object* v_args_305_, uint8_t v___x_306_, lean_object* v_range_307_, lean_object* v_b_308_, lean_object* v_i_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_stop_311_; lean_object* v_step_312_; uint8_t v___x_313_; 
v_stop_311_ = lean_ctor_get(v_range_307_, 1);
v_step_312_ = lean_ctor_get(v_range_307_, 2);
v___x_313_ = lean_nat_dec_lt(v_i_309_, v_stop_311_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; 
lean_dec(v_i_309_);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v_b_308_);
lean_ctor_set(v___x_314_, 1, v___y_310_);
return v___x_314_;
}
else
{
lean_object* v___x_315_; lean_object* v_fvarId_316_; lean_object* v___x_317_; lean_object* v_a_319_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
lean_dec_ref(v_b_308_);
v___x_315_ = lean_array_fget_borrowed(v_params_304_, v_i_309_);
v_fvarId_316_ = lean_ctor_get(v___x_315_, 0);
v___x_317_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__0));
v___x_322_ = lean_box(0);
v___x_323_ = lean_array_get_borrowed(v___x_322_, v_args_305_, v_i_309_);
lean_inc(v_fvarId_316_);
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v_fvarId_316_);
v___x_325_ = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(v___x_323_, v___x_324_);
lean_dec_ref_known(v___x_324_, 1);
if (v___x_325_ == 0)
{
if (v___x_306_ == 0)
{
v_a_319_ = v___y_310_;
goto v___jp_318_;
}
else
{
uint8_t v___x_326_; 
v___x_326_ = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(v___x_323_, v___x_322_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec(v_i_309_);
v___x_327_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__2));
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___y_310_);
return v___x_328_;
}
else
{
v_a_319_ = v___y_310_;
goto v___jp_318_;
}
}
}
else
{
v_a_319_ = v___y_310_;
goto v___jp_318_;
}
v___jp_318_:
{
lean_object* v___x_320_; 
v___x_320_ = lean_nat_add(v_i_309_, v_step_312_);
lean_dec(v_i_309_);
v_b_308_ = v___x_317_;
v_i_309_ = v___x_320_;
v___y_310_ = v_a_319_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___boxed(lean_object* v_params_329_, lean_object* v_args_330_, lean_object* v___x_331_, lean_object* v_range_332_, lean_object* v_b_333_, lean_object* v_i_334_, lean_object* v___y_335_){
_start:
{
uint8_t v___x_3258__boxed_336_; lean_object* v_res_337_; 
v___x_3258__boxed_336_ = lean_unbox(v___x_331_);
v_res_337_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_329_, v_args_330_, v___x_3258__boxed_336_, v_range_332_, v_b_333_, v_i_334_, v___y_335_);
lean_dec_ref(v_range_332_);
lean_dec_ref(v_args_330_);
lean_dec_ref(v_params_329_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(lean_object* v_decl_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___y_342_; lean_object* v___y_346_; lean_object* v_value_349_; 
v_value_349_ = lean_ctor_get(v_decl_338_, 4);
lean_inc_ref(v_value_349_);
if (lean_obj_tag(v_value_349_) == 0)
{
lean_object* v_decl_350_; lean_object* v_value_351_; 
v_decl_350_ = lean_ctor_get(v_value_349_, 0);
lean_inc_ref(v_decl_350_);
v_value_351_ = lean_ctor_get(v_decl_350_, 3);
lean_inc(v_value_351_);
if (lean_obj_tag(v_value_351_) == 4)
{
lean_object* v_params_352_; lean_object* v_k_353_; lean_object* v_fvarId_354_; lean_object* v_fvarId_355_; lean_object* v_args_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_414_; 
v_params_352_ = lean_ctor_get(v_decl_338_, 2);
lean_inc_ref(v_params_352_);
lean_dec_ref(v_decl_338_);
v_k_353_ = lean_ctor_get(v_value_349_, 1);
lean_inc_ref(v_k_353_);
lean_dec_ref_known(v_value_349_, 2);
v_fvarId_354_ = lean_ctor_get(v_decl_350_, 0);
lean_inc(v_fvarId_354_);
lean_dec_ref(v_decl_350_);
v_fvarId_355_ = lean_ctor_get(v_value_351_, 0);
v_args_356_ = lean_ctor_get(v_value_351_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v_value_351_);
if (v_isSharedCheck_414_ == 0)
{
v___x_358_ = v_value_351_;
v_isShared_359_ = v_isSharedCheck_414_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_args_356_);
lean_inc(v_fvarId_355_);
lean_dec(v_value_351_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_414_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_360_ = lean_array_get_size(v_args_356_);
v___x_361_ = lean_array_get_size(v_params_352_);
v___x_362_ = lean_nat_dec_eq(v___x_360_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_365_; 
lean_dec_ref(v_args_356_);
lean_dec(v_fvarId_355_);
lean_dec(v_fvarId_354_);
lean_dec_ref(v_k_353_);
lean_dec_ref(v_params_352_);
v___x_363_ = lean_box(0);
if (v_isShared_359_ == 0)
{
lean_ctor_set_tag(v___x_358_, 0);
lean_ctor_set(v___x_358_, 1, v_a_340_);
lean_ctor_set(v___x_358_, 0, v___x_363_);
v___x_365_ = v___x_358_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_a_340_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
else
{
if (lean_obj_tag(v_k_353_) == 5)
{
lean_object* v_fvarId_367_; uint8_t v___x_368_; 
v_fvarId_367_ = lean_ctor_get(v_k_353_, 0);
lean_inc(v_fvarId_367_);
lean_dec_ref_known(v_k_353_, 1);
v___x_368_ = l_Lean_instBEqFVarId_beq(v_fvarId_367_, v_fvarId_354_);
lean_dec(v_fvarId_354_);
lean_dec(v_fvarId_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_371_; 
lean_dec_ref(v_args_356_);
lean_dec(v_fvarId_355_);
lean_dec_ref(v_params_352_);
v___x_369_ = lean_box(0);
if (v_isShared_359_ == 0)
{
lean_ctor_set_tag(v___x_358_, 0);
lean_ctor_set(v___x_358_, 1, v_a_340_);
lean_ctor_set(v___x_358_, 0, v___x_369_);
v___x_371_ = v___x_358_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_a_340_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
else
{
lean_object* v_assignment_373_; lean_object* v___x_374_; 
lean_del_object(v___x_358_);
v_assignment_373_ = lean_ctor_get(v_a_339_, 2);
v___x_374_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(v_assignment_373_, v_fvarId_355_);
lean_dec(v_fvarId_355_);
if (lean_obj_tag(v___x_374_) == 1)
{
lean_object* v_val_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_409_; 
v_val_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_409_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_409_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_val_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_409_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
if (lean_obj_tag(v_val_375_) == 2)
{
lean_object* v_i_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v_a_385_; lean_object* v_fst_386_; 
v_i_379_ = lean_ctor_get(v_val_375_, 0);
lean_inc(v_i_379_);
lean_dec_ref_known(v_val_375_, 1);
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = lean_unsigned_to_nat(1u);
v___x_382_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_361_);
lean_ctor_set(v___x_382_, 2, v___x_381_);
v___x_383_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__0));
v___x_384_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_352_, v_args_356_, v___x_368_, v___x_382_, v___x_383_, v___x_380_, v_a_340_);
lean_dec_ref_known(v___x_382_, 3);
lean_dec_ref(v_args_356_);
lean_dec_ref(v_params_352_);
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_fst_386_ = lean_ctor_get(v_a_385_, 0);
if (lean_obj_tag(v_fst_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_397_; 
v_a_387_ = lean_ctor_get(v___x_384_, 1);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v___x_384_, 0);
lean_dec(v_unused_398_);
v___x_389_ = v___x_384_;
v_isShared_390_ = v_isSharedCheck_397_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_384_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_397_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v_i_379_);
v___x_392_ = v___x_377_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_i_379_);
v___x_392_ = v_reuseFailAlloc_396_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_394_; 
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_392_);
v___x_394_ = v___x_389_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_a_387_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_407_; 
lean_inc_ref(v_fst_386_);
lean_dec(v_i_379_);
lean_del_object(v___x_377_);
v_a_399_ = lean_ctor_get(v___x_384_, 1);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; 
v_unused_408_ = lean_ctor_get(v___x_384_, 0);
lean_dec(v_unused_408_);
v___x_401_ = v___x_384_;
v_isShared_402_ = v_isSharedCheck_407_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_384_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_407_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v_val_403_; lean_object* v___x_405_; 
v_val_403_ = lean_ctor_get(v_fst_386_, 0);
lean_inc(v_val_403_);
lean_dec_ref_known(v_fst_386_, 1);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v_val_403_);
v___x_405_ = v___x_401_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_val_403_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_a_399_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
else
{
lean_del_object(v___x_377_);
lean_dec(v_val_375_);
lean_dec_ref(v_args_356_);
lean_dec_ref(v_params_352_);
v___y_346_ = v_a_340_;
goto v___jp_345_;
}
}
}
else
{
lean_dec(v___x_374_);
lean_dec_ref(v_args_356_);
lean_dec_ref(v_params_352_);
v___y_346_ = v_a_340_;
goto v___jp_345_;
}
}
}
else
{
lean_object* v___x_410_; lean_object* v___x_412_; 
lean_dec_ref(v_args_356_);
lean_dec(v_fvarId_355_);
lean_dec(v_fvarId_354_);
lean_dec_ref(v_k_353_);
lean_dec_ref(v_params_352_);
v___x_410_ = lean_box(0);
if (v_isShared_359_ == 0)
{
lean_ctor_set_tag(v___x_358_, 0);
lean_ctor_set(v___x_358_, 1, v_a_340_);
lean_ctor_set(v___x_358_, 0, v___x_410_);
v___x_412_ = v___x_358_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_a_340_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
else
{
lean_dec(v_value_351_);
lean_dec_ref_known(v_value_349_, 2);
lean_dec_ref(v_decl_350_);
lean_dec_ref(v_decl_338_);
v___y_342_ = v_a_340_;
goto v___jp_341_;
}
}
else
{
lean_dec_ref(v_value_349_);
lean_dec_ref(v_decl_338_);
v___y_342_ = v_a_340_;
goto v___jp_341_;
}
v___jp_341_:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_box(0);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v___y_342_);
return v___x_344_;
}
v___jp_345_:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_box(0);
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v___y_346_);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f___boxed(lean_object* v_decl_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(v_decl_415_, v_a_416_, v_a_417_);
lean_dec_ref(v_a_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0(lean_object* v_params_419_, lean_object* v_args_420_, uint8_t v___x_421_, lean_object* v_range_422_, lean_object* v_b_423_, lean_object* v_i_424_, lean_object* v_hs_425_, lean_object* v_hl_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_419_, v_args_420_, v___x_421_, v_range_422_, v_b_423_, v_i_424_, v___y_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___boxed(lean_object* v_params_430_, lean_object* v_args_431_, lean_object* v___x_432_, lean_object* v_range_433_, lean_object* v_b_434_, lean_object* v_i_435_, lean_object* v_hs_436_, lean_object* v_hl_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
uint8_t v___x_3462__boxed_440_; lean_object* v_res_441_; 
v___x_3462__boxed_440_ = lean_unbox(v___x_432_);
v_res_441_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0(v_params_430_, v_args_431_, v___x_3462__boxed_440_, v_range_433_, v_b_434_, v_i_435_, v_hs_436_, v_hl_437_, v___y_438_, v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec_ref(v_range_433_);
lean_dec_ref(v_args_431_);
lean_dec_ref(v_params_430_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(lean_object* v_upperBound_442_, lean_object* v_args_443_, lean_object* v_a_444_, lean_object* v_b_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_a_449_; lean_object* v_a_450_; uint8_t v___x_454_; 
v___x_454_ = lean_nat_dec_lt(v_a_444_, v_upperBound_442_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
lean_dec(v_a_444_);
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v_b_445_);
lean_ctor_set(v___x_455_, 1, v___y_447_);
return v___x_455_;
}
else
{
lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_456_ = lean_box(0);
v___x_457_ = lean_array_get_size(v_args_443_);
v___x_458_ = lean_nat_dec_lt(v_a_444_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v_visited_459_; lean_object* v_fixed_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_469_; 
v_visited_459_ = lean_ctor_get(v___y_447_, 0);
v_fixed_460_ = lean_ctor_get(v___y_447_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v___y_447_);
if (v_isSharedCheck_469_ == 0)
{
v___x_462_ = v___y_447_;
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_fixed_460_);
lean_inc(v_visited_459_);
lean_dec(v___y_447_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_464_ = lean_box(v___x_458_);
v___x_465_ = lean_array_set(v_fixed_460_, v_a_444_, v___x_464_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 1, v___x_465_);
v___x_467_ = v___x_462_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_visited_459_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
v_a_449_ = v___x_456_;
v_a_450_ = v___x_467_;
goto v___jp_448_;
}
}
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_array_fget_borrowed(v_args_443_, v_a_444_);
v___x_471_ = l_Lean_Compiler_LCNF_FixedParams_evalArg(v___x_470_, v___y_446_, v___y_447_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v_a_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
v_a_473_ = lean_ctor_get(v___x_471_, 1);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_471_, 2);
lean_inc(v_a_444_);
v___x_474_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_474_, 0, v_a_444_);
v___x_475_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v_a_472_, v___x_474_);
lean_dec_ref_known(v___x_474_, 1);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = lean_box(1);
v___x_477_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v_a_472_, v___x_476_);
lean_dec(v_a_472_);
if (v___x_477_ == 0)
{
lean_object* v_visited_478_; lean_object* v_fixed_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_488_; 
v_visited_478_ = lean_ctor_get(v_a_473_, 0);
v_fixed_479_ = lean_ctor_get(v_a_473_, 1);
v_isSharedCheck_488_ = !lean_is_exclusive(v_a_473_);
if (v_isSharedCheck_488_ == 0)
{
v___x_481_ = v_a_473_;
v_isShared_482_ = v_isSharedCheck_488_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_fixed_479_);
lean_inc(v_visited_478_);
lean_dec(v_a_473_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_488_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_483_ = lean_box(v___x_477_);
v___x_484_ = lean_array_set(v_fixed_479_, v_a_444_, v___x_483_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v___x_484_);
v___x_486_ = v___x_481_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_visited_478_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
v_a_449_ = v___x_456_;
v_a_450_ = v___x_486_;
goto v___jp_448_;
}
}
}
else
{
v_a_449_ = v___x_456_;
v_a_450_ = v_a_473_;
goto v___jp_448_;
}
}
else
{
lean_dec(v_a_472_);
v_a_449_ = v___x_456_;
v_a_450_ = v_a_473_;
goto v___jp_448_;
}
}
else
{
lean_object* v_a_489_; lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v_a_444_);
v_a_489_ = lean_ctor_get(v___x_471_, 0);
v_a_490_ = lean_ctor_get(v___x_471_, 1);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_471_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_inc(v_a_489_);
lean_dec(v___x_471_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_489_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
v___jp_448_:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_nat_add(v_a_444_, v___x_451_);
lean_dec(v_a_444_);
v_a_444_ = v___x_452_;
v_b_445_ = v_a_449_;
v___y_447_ = v_a_450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg___boxed(lean_object* v_upperBound_498_, lean_object* v_args_499_, lean_object* v_a_500_, lean_object* v_b_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(v_upperBound_498_, v_args_499_, v_a_500_, v_b_501_, v___y_502_, v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec_ref(v_args_499_);
lean_dec(v_upperBound_498_);
return v_res_504_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(lean_object* v_xs_505_, lean_object* v_ys_506_, lean_object* v_x_507_){
_start:
{
lean_object* v_zero_508_; uint8_t v_isZero_509_; 
v_zero_508_ = lean_unsigned_to_nat(0u);
v_isZero_509_ = lean_nat_dec_eq(v_x_507_, v_zero_508_);
if (v_isZero_509_ == 1)
{
lean_dec(v_x_507_);
return v_isZero_509_;
}
else
{
lean_object* v_one_510_; lean_object* v_n_511_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_one_510_ = lean_unsigned_to_nat(1u);
v_n_511_ = lean_nat_sub(v_x_507_, v_one_510_);
lean_dec(v_x_507_);
v___x_512_ = lean_array_fget_borrowed(v_xs_505_, v_n_511_);
v___x_513_ = lean_array_fget_borrowed(v_ys_506_, v_n_511_);
v___x_514_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v___x_512_, v___x_513_);
if (v___x_514_ == 0)
{
lean_dec(v_n_511_);
return v___x_514_;
}
else
{
v_x_507_ = v_n_511_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_xs_516_, lean_object* v_ys_517_, lean_object* v_x_518_){
_start:
{
uint8_t v_res_519_; lean_object* v_r_520_; 
v_res_519_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(v_xs_516_, v_ys_517_, v_x_518_);
lean_dec_ref(v_ys_517_);
lean_dec_ref(v_xs_516_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(lean_object* v_a_521_, lean_object* v_x_522_){
_start:
{
if (lean_obj_tag(v_x_522_) == 0)
{
uint8_t v___x_523_; 
v___x_523_ = 0;
return v___x_523_;
}
else
{
lean_object* v_key_524_; lean_object* v_tail_525_; uint8_t v___y_527_; lean_object* v_fst_529_; lean_object* v_snd_530_; lean_object* v_fst_531_; lean_object* v_snd_532_; uint8_t v___x_533_; 
v_key_524_ = lean_ctor_get(v_x_522_, 0);
v_tail_525_ = lean_ctor_get(v_x_522_, 2);
v_fst_529_ = lean_ctor_get(v_key_524_, 0);
v_snd_530_ = lean_ctor_get(v_key_524_, 1);
v_fst_531_ = lean_ctor_get(v_a_521_, 0);
v_snd_532_ = lean_ctor_get(v_a_521_, 1);
v___x_533_ = lean_name_eq(v_fst_529_, v_fst_531_);
if (v___x_533_ == 0)
{
v___y_527_ = v___x_533_;
goto v___jp_526_;
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_534_ = lean_array_get_size(v_snd_530_);
v___x_535_ = lean_array_get_size(v_snd_532_);
v___x_536_ = lean_nat_dec_eq(v___x_534_, v___x_535_);
if (v___x_536_ == 0)
{
v_x_522_ = v_tail_525_;
goto _start;
}
else
{
uint8_t v___x_538_; 
v___x_538_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(v_snd_530_, v_snd_532_, v___x_534_);
v___y_527_ = v___x_538_;
goto v___jp_526_;
}
}
v___jp_526_:
{
if (v___y_527_ == 0)
{
v_x_522_ = v_tail_525_;
goto _start;
}
else
{
return v___y_527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg___boxed(lean_object* v_a_539_, lean_object* v_x_540_){
_start:
{
uint8_t v_res_541_; lean_object* v_r_542_; 
v_res_541_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_539_, v_x_540_);
lean_dec(v_x_540_);
lean_dec_ref(v_a_539_);
v_r_542_ = lean_box(v_res_541_);
return v_r_542_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(lean_object* v_as_543_, size_t v_i_544_, size_t v_stop_545_, uint64_t v_b_546_){
_start:
{
uint8_t v___x_547_; 
v___x_547_ = lean_usize_dec_eq(v_i_544_, v_stop_545_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; uint64_t v___x_549_; uint64_t v___x_550_; size_t v___x_551_; size_t v___x_552_; 
v___x_548_ = lean_array_uget_borrowed(v_as_543_, v_i_544_);
v___x_549_ = l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash(v___x_548_);
v___x_550_ = lean_uint64_mix_hash(v_b_546_, v___x_549_);
v___x_551_ = ((size_t)1ULL);
v___x_552_ = lean_usize_add(v_i_544_, v___x_551_);
v_i_544_ = v___x_552_;
v_b_546_ = v___x_550_;
goto _start;
}
else
{
return v_b_546_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2___boxed(lean_object* v_as_554_, lean_object* v_i_555_, lean_object* v_stop_556_, lean_object* v_b_557_){
_start:
{
size_t v_i_boxed_558_; size_t v_stop_boxed_559_; uint64_t v_b_boxed_560_; uint64_t v_res_561_; lean_object* v_r_562_; 
v_i_boxed_558_ = lean_unbox_usize(v_i_555_);
lean_dec(v_i_555_);
v_stop_boxed_559_ = lean_unbox_usize(v_stop_556_);
lean_dec(v_stop_556_);
v_b_boxed_560_ = lean_unbox_uint64(v_b_557_);
lean_dec_ref(v_b_557_);
v_res_561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_as_554_, v_i_boxed_558_, v_stop_boxed_559_, v_b_boxed_560_);
lean_dec_ref(v_as_554_);
v_r_562_ = lean_box_uint64(v_res_561_);
return v_r_562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
if (lean_obj_tag(v_x_564_) == 0)
{
return v_x_563_;
}
else
{
lean_object* v_key_565_; lean_object* v_value_566_; lean_object* v_tail_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_606_; 
v_key_565_ = lean_ctor_get(v_x_564_, 0);
v_value_566_ = lean_ctor_get(v_x_564_, 1);
v_tail_567_ = lean_ctor_get(v_x_564_, 2);
v_isSharedCheck_606_ = !lean_is_exclusive(v_x_564_);
if (v_isSharedCheck_606_ == 0)
{
v___x_569_ = v_x_564_;
v_isShared_570_ = v_isSharedCheck_606_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_tail_567_);
lean_inc(v_value_566_);
lean_inc(v_key_565_);
lean_dec(v_x_564_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_606_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v_fst_571_; lean_object* v_snd_572_; lean_object* v___x_573_; uint64_t v___y_575_; uint64_t v___y_576_; uint64_t v___y_596_; 
v_fst_571_ = lean_ctor_get(v_key_565_, 0);
v_snd_572_ = lean_ctor_get(v_key_565_, 1);
v___x_573_ = lean_array_get_size(v_x_563_);
if (lean_obj_tag(v_fst_571_) == 0)
{
uint64_t v___x_604_; 
v___x_604_ = 1723ULL;
v___y_596_ = v___x_604_;
goto v___jp_595_;
}
else
{
uint64_t v_hash_605_; 
v_hash_605_ = lean_ctor_get_uint64(v_fst_571_, sizeof(void*)*2);
v___y_596_ = v_hash_605_;
goto v___jp_595_;
}
v___jp_574_:
{
uint64_t v___x_577_; uint64_t v___x_578_; uint64_t v___x_579_; uint64_t v_fold_580_; uint64_t v___x_581_; uint64_t v___x_582_; uint64_t v___x_583_; size_t v___x_584_; size_t v___x_585_; size_t v___x_586_; size_t v___x_587_; size_t v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_577_ = lean_uint64_mix_hash(v___y_575_, v___y_576_);
v___x_578_ = 32ULL;
v___x_579_ = lean_uint64_shift_right(v___x_577_, v___x_578_);
v_fold_580_ = lean_uint64_xor(v___x_577_, v___x_579_);
v___x_581_ = 16ULL;
v___x_582_ = lean_uint64_shift_right(v_fold_580_, v___x_581_);
v___x_583_ = lean_uint64_xor(v_fold_580_, v___x_582_);
v___x_584_ = lean_uint64_to_usize(v___x_583_);
v___x_585_ = lean_usize_of_nat(v___x_573_);
v___x_586_ = ((size_t)1ULL);
v___x_587_ = lean_usize_sub(v___x_585_, v___x_586_);
v___x_588_ = lean_usize_land(v___x_584_, v___x_587_);
v___x_589_ = lean_array_uget_borrowed(v_x_563_, v___x_588_);
lean_inc(v___x_589_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 2, v___x_589_);
v___x_591_ = v___x_569_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_key_565_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_value_566_);
lean_ctor_set(v_reuseFailAlloc_594_, 2, v___x_589_);
v___x_591_ = v_reuseFailAlloc_594_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; 
v___x_592_ = lean_array_uset(v_x_563_, v___x_588_, v___x_591_);
v_x_563_ = v___x_592_;
v_x_564_ = v_tail_567_;
goto _start;
}
}
v___jp_595_:
{
uint64_t v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_597_ = 7ULL;
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = lean_array_get_size(v_snd_572_);
v___x_600_ = lean_nat_dec_lt(v___x_598_, v___x_599_);
if (v___x_600_ == 0)
{
v___y_575_ = v___y_596_;
v___y_576_ = v___x_597_;
goto v___jp_574_;
}
else
{
size_t v___x_601_; size_t v___x_602_; uint64_t v___x_603_; 
v___x_601_ = ((size_t)0ULL);
v___x_602_ = lean_usize_of_nat(v___x_599_);
v___x_603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_572_, v___x_601_, v___x_602_, v___x_597_);
v___y_575_ = v___y_596_;
v___y_576_ = v___x_603_;
goto v___jp_574_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(lean_object* v_i_607_, lean_object* v_source_608_, lean_object* v_target_609_){
_start:
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_array_get_size(v_source_608_);
v___x_611_ = lean_nat_dec_lt(v_i_607_, v___x_610_);
if (v___x_611_ == 0)
{
lean_dec_ref(v_source_608_);
lean_dec(v_i_607_);
return v_target_609_;
}
else
{
lean_object* v_es_612_; lean_object* v___x_613_; lean_object* v_source_614_; lean_object* v_target_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_es_612_ = lean_array_fget(v_source_608_, v_i_607_);
v___x_613_ = lean_box(0);
v_source_614_ = lean_array_fset(v_source_608_, v_i_607_, v___x_613_);
v_target_615_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(v_target_609_, v_es_612_);
v___x_616_ = lean_unsigned_to_nat(1u);
v___x_617_ = lean_nat_add(v_i_607_, v___x_616_);
lean_dec(v_i_607_);
v_i_607_ = v___x_617_;
v_source_608_ = v_source_614_;
v_target_609_ = v_target_615_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(lean_object* v_data_619_){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_nbuckets_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_620_ = lean_array_get_size(v_data_619_);
v___x_621_ = lean_unsigned_to_nat(2u);
v_nbuckets_622_ = lean_nat_mul(v___x_620_, v___x_621_);
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = lean_box(0);
v___x_625_ = lean_mk_array(v_nbuckets_622_, v___x_624_);
v___x_626_ = lean_array_propagate_mark(v_data_619_, v___x_625_);
v___x_627_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(v___x_623_, v_data_619_, v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(lean_object* v_m_628_, lean_object* v_a_629_, lean_object* v_b_630_){
_start:
{
lean_object* v_size_631_; lean_object* v_buckets_632_; lean_object* v_fst_633_; lean_object* v_snd_634_; lean_object* v___x_635_; uint64_t v___y_637_; uint64_t v___y_638_; uint64_t v___y_677_; 
v_size_631_ = lean_ctor_get(v_m_628_, 0);
v_buckets_632_ = lean_ctor_get(v_m_628_, 1);
v_fst_633_ = lean_ctor_get(v_a_629_, 0);
v_snd_634_ = lean_ctor_get(v_a_629_, 1);
v___x_635_ = lean_array_get_size(v_buckets_632_);
if (lean_obj_tag(v_fst_633_) == 0)
{
uint64_t v___x_685_; 
v___x_685_ = 1723ULL;
v___y_677_ = v___x_685_;
goto v___jp_676_;
}
else
{
uint64_t v_hash_686_; 
v_hash_686_ = lean_ctor_get_uint64(v_fst_633_, sizeof(void*)*2);
v___y_677_ = v_hash_686_;
goto v___jp_676_;
}
v___jp_636_:
{
uint64_t v___x_639_; uint64_t v___x_640_; uint64_t v___x_641_; uint64_t v_fold_642_; uint64_t v___x_643_; uint64_t v___x_644_; uint64_t v___x_645_; size_t v___x_646_; size_t v___x_647_; size_t v___x_648_; size_t v___x_649_; size_t v___x_650_; lean_object* v_bkt_651_; uint8_t v___x_652_; 
v___x_639_ = lean_uint64_mix_hash(v___y_637_, v___y_638_);
v___x_640_ = 32ULL;
v___x_641_ = lean_uint64_shift_right(v___x_639_, v___x_640_);
v_fold_642_ = lean_uint64_xor(v___x_639_, v___x_641_);
v___x_643_ = 16ULL;
v___x_644_ = lean_uint64_shift_right(v_fold_642_, v___x_643_);
v___x_645_ = lean_uint64_xor(v_fold_642_, v___x_644_);
v___x_646_ = lean_uint64_to_usize(v___x_645_);
v___x_647_ = lean_usize_of_nat(v___x_635_);
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_sub(v___x_647_, v___x_648_);
v___x_650_ = lean_usize_land(v___x_646_, v___x_649_);
v_bkt_651_ = lean_array_uget_borrowed(v_buckets_632_, v___x_650_);
v___x_652_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_629_, v_bkt_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_673_; 
lean_inc_ref(v_buckets_632_);
lean_inc(v_size_631_);
v_isSharedCheck_673_ = !lean_is_exclusive(v_m_628_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; lean_object* v_unused_675_; 
v_unused_674_ = lean_ctor_get(v_m_628_, 1);
lean_dec(v_unused_674_);
v_unused_675_ = lean_ctor_get(v_m_628_, 0);
lean_dec(v_unused_675_);
v___x_654_ = v_m_628_;
v_isShared_655_ = v_isSharedCheck_673_;
goto v_resetjp_653_;
}
else
{
lean_dec(v_m_628_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_673_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v_size_x27_657_; lean_object* v___x_658_; lean_object* v_buckets_x27_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_656_ = lean_unsigned_to_nat(1u);
v_size_x27_657_ = lean_nat_add(v_size_631_, v___x_656_);
lean_dec(v_size_631_);
lean_inc(v_bkt_651_);
v___x_658_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_658_, 0, v_a_629_);
lean_ctor_set(v___x_658_, 1, v_b_630_);
lean_ctor_set(v___x_658_, 2, v_bkt_651_);
v_buckets_x27_659_ = lean_array_uset(v_buckets_632_, v___x_650_, v___x_658_);
v___x_660_ = lean_unsigned_to_nat(4u);
v___x_661_ = lean_nat_mul(v_size_x27_657_, v___x_660_);
v___x_662_ = lean_unsigned_to_nat(3u);
v___x_663_ = lean_nat_div(v___x_661_, v___x_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_array_get_size(v_buckets_x27_659_);
v___x_665_ = lean_nat_dec_le(v___x_663_, v___x_664_);
lean_dec(v___x_663_);
if (v___x_665_ == 0)
{
lean_object* v_val_666_; lean_object* v___x_668_; 
v_val_666_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(v_buckets_x27_659_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v_val_666_);
lean_ctor_set(v___x_654_, 0, v_size_x27_657_);
v___x_668_ = v___x_654_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_size_x27_657_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_val_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
else
{
lean_object* v___x_671_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v_buckets_x27_659_);
lean_ctor_set(v___x_654_, 0, v_size_x27_657_);
v___x_671_ = v___x_654_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_size_x27_657_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_buckets_x27_659_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
else
{
lean_dec(v_b_630_);
lean_dec_ref(v_a_629_);
return v_m_628_;
}
}
v___jp_676_:
{
uint64_t v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_678_ = 7ULL;
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = lean_array_get_size(v_snd_634_);
v___x_681_ = lean_nat_dec_lt(v___x_679_, v___x_680_);
if (v___x_681_ == 0)
{
v___y_637_ = v___y_677_;
v___y_638_ = v___x_678_;
goto v___jp_636_;
}
else
{
size_t v___x_682_; size_t v___x_683_; uint64_t v___x_684_; 
v___x_682_ = ((size_t)0ULL);
v___x_683_ = lean_usize_of_nat(v___x_680_);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_634_, v___x_682_, v___x_683_, v___x_678_);
v___y_637_ = v___y_677_;
v___y_638_ = v___x_684_;
goto v___jp_636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(lean_object* v_f_687_, lean_object* v_v_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
if (lean_obj_tag(v_v_688_) == 0)
{
lean_object* v_code_691_; lean_object* v___x_692_; 
v_code_691_ = lean_ctor_get(v_v_688_, 0);
lean_inc_ref(v_code_691_);
lean_dec_ref_known(v_v_688_, 1);
lean_inc_ref(v___y_689_);
v___x_692_ = lean_apply_3(v_f_687_, v_code_691_, v___y_689_, v___y_690_);
return v___x_692_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec_ref_known(v_v_688_, 1);
lean_dec_ref(v_f_687_);
v___x_693_ = lean_box(0);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v___y_690_);
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg___boxed(lean_object* v_f_695_, lean_object* v_v_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v_f_695_, v_v_696_, v___y_697_, v___y_698_);
lean_dec_ref(v___y_697_);
return v_res_699_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(lean_object* v_m_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_buckets_702_; lean_object* v_fst_703_; lean_object* v_snd_704_; lean_object* v___x_705_; uint64_t v___y_707_; uint64_t v___y_708_; uint64_t v___y_724_; 
v_buckets_702_ = lean_ctor_get(v_m_700_, 1);
v_fst_703_ = lean_ctor_get(v_a_701_, 0);
v_snd_704_ = lean_ctor_get(v_a_701_, 1);
v___x_705_ = lean_array_get_size(v_buckets_702_);
if (lean_obj_tag(v_fst_703_) == 0)
{
uint64_t v___x_732_; 
v___x_732_ = 1723ULL;
v___y_724_ = v___x_732_;
goto v___jp_723_;
}
else
{
uint64_t v_hash_733_; 
v_hash_733_ = lean_ctor_get_uint64(v_fst_703_, sizeof(void*)*2);
v___y_724_ = v_hash_733_;
goto v___jp_723_;
}
v___jp_706_:
{
uint64_t v___x_709_; uint64_t v___x_710_; uint64_t v___x_711_; uint64_t v_fold_712_; uint64_t v___x_713_; uint64_t v___x_714_; uint64_t v___x_715_; size_t v___x_716_; size_t v___x_717_; size_t v___x_718_; size_t v___x_719_; size_t v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_709_ = lean_uint64_mix_hash(v___y_707_, v___y_708_);
v___x_710_ = 32ULL;
v___x_711_ = lean_uint64_shift_right(v___x_709_, v___x_710_);
v_fold_712_ = lean_uint64_xor(v___x_709_, v___x_711_);
v___x_713_ = 16ULL;
v___x_714_ = lean_uint64_shift_right(v_fold_712_, v___x_713_);
v___x_715_ = lean_uint64_xor(v_fold_712_, v___x_714_);
v___x_716_ = lean_uint64_to_usize(v___x_715_);
v___x_717_ = lean_usize_of_nat(v___x_705_);
v___x_718_ = ((size_t)1ULL);
v___x_719_ = lean_usize_sub(v___x_717_, v___x_718_);
v___x_720_ = lean_usize_land(v___x_716_, v___x_719_);
v___x_721_ = lean_array_uget_borrowed(v_buckets_702_, v___x_720_);
v___x_722_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_701_, v___x_721_);
return v___x_722_;
}
v___jp_723_:
{
uint64_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_725_ = 7ULL;
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = lean_array_get_size(v_snd_704_);
v___x_728_ = lean_nat_dec_lt(v___x_726_, v___x_727_);
if (v___x_728_ == 0)
{
v___y_707_ = v___y_724_;
v___y_708_ = v___x_725_;
goto v___jp_706_;
}
else
{
size_t v___x_729_; size_t v___x_730_; uint64_t v___x_731_; 
v___x_729_ = ((size_t)0ULL);
v___x_730_ = lean_usize_of_nat(v___x_727_);
v___x_731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_704_, v___x_729_, v___x_730_, v___x_725_);
v___y_707_ = v___y_724_;
v___y_708_ = v___x_731_;
goto v___jp_706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg___boxed(lean_object* v_m_734_, lean_object* v_a_735_){
_start:
{
uint8_t v_res_736_; lean_object* v_r_737_; 
v_res_736_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_m_734_, v_a_735_);
lean_dec_ref(v_a_735_);
lean_dec_ref(v_m_734_);
v_r_737_ = lean_box(v_res_736_);
return v_r_737_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(lean_object* v_upperBound_738_, lean_object* v_args_739_, lean_object* v_a_740_, lean_object* v_b_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_a_745_; lean_object* v_a_746_; uint8_t v___x_750_; 
v___x_750_ = lean_nat_dec_lt(v_a_740_, v_upperBound_738_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; 
lean_dec(v_a_740_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v_b_741_);
lean_ctor_set(v___x_751_, 1, v___y_743_);
return v___x_751_;
}
else
{
lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_752_ = lean_array_get_size(v_args_739_);
v___x_753_ = lean_nat_dec_lt(v_a_740_, v___x_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_box(0);
v___x_755_ = lean_array_push(v_b_741_, v___x_754_);
v_a_745_ = v___x_755_;
v_a_746_ = v___y_743_;
goto v___jp_744_;
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_array_fget_borrowed(v_args_739_, v_a_740_);
v___x_757_ = l_Lean_Compiler_LCNF_FixedParams_evalArg(v___x_756_, v___y_742_, v___y_743_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v_a_759_; lean_object* v___x_760_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
v_a_759_ = lean_ctor_get(v___x_757_, 1);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_757_, 2);
v___x_760_ = lean_array_push(v_b_741_, v_a_758_);
v_a_745_ = v___x_760_;
v_a_746_ = v_a_759_;
goto v___jp_744_;
}
else
{
lean_object* v_a_761_; lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec_ref(v_b_741_);
lean_dec(v_a_740_);
v_a_761_ = lean_ctor_get(v___x_757_, 0);
v_a_762_ = lean_ctor_get(v___x_757_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_757_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_inc(v_a_761_);
lean_dec(v___x_757_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_761_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
v___jp_744_:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_unsigned_to_nat(1u);
v___x_748_ = lean_nat_add(v_a_740_, v___x_747_);
lean_dec(v_a_740_);
v_a_740_ = v___x_748_;
v_b_741_ = v_a_745_;
v___y_743_ = v_a_746_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg___boxed(lean_object* v_upperBound_770_, lean_object* v_args_771_, lean_object* v_a_772_, lean_object* v_b_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v_upperBound_770_, v_args_771_, v_a_772_, v_b_773_, v___y_774_, v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec_ref(v_args_771_);
lean_dec(v_upperBound_770_);
return v_res_776_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(uint8_t v_a_777_, uint8_t v___x_778_, lean_object* v_as_779_, size_t v_i_780_, size_t v_stop_781_){
_start:
{
uint8_t v___x_782_; 
v___x_782_ = lean_usize_dec_eq(v_i_780_, v_stop_781_);
if (v___x_782_ == 0)
{
uint8_t v___x_783_; uint8_t v___y_785_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_783_ = 1;
v___x_789_ = lean_array_uget_borrowed(v_as_779_, v_i_780_);
v___x_790_ = lean_unbox(v___x_789_);
if (v___x_790_ == 0)
{
if (v_a_777_ == 0)
{
v___y_785_ = v___x_778_;
goto v___jp_784_;
}
else
{
uint8_t v___x_791_; 
v___x_791_ = lean_unbox(v___x_789_);
v___y_785_ = v___x_791_;
goto v___jp_784_;
}
}
else
{
v___y_785_ = v_a_777_;
goto v___jp_784_;
}
v___jp_784_:
{
if (v___y_785_ == 0)
{
size_t v___x_786_; size_t v___x_787_; 
v___x_786_ = ((size_t)1ULL);
v___x_787_ = lean_usize_add(v_i_780_, v___x_786_);
v_i_780_ = v___x_787_;
goto _start;
}
else
{
return v___x_783_;
}
}
}
else
{
uint8_t v___x_792_; 
v___x_792_ = 0;
return v___x_792_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9___boxed(lean_object* v_a_793_, lean_object* v___x_794_, lean_object* v_as_795_, lean_object* v_i_796_, lean_object* v_stop_797_){
_start:
{
uint8_t v_a_boxed_798_; uint8_t v___x_13266__boxed_799_; size_t v_i_boxed_800_; size_t v_stop_boxed_801_; uint8_t v_res_802_; lean_object* v_r_803_; 
v_a_boxed_798_ = lean_unbox(v_a_793_);
v___x_13266__boxed_799_ = lean_unbox(v___x_794_);
v_i_boxed_800_ = lean_unbox_usize(v_i_796_);
lean_dec(v_i_796_);
v_stop_boxed_801_ = lean_unbox_usize(v_stop_797_);
lean_dec(v_stop_797_);
v_res_802_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(v_a_boxed_798_, v___x_13266__boxed_799_, v_as_795_, v_i_boxed_800_, v_stop_boxed_801_);
lean_dec_ref(v_as_795_);
v_r_803_ = lean_box(v_res_802_);
return v_r_803_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(uint8_t v___x_804_, lean_object* v_as_805_, uint8_t v_a_806_){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = lean_array_get_size(v_as_805_);
v___x_809_ = lean_nat_dec_lt(v___x_807_, v___x_808_);
if (v___x_809_ == 0)
{
return v___x_809_;
}
else
{
if (v___x_809_ == 0)
{
return v___x_809_;
}
else
{
size_t v___x_810_; size_t v___x_811_; uint8_t v___x_812_; 
v___x_810_ = ((size_t)0ULL);
v___x_811_ = lean_usize_of_nat(v___x_808_);
v___x_812_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(v_a_806_, v___x_804_, v_as_805_, v___x_810_, v___x_811_);
return v___x_812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___boxed(lean_object* v___x_813_, lean_object* v_as_814_, lean_object* v_a_815_){
_start:
{
uint8_t v___x_13291__boxed_816_; uint8_t v_a_boxed_817_; uint8_t v_res_818_; lean_object* v_r_819_; 
v___x_13291__boxed_816_ = lean_unbox(v___x_813_);
v_a_boxed_817_ = lean_unbox(v_a_815_);
v_res_818_ = l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(v___x_13291__boxed_816_, v_as_814_, v_a_boxed_817_);
lean_dec_ref(v_as_814_);
v_r_819_ = lean_box(v_res_818_);
return v_r_819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0___boxed(lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_c_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0(v_a_822_, v_a_823_, v_c_824_, v___y_825_, v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec_ref(v_a_822_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(lean_object* v_declName_828_, lean_object* v_args_829_, lean_object* v_as_830_, size_t v_sz_831_, size_t v_i_832_, lean_object* v_b_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_a_837_; lean_object* v_a_838_; uint8_t v___x_842_; 
v___x_842_ = lean_usize_dec_lt(v_i_832_, v_sz_831_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; 
lean_dec(v_declName_828_);
v___x_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_843_, 0, v_b_833_);
lean_ctor_set(v___x_843_, 1, v___y_835_);
return v___x_843_;
}
else
{
lean_object* v_a_844_; lean_object* v_toSignature_845_; lean_object* v_value_846_; lean_object* v_name_847_; lean_object* v_params_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v_a_844_ = lean_array_uget_borrowed(v_as_830_, v_i_832_);
v_toSignature_845_ = lean_ctor_get(v_a_844_, 0);
v_value_846_ = lean_ctor_get(v_a_844_, 1);
v_name_847_ = lean_ctor_get(v_toSignature_845_, 0);
v_params_848_ = lean_ctor_get(v_toSignature_845_, 3);
v___x_849_ = lean_box(0);
v___x_850_ = lean_name_eq(v_declName_828_, v_name_847_);
if (v___x_850_ == 0)
{
v_a_837_ = v___x_849_;
v_a_838_ = v___y_835_;
goto v___jp_836_;
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_851_ = lean_array_get_size(v_params_848_);
v___x_852_ = lean_unsigned_to_nat(0u);
v___x_853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0));
v___x_854_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v___x_851_, v_args_829_, v___x_852_, v___x_853_, v___y_834_, v___y_835_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v_a_856_; lean_object* v_visited_857_; lean_object* v_fixed_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v_a_855_ = lean_ctor_get(v___x_854_, 1);
lean_inc(v_a_855_);
v_a_856_ = lean_ctor_get(v___x_854_, 0);
lean_inc_n(v_a_856_, 2);
lean_dec_ref_known(v___x_854_, 2);
v_visited_857_ = lean_ctor_get(v_a_855_, 0);
v_fixed_858_ = lean_ctor_get(v_a_855_, 1);
lean_inc(v_declName_828_);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v_declName_828_);
lean_ctor_set(v___x_859_, 1, v_a_856_);
v___x_860_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_visited_857_, v___x_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_871_; 
lean_inc_ref(v_fixed_858_);
lean_inc_ref(v_visited_857_);
v_isSharedCheck_871_ = !lean_is_exclusive(v_a_855_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; lean_object* v_unused_873_; 
v_unused_872_ = lean_ctor_get(v_a_855_, 1);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_a_855_, 0);
lean_dec(v_unused_873_);
v___x_862_ = v_a_855_;
v_isShared_863_ = v_isSharedCheck_871_;
goto v_resetjp_861_;
}
else
{
lean_dec(v_a_855_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_871_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___f_864_; lean_object* v___x_865_; lean_object* v___x_867_; 
lean_inc(v_a_844_);
v___f_864_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0___boxed), 5, 2);
lean_closure_set(v___f_864_, 0, v_a_844_);
lean_closure_set(v___f_864_, 1, v_a_856_);
v___x_865_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(v_visited_857_, v___x_859_, v___x_849_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_865_);
v___x_867_ = v___x_862_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_fixed_858_);
v___x_867_ = v_reuseFailAlloc_870_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; 
lean_inc_ref(v_value_846_);
v___x_868_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v___f_864_, v_value_846_, v___y_834_, v___x_867_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; 
v_a_869_ = lean_ctor_get(v___x_868_, 1);
lean_inc(v_a_869_);
lean_dec_ref_known(v___x_868_, 2);
v_a_837_ = v___x_849_;
v_a_838_ = v_a_869_;
goto v___jp_836_;
}
else
{
lean_dec(v_declName_828_);
return v___x_868_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_859_, 2);
lean_dec(v_a_856_);
v_a_837_ = v___x_849_;
v_a_838_ = v_a_855_;
goto v___jp_836_;
}
}
else
{
lean_object* v_a_874_; lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec(v_declName_828_);
v_a_874_ = lean_ctor_get(v___x_854_, 0);
v_a_875_ = lean_ctor_get(v___x_854_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_854_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_inc(v_a_874_);
lean_dec(v___x_854_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_874_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
v___jp_836_:
{
size_t v___x_839_; size_t v___x_840_; 
v___x_839_ = ((size_t)1ULL);
v___x_840_ = lean_usize_add(v_i_832_, v___x_839_);
v_i_832_ = v___x_840_;
v_b_833_ = v_a_837_;
v___y_835_ = v_a_838_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp(lean_object* v_declName_883_, lean_object* v_args_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v___y_888_; lean_object* v_decls_889_; lean_object* v___y_890_; lean_object* v_main_904_; lean_object* v_toSignature_905_; lean_object* v_decls_906_; lean_object* v_name_907_; lean_object* v_params_908_; uint8_t v___x_909_; 
v_main_904_ = lean_ctor_get(v_a_885_, 1);
v_toSignature_905_ = lean_ctor_get(v_main_904_, 0);
v_decls_906_ = lean_ctor_get(v_a_885_, 0);
v_name_907_ = lean_ctor_get(v_toSignature_905_, 0);
v_params_908_ = lean_ctor_get(v_toSignature_905_, 3);
v___x_909_ = lean_name_eq(v_declName_883_, v_name_907_);
if (v___x_909_ == 0)
{
v___y_888_ = v_a_885_;
v_decls_889_ = v_decls_906_;
v___y_890_ = v_a_886_;
goto v___jp_887_;
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_910_ = lean_array_get_size(v_params_908_);
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = lean_box(0);
v___x_913_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(v___x_910_, v_args_884_, v___x_911_, v___x_912_, v_a_885_, v_a_886_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_923_; 
v_a_914_ = lean_ctor_get(v___x_913_, 1);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v___x_913_, 0);
lean_dec(v_unused_924_);
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_923_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_923_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v_fixed_918_; uint8_t v___x_919_; 
v_fixed_918_ = lean_ctor_get(v_a_914_, 1);
v___x_919_ = l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(v___x_909_, v_fixed_918_, v___x_909_);
if (v___x_919_ == 0)
{
lean_object* v___x_921_; 
lean_dec(v_declName_883_);
if (v_isShared_917_ == 0)
{
lean_ctor_set_tag(v___x_916_, 1);
lean_ctor_set(v___x_916_, 0, v___x_912_);
v___x_921_ = v___x_916_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_a_914_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
else
{
lean_del_object(v___x_916_);
v___y_888_ = v_a_885_;
v_decls_889_ = v_decls_906_;
v___y_890_ = v_a_914_;
goto v___jp_887_;
}
}
}
else
{
lean_dec(v_declName_883_);
return v___x_913_;
}
}
v___jp_887_:
{
lean_object* v___x_891_; size_t v_sz_892_; size_t v___x_893_; lean_object* v___x_894_; 
v___x_891_ = lean_box(0);
v_sz_892_ = lean_array_size(v_decls_889_);
v___x_893_ = ((size_t)0ULL);
v___x_894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(v_declName_883_, v_args_884_, v_decls_889_, v_sz_892_, v___x_893_, v___x_891_, v___y_888_, v___y_890_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
v_a_895_ = lean_ctor_get(v___x_894_, 1);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v___x_894_, 0);
lean_dec(v_unused_903_);
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_891_);
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
else
{
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalLetValue(lean_object* v_e_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
if (lean_obj_tag(v_e_925_) == 3)
{
lean_object* v_declName_928_; lean_object* v_args_929_; lean_object* v___x_930_; 
v_declName_928_ = lean_ctor_get(v_e_925_, 0);
lean_inc(v_declName_928_);
v_args_929_ = lean_ctor_get(v_e_925_, 2);
lean_inc_ref(v_args_929_);
lean_dec_ref_known(v_e_925_, 3);
v___x_930_ = l_Lean_Compiler_LCNF_FixedParams_evalApp(v_declName_928_, v_args_929_, v_a_926_, v_a_927_);
lean_dec_ref(v_args_929_);
return v___x_930_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec(v_e_925_);
v___x_931_ = lean_box(0);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v_a_927_);
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(lean_object* v_as_933_, size_t v_i_934_, size_t v_stop_935_, lean_object* v_b_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___y_940_; uint8_t v___x_947_; 
v___x_947_ = lean_usize_dec_eq(v_i_934_, v_stop_935_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; 
v___x_948_ = lean_array_uget_borrowed(v_as_933_, v_i_934_);
switch(lean_obj_tag(v___x_948_))
{
case 0:
{
lean_object* v_code_949_; 
v_code_949_ = lean_ctor_get(v___x_948_, 2);
lean_inc_ref(v_code_949_);
v___y_940_ = v_code_949_;
goto v___jp_939_;
}
case 1:
{
lean_object* v_code_950_; 
v_code_950_ = lean_ctor_get(v___x_948_, 1);
lean_inc_ref(v_code_950_);
v___y_940_ = v_code_950_;
goto v___jp_939_;
}
default: 
{
lean_object* v_code_951_; 
v_code_951_ = lean_ctor_get(v___x_948_, 0);
lean_inc_ref(v_code_951_);
v___y_940_ = v_code_951_;
goto v___jp_939_;
}
}
}
else
{
lean_object* v___x_952_; 
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v_b_936_);
lean_ctor_set(v___x_952_, 1, v___y_938_);
return v___x_952_;
}
v___jp_939_:
{
lean_object* v___x_941_; 
lean_inc_ref(v___y_937_);
v___x_941_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v___y_940_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v_a_943_; size_t v___x_944_; size_t v___x_945_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
v_a_943_ = lean_ctor_get(v___x_941_, 1);
lean_inc(v_a_943_);
lean_dec_ref_known(v___x_941_, 2);
v___x_944_ = ((size_t)1ULL);
v___x_945_ = lean_usize_add(v_i_934_, v___x_944_);
v_i_934_ = v___x_945_;
v_b_936_ = v_a_942_;
v___y_938_ = v_a_943_;
goto _start;
}
else
{
return v___x_941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalCode(lean_object* v_code_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
switch(lean_obj_tag(v_code_953_))
{
case 0:
{
lean_object* v_decl_956_; lean_object* v_k_957_; lean_object* v_value_958_; lean_object* v___x_959_; 
v_decl_956_ = lean_ctor_get(v_code_953_, 0);
lean_inc_ref(v_decl_956_);
v_k_957_ = lean_ctor_get(v_code_953_, 1);
lean_inc_ref(v_k_957_);
lean_dec_ref_known(v_code_953_, 2);
v_value_958_ = lean_ctor_get(v_decl_956_, 3);
lean_inc(v_value_958_);
lean_dec_ref(v_decl_956_);
v___x_959_ = l_Lean_Compiler_LCNF_FixedParams_evalLetValue(v_value_958_, v_a_954_, v_a_955_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; 
v_a_960_ = lean_ctor_get(v___x_959_, 1);
lean_inc(v_a_960_);
lean_dec_ref_known(v___x_959_, 2);
v_code_953_ = v_k_957_;
v_a_955_ = v_a_960_;
goto _start;
}
else
{
lean_dec_ref(v_k_957_);
lean_dec_ref(v_a_954_);
return v___x_959_;
}
}
case 1:
{
lean_object* v_decl_962_; lean_object* v_k_963_; lean_object* v___x_964_; 
v_decl_962_ = lean_ctor_get(v_code_953_, 0);
lean_inc_ref_n(v_decl_962_, 2);
v_k_963_ = lean_ctor_get(v_code_953_, 1);
lean_inc_ref(v_k_963_);
lean_dec_ref_known(v_code_953_, 2);
v___x_964_ = l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(v_decl_962_, v_a_954_, v_a_955_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
if (lean_obj_tag(v_a_965_) == 1)
{
lean_object* v_a_966_; lean_object* v_val_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_981_; 
v_a_966_ = lean_ctor_get(v___x_964_, 1);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_964_, 2);
v_val_967_ = lean_ctor_get(v_a_965_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v_a_965_);
if (v_isSharedCheck_981_ == 0)
{
v___x_969_ = v_a_965_;
v_isShared_970_ = v_isSharedCheck_981_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_val_967_);
lean_dec(v_a_965_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_981_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v_fvarId_971_; lean_object* v_decls_972_; lean_object* v_main_973_; lean_object* v_assignment_974_; lean_object* v___x_976_; 
v_fvarId_971_ = lean_ctor_get(v_decl_962_, 0);
lean_inc(v_fvarId_971_);
lean_dec_ref(v_decl_962_);
v_decls_972_ = lean_ctor_get(v_a_954_, 0);
lean_inc_ref(v_decls_972_);
v_main_973_ = lean_ctor_get(v_a_954_, 1);
lean_inc_ref(v_main_973_);
v_assignment_974_ = lean_ctor_get(v_a_954_, 2);
lean_inc(v_assignment_974_);
lean_dec_ref(v_a_954_);
if (v_isShared_970_ == 0)
{
lean_ctor_set_tag(v___x_969_, 2);
v___x_976_ = v___x_969_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_val_967_);
v___x_976_ = v_reuseFailAlloc_980_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_971_, v___x_976_, v_assignment_974_);
v___x_978_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_978_, 0, v_decls_972_);
lean_ctor_set(v___x_978_, 1, v_main_973_);
lean_ctor_set(v___x_978_, 2, v___x_977_);
v_code_953_ = v_k_963_;
v_a_954_ = v___x_978_;
v_a_955_ = v_a_966_;
goto _start;
}
}
}
else
{
lean_object* v_a_982_; lean_object* v_value_983_; lean_object* v___x_984_; 
lean_dec(v_a_965_);
v_a_982_ = lean_ctor_get(v___x_964_, 1);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_964_, 2);
v_value_983_ = lean_ctor_get(v_decl_962_, 4);
lean_inc_ref(v_value_983_);
lean_dec_ref(v_decl_962_);
lean_inc_ref(v_a_954_);
v___x_984_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_value_983_, v_a_954_, v_a_982_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; 
v_a_985_ = lean_ctor_get(v___x_984_, 1);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 2);
v_code_953_ = v_k_963_;
v_a_955_ = v_a_985_;
goto _start;
}
else
{
lean_dec_ref(v_k_963_);
lean_dec_ref(v_a_954_);
return v___x_984_;
}
}
}
else
{
lean_object* v_a_987_; lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v_k_963_);
lean_dec_ref(v_decl_962_);
lean_dec_ref(v_a_954_);
v_a_987_ = lean_ctor_get(v___x_964_, 0);
v_a_988_ = lean_ctor_get(v___x_964_, 1);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_964_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_inc(v_a_987_);
lean_dec(v___x_964_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_987_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
case 2:
{
lean_object* v_decl_996_; lean_object* v_k_997_; lean_object* v_value_998_; lean_object* v___x_999_; 
v_decl_996_ = lean_ctor_get(v_code_953_, 0);
lean_inc_ref(v_decl_996_);
v_k_997_ = lean_ctor_get(v_code_953_, 1);
lean_inc_ref(v_k_997_);
lean_dec_ref_known(v_code_953_, 2);
v_value_998_ = lean_ctor_get(v_decl_996_, 4);
lean_inc_ref(v_value_998_);
lean_dec_ref(v_decl_996_);
lean_inc_ref(v_a_954_);
v___x_999_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_value_998_, v_a_954_, v_a_955_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 1);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 2);
v_code_953_ = v_k_997_;
v_a_955_ = v_a_1000_;
goto _start;
}
else
{
lean_dec_ref(v_k_997_);
lean_dec_ref(v_a_954_);
return v___x_999_;
}
}
case 3:
{
lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1009_; 
lean_dec_ref(v_a_954_);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_code_953_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; lean_object* v_unused_1011_; 
v_unused_1010_ = lean_ctor_get(v_code_953_, 1);
lean_dec(v_unused_1010_);
v_unused_1011_ = lean_ctor_get(v_code_953_, 0);
lean_dec(v_unused_1011_);
v___x_1003_ = v_code_953_;
v_isShared_1004_ = v_isSharedCheck_1009_;
goto v_resetjp_1002_;
}
else
{
lean_dec(v_code_953_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1009_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1005_ = lean_box(0);
if (v_isShared_1004_ == 0)
{
lean_ctor_set_tag(v___x_1003_, 0);
lean_ctor_set(v___x_1003_, 1, v_a_955_);
lean_ctor_set(v___x_1003_, 0, v___x_1005_);
v___x_1007_ = v___x_1003_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_a_955_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
case 4:
{
lean_object* v_cases_1012_; lean_object* v_alts_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v_cases_1012_ = lean_ctor_get(v_code_953_, 0);
lean_inc_ref(v_cases_1012_);
lean_dec_ref_known(v_code_953_, 1);
v_alts_1013_ = lean_ctor_get(v_cases_1012_, 3);
lean_inc_ref(v_alts_1013_);
lean_dec_ref(v_cases_1012_);
v___x_1014_ = lean_unsigned_to_nat(0u);
v___x_1015_ = lean_array_get_size(v_alts_1013_);
v___x_1016_ = lean_box(0);
v___x_1017_ = lean_nat_dec_lt(v___x_1014_, v___x_1015_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
lean_dec_ref(v_alts_1013_);
lean_dec_ref(v_a_954_);
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v_a_955_);
return v___x_1018_;
}
else
{
uint8_t v___x_1019_; 
v___x_1019_ = lean_nat_dec_le(v___x_1015_, v___x_1015_);
if (v___x_1019_ == 0)
{
if (v___x_1017_ == 0)
{
lean_object* v___x_1020_; 
lean_dec_ref(v_alts_1013_);
lean_dec_ref(v_a_954_);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1016_);
lean_ctor_set(v___x_1020_, 1, v_a_955_);
return v___x_1020_;
}
else
{
size_t v___x_1021_; size_t v___x_1022_; lean_object* v___x_1023_; 
v___x_1021_ = ((size_t)0ULL);
v___x_1022_ = lean_usize_of_nat(v___x_1015_);
v___x_1023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(v_alts_1013_, v___x_1021_, v___x_1022_, v___x_1016_, v_a_954_, v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec_ref(v_alts_1013_);
return v___x_1023_;
}
}
else
{
size_t v___x_1024_; size_t v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = ((size_t)0ULL);
v___x_1025_ = lean_usize_of_nat(v___x_1015_);
v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(v_alts_1013_, v___x_1024_, v___x_1025_, v___x_1016_, v_a_954_, v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec_ref(v_alts_1013_);
return v___x_1026_;
}
}
}
default: 
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec_ref(v_a_954_);
lean_dec_ref(v_code_953_);
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v_a_955_);
return v___x_1028_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0(lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_c_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_decls_1034_; lean_object* v_main_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v_decls_1034_ = lean_ctor_get(v___y_1032_, 0);
v_main_1035_ = lean_ctor_get(v___y_1032_, 1);
v___x_1036_ = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(v_a_1029_, v_a_1030_);
lean_inc_ref(v_main_1035_);
lean_inc_ref(v_decls_1034_);
v___x_1037_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1037_, 0, v_decls_1034_);
lean_ctor_set(v___x_1037_, 1, v_main_1035_);
lean_ctor_set(v___x_1037_, 2, v___x_1036_);
v___x_1038_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_c_1031_, v___x_1037_, v___y_1033_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalLetValue___boxed(lean_object* v_e_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_Compiler_LCNF_FixedParams_evalLetValue(v_e_1039_, v_a_1040_, v_a_1041_);
lean_dec_ref(v_a_1040_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9___boxed(lean_object* v_as_1043_, lean_object* v_i_1044_, lean_object* v_stop_1045_, lean_object* v_b_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
size_t v_i_boxed_1049_; size_t v_stop_boxed_1050_; lean_object* v_res_1051_; 
v_i_boxed_1049_ = lean_unbox_usize(v_i_1044_);
lean_dec(v_i_1044_);
v_stop_boxed_1050_ = lean_unbox_usize(v_stop_1045_);
lean_dec(v_stop_1045_);
v_res_1051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(v_as_1043_, v_i_boxed_1049_, v_stop_boxed_1050_, v_b_1046_, v___y_1047_, v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec_ref(v_as_1043_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp___boxed(lean_object* v_declName_1052_, lean_object* v_args_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_Compiler_LCNF_FixedParams_evalApp(v_declName_1052_, v_args_1053_, v_a_1054_, v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec_ref(v_args_1053_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___boxed(lean_object* v_declName_1057_, lean_object* v_args_1058_, lean_object* v_as_1059_, lean_object* v_sz_1060_, lean_object* v_i_1061_, lean_object* v_b_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
size_t v_sz_boxed_1065_; size_t v_i_boxed_1066_; lean_object* v_res_1067_; 
v_sz_boxed_1065_ = lean_unbox_usize(v_sz_1060_);
lean_dec(v_sz_1060_);
v_i_boxed_1066_ = lean_unbox_usize(v_i_1061_);
lean_dec(v_i_1061_);
v_res_1067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(v_declName_1057_, v_args_1058_, v_as_1059_, v_sz_boxed_1065_, v_i_boxed_1066_, v_b_1062_, v___y_1063_, v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec_ref(v_as_1059_);
lean_dec_ref(v_args_1058_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3(uint8_t v_pu_1068_, lean_object* v_f_1069_, lean_object* v_v_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v_f_1069_, v_v_1070_, v___y_1071_, v___y_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___boxed(lean_object* v_pu_1074_, lean_object* v_f_1075_, lean_object* v_v_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
uint8_t v_pu_boxed_1079_; lean_object* v_res_1080_; 
v_pu_boxed_1079_ = lean_unbox(v_pu_1074_);
v_res_1080_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3(v_pu_boxed_1079_, v_f_1075_, v_v_1076_, v___y_1077_, v___y_1078_);
lean_dec_ref(v___y_1077_);
return v_res_1080_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1(lean_object* v_00_u03b2_1081_, lean_object* v_m_1082_, lean_object* v_a_1083_){
_start:
{
uint8_t v___x_1084_; 
v___x_1084_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_m_1082_, v_a_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___boxed(lean_object* v_00_u03b2_1085_, lean_object* v_m_1086_, lean_object* v_a_1087_){
_start:
{
uint8_t v_res_1088_; lean_object* v_r_1089_; 
v_res_1088_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1(v_00_u03b2_1085_, v_m_1086_, v_a_1087_);
lean_dec_ref(v_a_1087_);
lean_dec_ref(v_m_1086_);
v_r_1089_ = lean_box(v_res_1088_);
return v_r_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2(lean_object* v_00_u03b2_1090_, lean_object* v_m_1091_, lean_object* v_a_1092_, lean_object* v_b_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(v_m_1091_, v_a_1092_, v_b_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4(lean_object* v_upperBound_1095_, lean_object* v_args_1096_, lean_object* v_inst_1097_, lean_object* v_R_1098_, lean_object* v_a_1099_, lean_object* v_b_1100_, lean_object* v_c_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v_upperBound_1095_, v_args_1096_, v_a_1099_, v_b_1100_, v___y_1102_, v___y_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___boxed(lean_object* v_upperBound_1105_, lean_object* v_args_1106_, lean_object* v_inst_1107_, lean_object* v_R_1108_, lean_object* v_a_1109_, lean_object* v_b_1110_, lean_object* v_c_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4(v_upperBound_1105_, v_args_1106_, v_inst_1107_, v_R_1108_, v_a_1109_, v_b_1110_, v_c_1111_, v___y_1112_, v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec_ref(v_args_1106_);
lean_dec(v_upperBound_1105_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7(lean_object* v_upperBound_1115_, lean_object* v_args_1116_, lean_object* v_inst_1117_, lean_object* v_R_1118_, lean_object* v_a_1119_, lean_object* v_b_1120_, lean_object* v_c_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(v_upperBound_1115_, v_args_1116_, v_a_1119_, v_b_1120_, v___y_1122_, v___y_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___boxed(lean_object* v_upperBound_1125_, lean_object* v_args_1126_, lean_object* v_inst_1127_, lean_object* v_R_1128_, lean_object* v_a_1129_, lean_object* v_b_1130_, lean_object* v_c_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7(v_upperBound_1125_, v_args_1126_, v_inst_1127_, v_R_1128_, v_a_1129_, v_b_1130_, v_c_1131_, v___y_1132_, v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec_ref(v_args_1126_);
lean_dec(v_upperBound_1125_);
return v_res_1134_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1(lean_object* v_00_u03b2_1135_, lean_object* v_a_1136_, lean_object* v_x_1137_){
_start:
{
uint8_t v___x_1138_; 
v___x_1138_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_1136_, v_x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1139_, lean_object* v_a_1140_, lean_object* v_x_1141_){
_start:
{
uint8_t v_res_1142_; lean_object* v_r_1143_; 
v_res_1142_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1(v_00_u03b2_1139_, v_a_1140_, v_x_1141_);
lean_dec(v_x_1141_);
lean_dec_ref(v_a_1140_);
v_r_1143_ = lean_box(v_res_1142_);
return v_r_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4(lean_object* v_00_u03b2_1144_, lean_object* v_data_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(v_data_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4(lean_object* v_xs_1147_, lean_object* v_ys_1148_, lean_object* v_hsz_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_){
_start:
{
uint8_t v___x_1152_; 
v___x_1152_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(v_xs_1147_, v_ys_1148_, v_x_1150_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___boxed(lean_object* v_xs_1153_, lean_object* v_ys_1154_, lean_object* v_hsz_1155_, lean_object* v_x_1156_, lean_object* v_x_1157_){
_start:
{
uint8_t v_res_1158_; lean_object* v_r_1159_; 
v_res_1158_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4(v_xs_1153_, v_ys_1154_, v_hsz_1155_, v_x_1156_, v_x_1157_);
lean_dec_ref(v_ys_1154_);
lean_dec_ref(v_xs_1153_);
v_r_1159_ = lean_box(v_res_1158_);
return v_r_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_1160_, lean_object* v_i_1161_, lean_object* v_source_1162_, lean_object* v_target_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(v_i_1161_, v_source_1162_, v_target_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14(lean_object* v_00_u03b2_1165_, lean_object* v_x_1166_, lean_object* v_x_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(v_x_1166_, v_x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(lean_object* v_upperBound_1169_, lean_object* v_a_1170_, lean_object* v_b_1171_){
_start:
{
uint8_t v___x_1172_; 
v___x_1172_ = lean_nat_dec_lt(v_a_1170_, v_upperBound_1169_);
if (v___x_1172_ == 0)
{
lean_dec(v_a_1170_);
return v_b_1171_;
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_inc(v_a_1170_);
v___x_1173_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1173_, 0, v_a_1170_);
v___x_1174_ = lean_array_push(v_b_1171_, v___x_1173_);
v___x_1175_ = lean_unsigned_to_nat(1u);
v___x_1176_ = lean_nat_add(v_a_1170_, v___x_1175_);
lean_dec(v_a_1170_);
v_a_1170_ = v___x_1176_;
v_b_1171_ = v___x_1174_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg___boxed(lean_object* v_upperBound_1178_, lean_object* v_a_1179_, lean_object* v_b_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_upperBound_1178_, v_a_1179_, v_b_1180_);
lean_dec(v_upperBound_1178_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(lean_object* v_numParams_1182_){
_start:
{
lean_object* v___x_1183_; lean_object* v_values_1184_; lean_object* v___x_1185_; 
v___x_1183_ = lean_unsigned_to_nat(0u);
v_values_1184_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0));
v___x_1185_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_numParams_1182_, v___x_1183_, v_values_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkInitialValues___boxed(lean_object* v_numParams_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(v_numParams_1186_);
lean_dec(v_numParams_1186_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0(lean_object* v_upperBound_1188_, lean_object* v_inst_1189_, lean_object* v_R_1190_, lean_object* v_a_1191_, lean_object* v_b_1192_, lean_object* v_c_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_upperBound_1188_, v_a_1191_, v_b_1192_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___boxed(lean_object* v_upperBound_1195_, lean_object* v_inst_1196_, lean_object* v_R_1197_, lean_object* v_a_1198_, lean_object* v_b_1199_, lean_object* v_c_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0(v_upperBound_1195_, v_inst_1196_, v_R_1197_, v_a_1198_, v_b_1199_, v_c_1200_);
lean_dec(v_upperBound_1195_);
return v_res_1201_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1202_ = lean_box(0);
v___x_1203_ = lean_unsigned_to_nat(16u);
v___x_1204_ = lean_mk_array(v___x_1203_, v___x_1202_);
return v___x_1204_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0);
v___x_1206_ = lean_unsigned_to_nat(0u);
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
lean_ctor_set(v___x_1207_, 1, v___x_1205_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(lean_object* v_decls_1208_, lean_object* v_as_1209_, size_t v_sz_1210_, size_t v_i_1211_, lean_object* v_b_1212_){
_start:
{
lean_object* v_a_1214_; uint8_t v___x_1218_; 
v___x_1218_ = lean_usize_dec_lt(v_i_1211_, v_sz_1210_);
if (v___x_1218_ == 0)
{
lean_dec_ref(v_decls_1208_);
return v_b_1212_;
}
else
{
lean_object* v_a_1219_; lean_object* v_toSignature_1220_; lean_object* v_value_1221_; lean_object* v_name_1222_; lean_object* v_params_1223_; lean_object* v_s_1225_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v_a_1219_ = lean_array_uget_borrowed(v_as_1209_, v_i_1211_);
v_toSignature_1220_ = lean_ctor_get(v_a_1219_, 0);
v_value_1221_ = lean_ctor_get(v_a_1219_, 1);
v_name_1222_ = lean_ctor_get(v_toSignature_1220_, 0);
v_params_1223_ = lean_ctor_get(v_toSignature_1220_, 3);
v___x_1228_ = lean_array_get_size(v_params_1223_);
v___x_1229_ = l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(v___x_1228_);
v___x_1230_ = lean_box(v___x_1218_);
v___x_1231_ = lean_mk_array(v___x_1228_, v___x_1230_);
if (lean_obj_tag(v_value_1221_) == 0)
{
lean_object* v_code_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v_a_1238_; 
v_code_1232_ = lean_ctor_get(v_value_1221_, 0);
v___x_1233_ = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(v_a_1219_, v___x_1229_);
lean_inc(v_a_1219_);
lean_inc_ref(v_decls_1208_);
v___x_1234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1234_, 0, v_decls_1208_);
lean_ctor_set(v___x_1234_, 1, v_a_1219_);
lean_ctor_set(v___x_1234_, 2, v___x_1233_);
v___x_1235_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1);
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
lean_ctor_set(v___x_1236_, 1, v___x_1231_);
lean_inc_ref(v_code_1232_);
v___x_1237_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_code_1232_, v___x_1234_, v___x_1236_);
v_a_1238_ = lean_ctor_get(v___x_1237_, 1);
lean_inc(v_a_1238_);
lean_dec_ref(v___x_1237_);
v_s_1225_ = v_a_1238_;
goto v___jp_1224_;
}
else
{
lean_object* v___x_1239_; 
lean_dec_ref(v___x_1229_);
lean_inc(v_name_1222_);
v___x_1239_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1222_, v___x_1231_, v_b_1212_);
v_a_1214_ = v___x_1239_;
goto v___jp_1213_;
}
v___jp_1224_:
{
lean_object* v_fixed_1226_; lean_object* v___x_1227_; 
v_fixed_1226_ = lean_ctor_get(v_s_1225_, 1);
lean_inc_ref(v_fixed_1226_);
lean_dec_ref(v_s_1225_);
lean_inc(v_name_1222_);
v___x_1227_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1222_, v_fixed_1226_, v_b_1212_);
v_a_1214_ = v___x_1227_;
goto v___jp_1213_;
}
}
v___jp_1213_:
{
size_t v___x_1215_; size_t v___x_1216_; 
v___x_1215_ = ((size_t)1ULL);
v___x_1216_ = lean_usize_add(v_i_1211_, v___x_1215_);
v_i_1211_ = v___x_1216_;
v_b_1212_ = v_a_1214_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___boxed(lean_object* v_decls_1240_, lean_object* v_as_1241_, lean_object* v_sz_1242_, lean_object* v_i_1243_, lean_object* v_b_1244_){
_start:
{
size_t v_sz_boxed_1245_; size_t v_i_boxed_1246_; lean_object* v_res_1247_; 
v_sz_boxed_1245_ = lean_unbox_usize(v_sz_1242_);
lean_dec(v_sz_1242_);
v_i_boxed_1246_ = lean_unbox_usize(v_i_1243_);
lean_dec(v_i_1243_);
v_res_1247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(v_decls_1240_, v_as_1241_, v_sz_boxed_1245_, v_i_boxed_1246_, v_b_1244_);
lean_dec_ref(v_as_1241_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFixedParamsMap(lean_object* v_decls_1248_){
_start:
{
lean_object* v_result_1249_; size_t v_sz_1250_; size_t v___x_1251_; lean_object* v___x_1252_; 
v_result_1249_ = lean_box(1);
v_sz_1250_ = lean_array_size(v_decls_1248_);
v___x_1251_ = ((size_t)0ULL);
lean_inc_ref(v_decls_1248_);
v___x_1252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(v_decls_1248_, v_decls_1248_, v_sz_1250_, v___x_1251_, v_result_1249_);
lean_dec_ref(v_decls_1248_);
return v___x_1252_;
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
