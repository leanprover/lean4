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
uint8_t l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(lean_object* v_x_47_, lean_object* v_x_48_){
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_47_ = stack[0].m_obj;
lean_object* v_x_48_ = stack[1].m_obj;
uint8_t v_res_57_;
v_res_57_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v_x_47_, v_x_48_);
stack->m_num = v_res_57_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq___boxed(lean_object* v_x_58_, lean_object* v_x_59_){
_start:
{
uint8_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v_x_58_, v_x_59_);
lean_dec(v_x_59_);
lean_dec(v_x_58_);
v_r_61_ = lean_box(v_res_60_);
return v_r_61_;
}
}
uint64_t l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash(lean_object* v_x_64_){
_start:
{
switch(lean_obj_tag(v_x_64_))
{
case 0:
{
uint64_t v___x_65_; 
v___x_65_ = 0ULL;
return v___x_65_;
}
case 1:
{
uint64_t v___x_66_; 
v___x_66_ = 1ULL;
return v___x_66_;
}
default: 
{
lean_object* v_i_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v___x_70_; 
v_i_67_ = lean_ctor_get(v_x_64_, 0);
v___x_68_ = 2ULL;
v___x_69_ = lean_uint64_of_nat(v_i_67_);
v___x_70_ = lean_uint64_mix_hash(v___x_68_, v___x_69_);
return v___x_70_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_64_ = stack[0].m_obj;
uint64_t v_res_71_;
v_res_71_ = l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash(v_x_64_);
stack->m_num = v_res_71_;
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
uint8_t l_Lean_Compiler_LCNF_FixedParams_abort___redArg___lam__0(uint8_t v_x_77_){
_start:
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FixedParams_abort___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_77_ = stack[0].m_num;
uint8_t v_res_79_;
v_res_79_ = l_Lean_Compiler_LCNF_FixedParams_abort___redArg___lam__0(v_x_77_);
stack->m_num = v_res_79_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___redArg___lam__0___boxed(lean_object* v_x_80_){
_start:
{
uint8_t v_x_273__boxed_81_; uint8_t v_res_82_; lean_object* v_r_83_; 
v_x_273__boxed_81_ = lean_unbox(v_x_80_);
v_res_82_ = l_Lean_Compiler_LCNF_FixedParams_abort___redArg___lam__0(v_x_273__boxed_81_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___redArg(lean_object* v_a_104_){
_start:
{
lean_object* v_visited_105_; lean_object* v_fixed_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_120_; 
v_visited_105_ = lean_ctor_get(v_a_104_, 0);
v_fixed_106_ = lean_ctor_get(v_a_104_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_a_104_);
if (v_isSharedCheck_120_ == 0)
{
v___x_108_ = v_a_104_;
v_isShared_109_ = v_isSharedCheck_120_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_fixed_106_);
lean_inc(v_visited_105_);
lean_dec(v_a_104_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_120_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___f_110_; lean_object* v___x_111_; size_t v_sz_112_; size_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_116_; 
v___f_110_ = ((lean_object*)(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__0));
v___x_111_ = ((lean_object*)(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__10));
v_sz_112_ = lean_array_size(v_fixed_106_);
v___x_113_ = ((size_t)0ULL);
v___x_114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_111_, v___f_110_, v_sz_112_, v___x_113_, v_fixed_106_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 1, v___x_114_);
v___x_116_ = v___x_108_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_visited_105_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v___x_114_);
v___x_116_ = v_reuseFailAlloc_119_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_box(0);
v___x_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v___x_116_);
return v___x_118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort(lean_object* v_00_u03b1_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_visited_124_; lean_object* v_fixed_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_139_; 
v_visited_124_ = lean_ctor_get(v_a_123_, 0);
v_fixed_125_ = lean_ctor_get(v_a_123_, 1);
v_isSharedCheck_139_ = !lean_is_exclusive(v_a_123_);
if (v_isSharedCheck_139_ == 0)
{
v___x_127_ = v_a_123_;
v_isShared_128_ = v_isSharedCheck_139_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_fixed_125_);
lean_inc(v_visited_124_);
lean_dec(v_a_123_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_139_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___f_129_; lean_object* v___x_130_; size_t v_sz_131_; size_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v___f_129_ = ((lean_object*)(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__0));
v___x_130_ = ((lean_object*)(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__10));
v_sz_131_ = lean_array_size(v_fixed_125_);
v___x_132_ = ((size_t)0ULL);
v___x_133_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_130_, v___f_129_, v_sz_131_, v___x_132_, v_fixed_125_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v___x_133_);
v___x_135_ = v___x_127_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_visited_124_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_133_);
v___x_135_ = v_reuseFailAlloc_138_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_box(0);
v___x_137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_135_);
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_abort___boxed(lean_object* v_00_u03b1_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Compiler_LCNF_FixedParams_abort(v_00_u03b1_140_, v_a_141_, v_a_142_);
lean_dec_ref(v_a_141_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(lean_object* v_t_144_, lean_object* v_k_145_){
_start:
{
if (lean_obj_tag(v_t_144_) == 0)
{
lean_object* v_k_146_; lean_object* v_v_147_; lean_object* v_l_148_; lean_object* v_r_149_; uint8_t v___x_150_; 
v_k_146_ = lean_ctor_get(v_t_144_, 1);
v_v_147_ = lean_ctor_get(v_t_144_, 2);
v_l_148_ = lean_ctor_get(v_t_144_, 3);
v_r_149_ = lean_ctor_get(v_t_144_, 4);
v___x_150_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_145_, v_k_146_);
switch(v___x_150_)
{
case 0:
{
v_t_144_ = v_l_148_;
goto _start;
}
case 1:
{
lean_object* v___x_152_; 
lean_inc(v_v_147_);
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v_v_147_);
return v___x_152_;
}
default: 
{
v_t_144_ = v_r_149_;
goto _start;
}
}
}
else
{
lean_object* v___x_154_; 
v___x_154_ = lean_box(0);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg___boxed(lean_object* v_t_155_, lean_object* v_k_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(v_t_155_, v_k_156_);
lean_dec(v_k_156_);
lean_dec(v_t_155_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalFVar(lean_object* v_fvarId_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_assignment_161_; lean_object* v___x_162_; 
v_assignment_161_ = lean_ctor_get(v_a_159_, 2);
v___x_162_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(v_assignment_161_, v_fvarId_158_);
if (lean_obj_tag(v___x_162_) == 1)
{
lean_object* v_val_163_; lean_object* v___x_164_; 
v_val_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_val_163_);
lean_dec_ref_known(v___x_162_, 1);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v_val_163_);
lean_ctor_set(v___x_164_, 1, v_a_160_);
return v___x_164_;
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec(v___x_162_);
v___x_165_ = lean_box(0);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v_a_160_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalFVar___boxed(lean_object* v_fvarId_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_Compiler_LCNF_FixedParams_evalFVar(v_fvarId_167_, v_a_168_, v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_fvarId_167_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0(lean_object* v_00_u03b4_171_, lean_object* v_t_172_, lean_object* v_k_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(v_t_172_, v_k_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___boxed(lean_object* v_00_u03b4_175_, lean_object* v_t_176_, lean_object* v_k_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0(v_00_u03b4_175_, v_t_176_, v_k_177_);
lean_dec(v_k_177_);
lean_dec(v_t_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalArg(lean_object* v_arg_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
switch(lean_obj_tag(v_arg_179_))
{
case 0:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_box(1);
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v_a_181_);
return v___x_183_;
}
case 1:
{
lean_object* v_fvarId_184_; lean_object* v___x_185_; 
v_fvarId_184_ = lean_ctor_get(v_arg_179_, 0);
v___x_185_ = l_Lean_Compiler_LCNF_FixedParams_evalFVar(v_fvarId_184_, v_a_180_, v_a_181_);
return v___x_185_;
}
default: 
{
lean_object* v_expr_186_; 
v_expr_186_ = lean_ctor_get(v_arg_179_, 0);
if (lean_obj_tag(v_expr_186_) == 1)
{
lean_object* v_fvarId_187_; lean_object* v___x_188_; 
v_fvarId_187_ = lean_ctor_get(v_expr_186_, 0);
v___x_188_ = l_Lean_Compiler_LCNF_FixedParams_evalFVar(v_fvarId_187_, v_a_180_, v_a_181_);
return v___x_188_;
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_box(0);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v_a_181_);
return v___x_190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalArg___boxed(lean_object* v_arg_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Compiler_LCNF_FixedParams_evalArg(v_arg_191_, v_a_192_, v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_arg_191_);
return v_res_194_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0(lean_object* v_declName_195_, lean_object* v_as_196_, size_t v_i_197_, size_t v_stop_198_){
_start:
{
uint8_t v___x_199_; 
v___x_199_ = lean_usize_dec_eq(v_i_197_, v_stop_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v_toSignature_201_; lean_object* v_name_202_; uint8_t v___x_203_; 
v___x_200_ = lean_array_uget_borrowed(v_as_196_, v_i_197_);
v_toSignature_201_ = lean_ctor_get(v___x_200_, 0);
v_name_202_ = lean_ctor_get(v_toSignature_201_, 0);
v___x_203_ = lean_name_eq(v_name_202_, v_declName_195_);
if (v___x_203_ == 0)
{
size_t v___x_204_; size_t v___x_205_; 
v___x_204_ = ((size_t)1ULL);
v___x_205_ = lean_usize_add(v_i_197_, v___x_204_);
v_i_197_ = v___x_205_;
goto _start;
}
else
{
return v___x_203_;
}
}
else
{
uint8_t v___x_207_; 
v___x_207_ = 0;
return v___x_207_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_195_ = stack[0].m_obj;
lean_object* v_as_196_ = stack[1].m_obj;
size_t v_i_197_ = stack[2].m_num;
size_t v_stop_198_ = stack[3].m_num;
uint8_t v_res_208_;
v_res_208_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0(v_declName_195_, v_as_196_, v_i_197_, v_stop_198_);
stack->m_num = v_res_208_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0___boxed(lean_object* v_declName_209_, lean_object* v_as_210_, lean_object* v_i_211_, lean_object* v_stop_212_){
_start:
{
size_t v_i_boxed_213_; size_t v_stop_boxed_214_; uint8_t v_res_215_; lean_object* v_r_216_; 
v_i_boxed_213_ = lean_unbox_usize(v_i_211_);
lean_dec(v_i_211_);
v_stop_boxed_214_ = lean_unbox_usize(v_stop_212_);
lean_dec(v_stop_212_);
v_res_215_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0(v_declName_209_, v_as_210_, v_i_boxed_213_, v_stop_boxed_214_);
lean_dec_ref(v_as_210_);
lean_dec(v_declName_209_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_inMutualBlock(lean_object* v_declName_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_decls_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v_decls_220_ = lean_ctor_get(v_a_218_, 0);
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_array_get_size(v_decls_220_);
v___x_223_ = lean_nat_dec_lt(v___x_221_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_box(v___x_223_);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v_a_219_);
return v___x_225_;
}
else
{
if (v___x_223_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_box(v___x_223_);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v_a_219_);
return v___x_227_;
}
else
{
size_t v___x_228_; size_t v___x_229_; uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_228_ = ((size_t)0ULL);
v___x_229_ = lean_usize_of_nat(v___x_222_);
v___x_230_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0(v_declName_217_, v_decls_220_, v___x_228_, v___x_229_);
v___x_231_ = lean_box(v___x_230_);
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v_a_219_);
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_inMutualBlock___boxed(lean_object* v_declName_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Compiler_LCNF_FixedParams_inMutualBlock(v_declName_233_, v_a_234_, v_a_235_);
lean_dec_ref(v_a_234_);
lean_dec(v_declName_233_);
return v_res_236_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0(lean_object* v_as_237_, size_t v_sz_238_, size_t v_i_239_, lean_object* v_b_240_){
_start:
{
uint8_t v___x_241_; 
v___x_241_ = lean_usize_dec_lt(v_i_239_, v_sz_238_);
if (v___x_241_ == 0)
{
return v_b_240_;
}
else
{
lean_object* v_snd_242_; lean_object* v_fst_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_276_; 
v_snd_242_ = lean_ctor_get(v_b_240_, 1);
v_fst_243_ = lean_ctor_get(v_b_240_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v_b_240_);
if (v_isSharedCheck_276_ == 0)
{
v___x_245_ = v_b_240_;
v_isShared_246_ = v_isSharedCheck_276_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_snd_242_);
lean_inc(v_fst_243_);
lean_dec(v_b_240_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_276_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v_array_247_; lean_object* v_start_248_; lean_object* v_stop_249_; uint8_t v___x_250_; 
v_array_247_ = lean_ctor_get(v_snd_242_, 0);
v_start_248_ = lean_ctor_get(v_snd_242_, 1);
v_stop_249_ = lean_ctor_get(v_snd_242_, 2);
v___x_250_ = lean_nat_dec_lt(v_start_248_, v_stop_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_252_; 
if (v_isShared_246_ == 0)
{
v___x_252_ = v___x_245_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_fst_243_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_snd_242_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
else
{
lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_272_; 
lean_inc(v_stop_249_);
lean_inc(v_start_248_);
lean_inc_ref(v_array_247_);
v_isSharedCheck_272_ = !lean_is_exclusive(v_snd_242_);
if (v_isSharedCheck_272_ == 0)
{
lean_object* v_unused_273_; lean_object* v_unused_274_; lean_object* v_unused_275_; 
v_unused_273_ = lean_ctor_get(v_snd_242_, 2);
lean_dec(v_unused_273_);
v_unused_274_ = lean_ctor_get(v_snd_242_, 1);
lean_dec(v_unused_274_);
v_unused_275_ = lean_ctor_get(v_snd_242_, 0);
lean_dec(v_unused_275_);
v___x_255_ = v_snd_242_;
v_isShared_256_ = v_isSharedCheck_272_;
goto v_resetjp_254_;
}
else
{
lean_dec(v_snd_242_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_272_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v_a_257_; lean_object* v_fvarId_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v_a_257_ = lean_array_uget_borrowed(v_as_237_, v_i_239_);
v_fvarId_258_ = lean_ctor_get(v_a_257_, 0);
v___x_259_ = lean_array_fget(v_array_247_, v_start_248_);
v___x_260_ = lean_unsigned_to_nat(1u);
v___x_261_ = lean_nat_add(v_start_248_, v___x_260_);
lean_dec(v_start_248_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 1, v___x_261_);
v___x_263_ = v___x_255_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_array_247_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v_stop_249_);
v___x_263_ = v_reuseFailAlloc_271_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; lean_object* v___x_266_; 
lean_inc(v_fvarId_258_);
v___x_264_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_258_, v___x_259_, v_fst_243_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 1, v___x_263_);
lean_ctor_set(v___x_245_, 0, v___x_264_);
v___x_266_ = v___x_245_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v___x_263_);
v___x_266_ = v_reuseFailAlloc_270_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
size_t v___x_267_; size_t v___x_268_; 
v___x_267_ = ((size_t)1ULL);
v___x_268_ = lean_usize_add(v_i_239_, v___x_267_);
v_i_239_ = v___x_268_;
v_b_240_ = v___x_266_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_237_ = stack[0].m_obj;
size_t v_sz_238_ = stack[1].m_num;
size_t v_i_239_ = stack[2].m_num;
lean_object* v_b_240_ = stack[3].m_obj;
lean_object* v_res_277_;
v_res_277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0(v_as_237_, v_sz_238_, v_i_239_, v_b_240_);
stack->m_obj
 = v_res_277_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0___boxed(lean_object* v_as_278_, lean_object* v_sz_279_, lean_object* v_i_280_, lean_object* v_b_281_){
_start:
{
size_t v_sz_boxed_282_; size_t v_i_boxed_283_; lean_object* v_res_284_; 
v_sz_boxed_282_ = lean_unbox_usize(v_sz_279_);
lean_dec(v_sz_279_);
v_i_boxed_283_ = lean_unbox_usize(v_i_280_);
lean_dec(v_i_280_);
v_res_284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0(v_as_278_, v_sz_boxed_282_, v_i_boxed_283_, v_b_281_);
lean_dec_ref(v_as_278_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkAssignment(lean_object* v_decl_285_, lean_object* v_values_286_){
_start:
{
lean_object* v_toSignature_287_; lean_object* v_params_288_; lean_object* v___x_289_; lean_object* v_assignment_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; size_t v_sz_294_; size_t v___x_295_; lean_object* v___x_296_; lean_object* v_fst_297_; 
v_toSignature_287_ = lean_ctor_get(v_decl_285_, 0);
v_params_288_ = lean_ctor_get(v_toSignature_287_, 3);
v___x_289_ = lean_array_get_size(v_values_286_);
v_assignment_290_ = lean_box(1);
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = l_Array_toSubarray___redArg(v_values_286_, v___x_291_, v___x_289_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v_assignment_290_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v_sz_294_ = lean_array_size(v_params_288_);
v___x_295_ = ((size_t)0ULL);
v___x_296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0(v_params_288_, v_sz_294_, v___x_295_, v___x_293_);
v_fst_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_fst_297_);
lean_dec_ref(v___x_296_);
return v_fst_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkAssignment___boxed(lean_object* v_decl_298_, lean_object* v_values_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(v_decl_298_, v_values_299_);
lean_dec_ref(v_decl_298_);
return v_res_300_;
}
}
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(lean_object* v_params_309_, lean_object* v_args_310_, uint8_t v___x_311_, lean_object* v_range_312_, lean_object* v_b_313_, lean_object* v_i_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_stop_316_; lean_object* v_step_317_; uint8_t v___x_318_; 
v_stop_316_ = lean_ctor_get(v_range_312_, 1);
v_step_317_ = lean_ctor_get(v_range_312_, 2);
v___x_318_ = lean_nat_dec_lt(v_i_314_, v_stop_316_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; 
lean_dec(v_i_314_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v_b_313_);
lean_ctor_set(v___x_319_, 1, v___y_315_);
return v___x_319_;
}
else
{
lean_object* v___x_320_; lean_object* v_fvarId_321_; lean_object* v___x_322_; lean_object* v_a_324_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
lean_dec_ref(v_b_313_);
v___x_320_ = lean_array_fget_borrowed(v_params_309_, v_i_314_);
v_fvarId_321_ = lean_ctor_get(v___x_320_, 0);
v___x_322_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__0));
v___x_327_ = lean_box(0);
v___x_328_ = lean_array_get_borrowed(v___x_327_, v_args_310_, v_i_314_);
lean_inc(v_fvarId_321_);
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v_fvarId_321_);
v___x_330_ = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(v___x_328_, v___x_329_);
lean_dec_ref_known(v___x_329_, 1);
if (v___x_330_ == 0)
{
if (v___x_311_ == 0)
{
v_a_324_ = v___y_315_;
goto v___jp_323_;
}
else
{
uint8_t v___x_331_; 
v___x_331_ = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(v___x_328_, v___x_327_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec(v_i_314_);
v___x_332_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__2));
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___y_315_);
return v___x_333_;
}
else
{
v_a_324_ = v___y_315_;
goto v___jp_323_;
}
}
}
else
{
v_a_324_ = v___y_315_;
goto v___jp_323_;
}
v___jp_323_:
{
lean_object* v___x_325_; 
v___x_325_ = lean_nat_add(v_i_314_, v_step_317_);
lean_dec(v_i_314_);
v_b_313_ = v___x_322_;
v_i_314_ = v___x_325_;
v___y_315_ = v_a_324_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_309_ = stack[0].m_obj;
lean_object* v_args_310_ = stack[1].m_obj;
uint8_t v___x_311_ = stack[2].m_num;
lean_object* v_range_312_ = stack[3].m_obj;
lean_object* v_b_313_ = stack[4].m_obj;
lean_object* v_i_314_ = stack[5].m_obj;
lean_object* v___y_315_ = stack[6].m_obj;
lean_object* v_res_334_;
v_res_334_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_309_, v_args_310_, v___x_311_, v_range_312_, v_b_313_, v_i_314_, v___y_315_);
stack->m_obj
 = v_res_334_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___boxed(lean_object* v_params_335_, lean_object* v_args_336_, lean_object* v___x_337_, lean_object* v_range_338_, lean_object* v_b_339_, lean_object* v_i_340_, lean_object* v___y_341_){
_start:
{
uint8_t v___x_3258__boxed_342_; lean_object* v_res_343_; 
v___x_3258__boxed_342_ = lean_unbox(v___x_337_);
v_res_343_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_335_, v_args_336_, v___x_3258__boxed_342_, v_range_338_, v_b_339_, v_i_340_, v___y_341_);
lean_dec_ref(v_range_338_);
lean_dec_ref(v_args_336_);
lean_dec_ref(v_params_335_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(lean_object* v_decl_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v___y_348_; lean_object* v___y_352_; lean_object* v_value_355_; 
v_value_355_ = lean_ctor_get(v_decl_344_, 4);
lean_inc_ref(v_value_355_);
if (lean_obj_tag(v_value_355_) == 0)
{
lean_object* v_decl_356_; lean_object* v_value_357_; 
v_decl_356_ = lean_ctor_get(v_value_355_, 0);
lean_inc_ref(v_decl_356_);
v_value_357_ = lean_ctor_get(v_decl_356_, 3);
lean_inc(v_value_357_);
if (lean_obj_tag(v_value_357_) == 4)
{
lean_object* v_params_358_; lean_object* v_k_359_; lean_object* v_fvarId_360_; lean_object* v_fvarId_361_; lean_object* v_args_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_420_; 
v_params_358_ = lean_ctor_get(v_decl_344_, 2);
lean_inc_ref(v_params_358_);
lean_dec_ref(v_decl_344_);
v_k_359_ = lean_ctor_get(v_value_355_, 1);
lean_inc_ref(v_k_359_);
lean_dec_ref_known(v_value_355_, 2);
v_fvarId_360_ = lean_ctor_get(v_decl_356_, 0);
lean_inc(v_fvarId_360_);
lean_dec_ref(v_decl_356_);
v_fvarId_361_ = lean_ctor_get(v_value_357_, 0);
v_args_362_ = lean_ctor_get(v_value_357_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v_value_357_);
if (v_isSharedCheck_420_ == 0)
{
v___x_364_ = v_value_357_;
v_isShared_365_ = v_isSharedCheck_420_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_args_362_);
lean_inc(v_fvarId_361_);
lean_dec(v_value_357_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_420_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_366_ = lean_array_get_size(v_args_362_);
v___x_367_ = lean_array_get_size(v_params_358_);
v___x_368_ = lean_nat_dec_eq(v___x_366_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_371_; 
lean_dec_ref(v_args_362_);
lean_dec(v_fvarId_361_);
lean_dec(v_fvarId_360_);
lean_dec_ref(v_k_359_);
lean_dec_ref(v_params_358_);
v___x_369_ = lean_box(0);
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 0);
lean_ctor_set(v___x_364_, 1, v_a_346_);
lean_ctor_set(v___x_364_, 0, v___x_369_);
v___x_371_ = v___x_364_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_a_346_);
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
if (lean_obj_tag(v_k_359_) == 5)
{
lean_object* v_fvarId_373_; uint8_t v___x_374_; 
v_fvarId_373_ = lean_ctor_get(v_k_359_, 0);
lean_inc(v_fvarId_373_);
lean_dec_ref_known(v_k_359_, 1);
v___x_374_ = l_Lean_instBEqFVarId_beq(v_fvarId_373_, v_fvarId_360_);
lean_dec(v_fvarId_360_);
lean_dec(v_fvarId_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v___x_377_; 
lean_dec_ref(v_args_362_);
lean_dec(v_fvarId_361_);
lean_dec_ref(v_params_358_);
v___x_375_ = lean_box(0);
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 0);
lean_ctor_set(v___x_364_, 1, v_a_346_);
lean_ctor_set(v___x_364_, 0, v___x_375_);
v___x_377_ = v___x_364_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_a_346_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
else
{
lean_object* v_assignment_379_; lean_object* v___x_380_; 
lean_del_object(v___x_364_);
v_assignment_379_ = lean_ctor_get(v_a_345_, 2);
v___x_380_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(v_assignment_379_, v_fvarId_361_);
lean_dec(v_fvarId_361_);
if (lean_obj_tag(v___x_380_) == 1)
{
lean_object* v_val_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_415_; 
v_val_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_415_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_415_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_val_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_415_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
if (lean_obj_tag(v_val_381_) == 2)
{
lean_object* v_i_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v_a_391_; lean_object* v_fst_392_; 
v_i_385_ = lean_ctor_get(v_val_381_, 0);
lean_inc(v_i_385_);
lean_dec_ref_known(v_val_381_, 1);
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = lean_unsigned_to_nat(1u);
v___x_388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_367_);
lean_ctor_set(v___x_388_, 2, v___x_387_);
v___x_389_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__0));
v___x_390_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_358_, v_args_362_, v___x_374_, v___x_388_, v___x_389_, v___x_386_, v_a_346_);
lean_dec_ref_known(v___x_388_, 3);
lean_dec_ref(v_args_362_);
lean_dec_ref(v_params_358_);
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_fst_392_ = lean_ctor_get(v_a_391_, 0);
if (lean_obj_tag(v_fst_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_403_; 
v_a_393_ = lean_ctor_get(v___x_390_, 1);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v___x_390_, 0);
lean_dec(v_unused_404_);
v___x_395_ = v___x_390_;
v_isShared_396_ = v_isSharedCheck_403_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_390_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_403_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v_i_385_);
v___x_398_ = v___x_383_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_i_385_);
v___x_398_ = v_reuseFailAlloc_402_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_400_; 
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_398_);
v___x_400_ = v___x_395_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_a_393_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_413_; 
lean_inc_ref(v_fst_392_);
lean_dec(v_i_385_);
lean_del_object(v___x_383_);
v_a_405_ = lean_ctor_get(v___x_390_, 1);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; 
v_unused_414_ = lean_ctor_get(v___x_390_, 0);
lean_dec(v_unused_414_);
v___x_407_ = v___x_390_;
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_390_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v_val_409_; lean_object* v___x_411_; 
v_val_409_ = lean_ctor_get(v_fst_392_, 0);
lean_inc(v_val_409_);
lean_dec_ref_known(v_fst_392_, 1);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v_val_409_);
v___x_411_ = v___x_407_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_val_409_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_a_405_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
lean_del_object(v___x_383_);
lean_dec(v_val_381_);
lean_dec_ref(v_args_362_);
lean_dec_ref(v_params_358_);
v___y_352_ = v_a_346_;
goto v___jp_351_;
}
}
}
else
{
lean_dec(v___x_380_);
lean_dec_ref(v_args_362_);
lean_dec_ref(v_params_358_);
v___y_352_ = v_a_346_;
goto v___jp_351_;
}
}
}
else
{
lean_object* v___x_416_; lean_object* v___x_418_; 
lean_dec_ref(v_args_362_);
lean_dec(v_fvarId_361_);
lean_dec(v_fvarId_360_);
lean_dec_ref(v_k_359_);
lean_dec_ref(v_params_358_);
v___x_416_ = lean_box(0);
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 0);
lean_ctor_set(v___x_364_, 1, v_a_346_);
lean_ctor_set(v___x_364_, 0, v___x_416_);
v___x_418_ = v___x_364_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_a_346_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
else
{
lean_dec(v_value_357_);
lean_dec_ref(v_decl_356_);
lean_dec_ref_known(v_value_355_, 2);
lean_dec_ref(v_decl_344_);
v___y_348_ = v_a_346_;
goto v___jp_347_;
}
}
else
{
lean_dec_ref(v_value_355_);
lean_dec_ref(v_decl_344_);
v___y_348_ = v_a_346_;
goto v___jp_347_;
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
v___jp_351_:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_box(0);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v___y_352_);
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f___boxed(lean_object* v_decl_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(v_decl_421_, v_a_422_, v_a_423_);
lean_dec_ref(v_a_422_);
return v_res_424_;
}
}
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0(lean_object* v_params_425_, lean_object* v_args_426_, uint8_t v___x_427_, lean_object* v_range_428_, lean_object* v_b_429_, lean_object* v_i_430_, lean_object* v_hs_431_, lean_object* v_hl_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_425_, v_args_426_, v___x_427_, v_range_428_, v_b_429_, v_i_430_, v___y_434_);
return v___x_435_;
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_425_ = stack[0].m_obj;
lean_object* v_args_426_ = stack[1].m_obj;
uint8_t v___x_427_ = stack[2].m_num;
lean_object* v_range_428_ = stack[3].m_obj;
lean_object* v_b_429_ = stack[4].m_obj;
lean_object* v_i_430_ = stack[5].m_obj;
lean_object* v___y_433_ = stack[8].m_obj;
lean_object* v___y_434_ = stack[9].m_obj;
lean_object* v_res_436_;
v_res_436_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0(v_params_425_, v_args_426_, v___x_427_, v_range_428_, v_b_429_, v_i_430_, lean_box(0), lean_box(0), v___y_433_, v___y_434_);
stack->m_obj
 = v_res_436_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___boxed(lean_object* v_params_437_, lean_object* v_args_438_, lean_object* v___x_439_, lean_object* v_range_440_, lean_object* v_b_441_, lean_object* v_i_442_, lean_object* v_hs_443_, lean_object* v_hl_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
uint8_t v___x_3567__boxed_447_; lean_object* v_res_448_; 
v___x_3567__boxed_447_ = lean_unbox(v___x_439_);
v_res_448_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0(v_params_437_, v_args_438_, v___x_3567__boxed_447_, v_range_440_, v_b_441_, v_i_442_, v_hs_443_, v_hl_444_, v___y_445_, v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec_ref(v_range_440_);
lean_dec_ref(v_args_438_);
lean_dec_ref(v_params_437_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(lean_object* v_upperBound_449_, lean_object* v_args_450_, lean_object* v_a_451_, lean_object* v_b_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_a_456_; lean_object* v_a_457_; uint8_t v___x_461_; 
v___x_461_ = lean_nat_dec_lt(v_a_451_, v_upperBound_449_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; 
lean_dec(v_a_451_);
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v_b_452_);
lean_ctor_set(v___x_462_, 1, v___y_454_);
return v___x_462_;
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_463_ = lean_box(0);
v___x_464_ = lean_array_get_size(v_args_450_);
v___x_465_ = lean_nat_dec_lt(v_a_451_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v_visited_466_; lean_object* v_fixed_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_476_; 
v_visited_466_ = lean_ctor_get(v___y_454_, 0);
v_fixed_467_ = lean_ctor_get(v___y_454_, 1);
v_isSharedCheck_476_ = !lean_is_exclusive(v___y_454_);
if (v_isSharedCheck_476_ == 0)
{
v___x_469_ = v___y_454_;
v_isShared_470_ = v_isSharedCheck_476_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_fixed_467_);
lean_inc(v_visited_466_);
lean_dec(v___y_454_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_476_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_471_ = lean_box(v___x_465_);
v___x_472_ = lean_array_set(v_fixed_467_, v_a_451_, v___x_471_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 1, v___x_472_);
v___x_474_ = v___x_469_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_visited_466_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
v_a_456_ = v___x_463_;
v_a_457_ = v___x_474_;
goto v___jp_455_;
}
}
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_array_fget_borrowed(v_args_450_, v_a_451_);
v___x_478_ = l_Lean_Compiler_LCNF_FixedParams_evalArg(v___x_477_, v___y_453_, v___y_454_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v_a_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
v_a_480_ = lean_ctor_get(v___x_478_, 1);
lean_inc(v_a_480_);
lean_dec_ref_known(v___x_478_, 2);
lean_inc(v_a_451_);
v___x_481_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_481_, 0, v_a_451_);
v___x_482_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v_a_479_, v___x_481_);
lean_dec_ref_known(v___x_481_, 1);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = lean_box(1);
v___x_484_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v_a_479_, v___x_483_);
lean_dec(v_a_479_);
if (v___x_484_ == 0)
{
lean_object* v_visited_485_; lean_object* v_fixed_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_495_; 
v_visited_485_ = lean_ctor_get(v_a_480_, 0);
v_fixed_486_ = lean_ctor_get(v_a_480_, 1);
v_isSharedCheck_495_ = !lean_is_exclusive(v_a_480_);
if (v_isSharedCheck_495_ == 0)
{
v___x_488_ = v_a_480_;
v_isShared_489_ = v_isSharedCheck_495_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_fixed_486_);
lean_inc(v_visited_485_);
lean_dec(v_a_480_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_495_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_490_ = lean_box(v___x_484_);
v___x_491_ = lean_array_set(v_fixed_486_, v_a_451_, v___x_490_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v___x_491_);
v___x_493_ = v___x_488_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_visited_485_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
v_a_456_ = v___x_463_;
v_a_457_ = v___x_493_;
goto v___jp_455_;
}
}
}
else
{
v_a_456_ = v___x_463_;
v_a_457_ = v_a_480_;
goto v___jp_455_;
}
}
else
{
lean_dec(v_a_479_);
v_a_456_ = v___x_463_;
v_a_457_ = v_a_480_;
goto v___jp_455_;
}
}
else
{
lean_object* v_a_496_; lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec(v_a_451_);
v_a_496_ = lean_ctor_get(v___x_478_, 0);
v_a_497_ = lean_ctor_get(v___x_478_, 1);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_478_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_inc(v_a_496_);
lean_dec(v___x_478_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_496_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
v___jp_455_:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_unsigned_to_nat(1u);
v___x_459_ = lean_nat_add(v_a_451_, v___x_458_);
lean_dec(v_a_451_);
v_a_451_ = v___x_459_;
v_b_452_ = v_a_456_;
v___y_454_ = v_a_457_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg___boxed(lean_object* v_upperBound_505_, lean_object* v_args_506_, lean_object* v_a_507_, lean_object* v_b_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(v_upperBound_505_, v_args_506_, v_a_507_, v_b_508_, v___y_509_, v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec_ref(v_args_506_);
lean_dec(v_upperBound_505_);
return v_res_511_;
}
}
uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(lean_object* v_xs_512_, lean_object* v_ys_513_, lean_object* v_x_514_){
_start:
{
lean_object* v_zero_515_; uint8_t v_isZero_516_; 
v_zero_515_ = lean_unsigned_to_nat(0u);
v_isZero_516_ = lean_nat_dec_eq(v_x_514_, v_zero_515_);
if (v_isZero_516_ == 1)
{
lean_dec(v_x_514_);
return v_isZero_516_;
}
else
{
lean_object* v_one_517_; lean_object* v_n_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v_one_517_ = lean_unsigned_to_nat(1u);
v_n_518_ = lean_nat_sub(v_x_514_, v_one_517_);
lean_dec(v_x_514_);
v___x_519_ = lean_array_fget_borrowed(v_xs_512_, v_n_518_);
v___x_520_ = lean_array_fget_borrowed(v_ys_513_, v_n_518_);
v___x_521_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v___x_519_, v___x_520_);
if (v___x_521_ == 0)
{
lean_dec(v_n_518_);
return v___x_521_;
}
else
{
v_x_514_ = v_n_518_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_512_ = stack[0].m_obj;
lean_object* v_ys_513_ = stack[1].m_obj;
lean_object* v_x_514_ = stack[2].m_obj;
uint8_t v_res_523_;
v_res_523_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(v_xs_512_, v_ys_513_, v_x_514_);
stack->m_num = v_res_523_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_xs_524_, lean_object* v_ys_525_, lean_object* v_x_526_){
_start:
{
uint8_t v_res_527_; lean_object* v_r_528_; 
v_res_527_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(v_xs_524_, v_ys_525_, v_x_526_);
lean_dec_ref(v_ys_525_);
lean_dec_ref(v_xs_524_);
v_r_528_ = lean_box(v_res_527_);
return v_r_528_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(lean_object* v_a_529_, lean_object* v_x_530_){
_start:
{
if (lean_obj_tag(v_x_530_) == 0)
{
uint8_t v___x_531_; 
v___x_531_ = 0;
return v___x_531_;
}
else
{
lean_object* v_key_532_; lean_object* v_tail_533_; uint8_t v___y_535_; lean_object* v_fst_537_; lean_object* v_snd_538_; lean_object* v_fst_539_; lean_object* v_snd_540_; uint8_t v___x_541_; 
v_key_532_ = lean_ctor_get(v_x_530_, 0);
v_tail_533_ = lean_ctor_get(v_x_530_, 2);
v_fst_537_ = lean_ctor_get(v_key_532_, 0);
v_snd_538_ = lean_ctor_get(v_key_532_, 1);
v_fst_539_ = lean_ctor_get(v_a_529_, 0);
v_snd_540_ = lean_ctor_get(v_a_529_, 1);
v___x_541_ = lean_name_eq(v_fst_537_, v_fst_539_);
if (v___x_541_ == 0)
{
v___y_535_ = v___x_541_;
goto v___jp_534_;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_542_ = lean_array_get_size(v_snd_538_);
v___x_543_ = lean_array_get_size(v_snd_540_);
v___x_544_ = lean_nat_dec_eq(v___x_542_, v___x_543_);
if (v___x_544_ == 0)
{
v_x_530_ = v_tail_533_;
goto _start;
}
else
{
uint8_t v___x_546_; 
v___x_546_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(v_snd_538_, v_snd_540_, v___x_542_);
v___y_535_ = v___x_546_;
goto v___jp_534_;
}
}
v___jp_534_:
{
if (v___y_535_ == 0)
{
v_x_530_ = v_tail_533_;
goto _start;
}
else
{
return v___y_535_;
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_529_ = stack[0].m_obj;
lean_object* v_x_530_ = stack[1].m_obj;
uint8_t v_res_547_;
v_res_547_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_529_, v_x_530_);
stack->m_num = v_res_547_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg___boxed(lean_object* v_a_548_, lean_object* v_x_549_){
_start:
{
uint8_t v_res_550_; lean_object* v_r_551_; 
v_res_550_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_548_, v_x_549_);
lean_dec(v_x_549_);
lean_dec_ref(v_a_548_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(lean_object* v_as_552_, size_t v_i_553_, size_t v_stop_554_, uint64_t v_b_555_){
_start:
{
uint8_t v___x_556_; 
v___x_556_ = lean_usize_dec_eq(v_i_553_, v_stop_554_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; uint64_t v___x_558_; uint64_t v___x_559_; size_t v___x_560_; size_t v___x_561_; 
v___x_557_ = lean_array_uget_borrowed(v_as_552_, v_i_553_);
v___x_558_ = l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash(v___x_557_);
v___x_559_ = lean_uint64_mix_hash(v_b_555_, v___x_558_);
v___x_560_ = ((size_t)1ULL);
v___x_561_ = lean_usize_add(v_i_553_, v___x_560_);
v_i_553_ = v___x_561_;
v_b_555_ = v___x_559_;
goto _start;
}
else
{
return v_b_555_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_552_ = stack[0].m_obj;
size_t v_i_553_ = stack[1].m_num;
size_t v_stop_554_ = stack[2].m_num;
uint64_t v_b_555_ = stack[3].m_num;
uint64_t v_res_563_;
v_res_563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_as_552_, v_i_553_, v_stop_554_, v_b_555_);
stack->m_num = v_res_563_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2___boxed(lean_object* v_as_564_, lean_object* v_i_565_, lean_object* v_stop_566_, lean_object* v_b_567_){
_start:
{
size_t v_i_boxed_568_; size_t v_stop_boxed_569_; uint64_t v_b_boxed_570_; uint64_t v_res_571_; lean_object* v_r_572_; 
v_i_boxed_568_ = lean_unbox_usize(v_i_565_);
lean_dec(v_i_565_);
v_stop_boxed_569_ = lean_unbox_usize(v_stop_566_);
lean_dec(v_stop_566_);
v_b_boxed_570_ = lean_unbox_uint64(v_b_567_);
lean_dec_ref(v_b_567_);
v_res_571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_as_564_, v_i_boxed_568_, v_stop_boxed_569_, v_b_boxed_570_);
lean_dec_ref(v_as_564_);
v_r_572_ = lean_box_uint64(v_res_571_);
return v_r_572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
if (lean_obj_tag(v_x_574_) == 0)
{
return v_x_573_;
}
else
{
lean_object* v_key_575_; lean_object* v_value_576_; lean_object* v_tail_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_616_; 
v_key_575_ = lean_ctor_get(v_x_574_, 0);
v_value_576_ = lean_ctor_get(v_x_574_, 1);
v_tail_577_ = lean_ctor_get(v_x_574_, 2);
v_isSharedCheck_616_ = !lean_is_exclusive(v_x_574_);
if (v_isSharedCheck_616_ == 0)
{
v___x_579_ = v_x_574_;
v_isShared_580_ = v_isSharedCheck_616_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_tail_577_);
lean_inc(v_value_576_);
lean_inc(v_key_575_);
lean_dec(v_x_574_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_616_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v_fst_581_; lean_object* v_snd_582_; lean_object* v___x_583_; uint64_t v___y_585_; uint64_t v___y_586_; uint64_t v___y_606_; 
v_fst_581_ = lean_ctor_get(v_key_575_, 0);
v_snd_582_ = lean_ctor_get(v_key_575_, 1);
v___x_583_ = lean_array_get_size(v_x_573_);
if (lean_obj_tag(v_fst_581_) == 0)
{
uint64_t v___x_614_; 
v___x_614_ = 1723ULL;
v___y_606_ = v___x_614_;
goto v___jp_605_;
}
else
{
uint64_t v_hash_615_; 
v_hash_615_ = lean_ctor_get_uint64(v_fst_581_, sizeof(void*)*2);
v___y_606_ = v_hash_615_;
goto v___jp_605_;
}
v___jp_584_:
{
uint64_t v___x_587_; uint64_t v___x_588_; uint64_t v___x_589_; uint64_t v_fold_590_; uint64_t v___x_591_; uint64_t v___x_592_; uint64_t v___x_593_; size_t v___x_594_; size_t v___x_595_; size_t v___x_596_; size_t v___x_597_; size_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_587_ = lean_uint64_mix_hash(v___y_585_, v___y_586_);
v___x_588_ = 32ULL;
v___x_589_ = lean_uint64_shift_right(v___x_587_, v___x_588_);
v_fold_590_ = lean_uint64_xor(v___x_587_, v___x_589_);
v___x_591_ = 16ULL;
v___x_592_ = lean_uint64_shift_right(v_fold_590_, v___x_591_);
v___x_593_ = lean_uint64_xor(v_fold_590_, v___x_592_);
v___x_594_ = lean_uint64_to_usize(v___x_593_);
v___x_595_ = lean_usize_of_nat(v___x_583_);
v___x_596_ = ((size_t)1ULL);
v___x_597_ = lean_usize_sub(v___x_595_, v___x_596_);
v___x_598_ = lean_usize_land(v___x_594_, v___x_597_);
v___x_599_ = lean_array_uget_borrowed(v_x_573_, v___x_598_);
lean_inc(v___x_599_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 2, v___x_599_);
v___x_601_ = v___x_579_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_key_575_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_value_576_);
lean_ctor_set(v_reuseFailAlloc_604_, 2, v___x_599_);
v___x_601_ = v_reuseFailAlloc_604_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; 
v___x_602_ = lean_array_uset(v_x_573_, v___x_598_, v___x_601_);
v_x_573_ = v___x_602_;
v_x_574_ = v_tail_577_;
goto _start;
}
}
v___jp_605_:
{
uint64_t v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_607_ = 7ULL;
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = lean_array_get_size(v_snd_582_);
v___x_610_ = lean_nat_dec_lt(v___x_608_, v___x_609_);
if (v___x_610_ == 0)
{
v___y_585_ = v___y_606_;
v___y_586_ = v___x_607_;
goto v___jp_584_;
}
else
{
size_t v___x_611_; size_t v___x_612_; uint64_t v___x_613_; 
v___x_611_ = ((size_t)0ULL);
v___x_612_ = lean_usize_of_nat(v___x_609_);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_582_, v___x_611_, v___x_612_, v___x_607_);
v___y_585_ = v___y_606_;
v___y_586_ = v___x_613_;
goto v___jp_584_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(lean_object* v_i_617_, lean_object* v_source_618_, lean_object* v_target_619_){
_start:
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = lean_array_get_size(v_source_618_);
v___x_621_ = lean_nat_dec_lt(v_i_617_, v___x_620_);
if (v___x_621_ == 0)
{
lean_dec_ref(v_source_618_);
lean_dec(v_i_617_);
return v_target_619_;
}
else
{
lean_object* v_es_622_; lean_object* v___x_623_; lean_object* v_source_624_; lean_object* v_target_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_es_622_ = lean_array_fget(v_source_618_, v_i_617_);
v___x_623_ = lean_box(0);
v_source_624_ = lean_array_fset(v_source_618_, v_i_617_, v___x_623_);
v_target_625_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(v_target_619_, v_es_622_);
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_nat_add(v_i_617_, v___x_626_);
lean_dec(v_i_617_);
v_i_617_ = v___x_627_;
v_source_618_ = v_source_624_;
v_target_619_ = v_target_625_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(lean_object* v_data_629_){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v_nbuckets_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_630_ = lean_array_get_size(v_data_629_);
v___x_631_ = lean_unsigned_to_nat(2u);
v_nbuckets_632_ = lean_nat_mul(v___x_630_, v___x_631_);
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_box(0);
v___x_635_ = lean_mk_array(v_nbuckets_632_, v___x_634_);
v___x_636_ = lean_array_propagate_mark(v_data_629_, v___x_635_);
v___x_637_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(v___x_633_, v_data_629_, v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(lean_object* v_m_638_, lean_object* v_a_639_, lean_object* v_b_640_){
_start:
{
lean_object* v_size_641_; lean_object* v_buckets_642_; lean_object* v_fst_643_; lean_object* v_snd_644_; lean_object* v___x_645_; uint64_t v___y_647_; uint64_t v___y_648_; uint64_t v___y_687_; 
v_size_641_ = lean_ctor_get(v_m_638_, 0);
v_buckets_642_ = lean_ctor_get(v_m_638_, 1);
v_fst_643_ = lean_ctor_get(v_a_639_, 0);
v_snd_644_ = lean_ctor_get(v_a_639_, 1);
v___x_645_ = lean_array_get_size(v_buckets_642_);
if (lean_obj_tag(v_fst_643_) == 0)
{
uint64_t v___x_695_; 
v___x_695_ = 1723ULL;
v___y_687_ = v___x_695_;
goto v___jp_686_;
}
else
{
uint64_t v_hash_696_; 
v_hash_696_ = lean_ctor_get_uint64(v_fst_643_, sizeof(void*)*2);
v___y_687_ = v_hash_696_;
goto v___jp_686_;
}
v___jp_646_:
{
uint64_t v___x_649_; uint64_t v___x_650_; uint64_t v___x_651_; uint64_t v_fold_652_; uint64_t v___x_653_; uint64_t v___x_654_; uint64_t v___x_655_; size_t v___x_656_; size_t v___x_657_; size_t v___x_658_; size_t v___x_659_; size_t v___x_660_; lean_object* v_bkt_661_; uint8_t v___x_662_; 
v___x_649_ = lean_uint64_mix_hash(v___y_647_, v___y_648_);
v___x_650_ = 32ULL;
v___x_651_ = lean_uint64_shift_right(v___x_649_, v___x_650_);
v_fold_652_ = lean_uint64_xor(v___x_649_, v___x_651_);
v___x_653_ = 16ULL;
v___x_654_ = lean_uint64_shift_right(v_fold_652_, v___x_653_);
v___x_655_ = lean_uint64_xor(v_fold_652_, v___x_654_);
v___x_656_ = lean_uint64_to_usize(v___x_655_);
v___x_657_ = lean_usize_of_nat(v___x_645_);
v___x_658_ = ((size_t)1ULL);
v___x_659_ = lean_usize_sub(v___x_657_, v___x_658_);
v___x_660_ = lean_usize_land(v___x_656_, v___x_659_);
v_bkt_661_ = lean_array_uget_borrowed(v_buckets_642_, v___x_660_);
v___x_662_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_639_, v_bkt_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_683_; 
lean_inc_ref(v_buckets_642_);
lean_inc(v_size_641_);
v_isSharedCheck_683_ = !lean_is_exclusive(v_m_638_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; lean_object* v_unused_685_; 
v_unused_684_ = lean_ctor_get(v_m_638_, 1);
lean_dec(v_unused_684_);
v_unused_685_ = lean_ctor_get(v_m_638_, 0);
lean_dec(v_unused_685_);
v___x_664_ = v_m_638_;
v_isShared_665_ = v_isSharedCheck_683_;
goto v_resetjp_663_;
}
else
{
lean_dec(v_m_638_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_683_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v_size_x27_667_; lean_object* v___x_668_; lean_object* v_buckets_x27_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_666_ = lean_unsigned_to_nat(1u);
v_size_x27_667_ = lean_nat_add(v_size_641_, v___x_666_);
lean_dec(v_size_641_);
lean_inc(v_bkt_661_);
v___x_668_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_668_, 0, v_a_639_);
lean_ctor_set(v___x_668_, 1, v_b_640_);
lean_ctor_set(v___x_668_, 2, v_bkt_661_);
v_buckets_x27_669_ = lean_array_uset(v_buckets_642_, v___x_660_, v___x_668_);
v___x_670_ = lean_unsigned_to_nat(4u);
v___x_671_ = lean_nat_mul(v_size_x27_667_, v___x_670_);
v___x_672_ = lean_unsigned_to_nat(3u);
v___x_673_ = lean_nat_div(v___x_671_, v___x_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_array_get_size(v_buckets_x27_669_);
v___x_675_ = lean_nat_dec_le(v___x_673_, v___x_674_);
lean_dec(v___x_673_);
if (v___x_675_ == 0)
{
lean_object* v_val_676_; lean_object* v___x_678_; 
v_val_676_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(v_buckets_x27_669_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 1, v_val_676_);
lean_ctor_set(v___x_664_, 0, v_size_x27_667_);
v___x_678_ = v___x_664_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_size_x27_667_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_val_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
else
{
lean_object* v___x_681_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 1, v_buckets_x27_669_);
lean_ctor_set(v___x_664_, 0, v_size_x27_667_);
v___x_681_ = v___x_664_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_size_x27_667_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_buckets_x27_669_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
else
{
lean_dec(v_b_640_);
lean_dec_ref(v_a_639_);
return v_m_638_;
}
}
v___jp_686_:
{
uint64_t v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_688_ = 7ULL;
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = lean_array_get_size(v_snd_644_);
v___x_691_ = lean_nat_dec_lt(v___x_689_, v___x_690_);
if (v___x_691_ == 0)
{
v___y_647_ = v___y_687_;
v___y_648_ = v___x_688_;
goto v___jp_646_;
}
else
{
size_t v___x_692_; size_t v___x_693_; uint64_t v___x_694_; 
v___x_692_ = ((size_t)0ULL);
v___x_693_ = lean_usize_of_nat(v___x_690_);
v___x_694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_644_, v___x_692_, v___x_693_, v___x_688_);
v___y_647_ = v___y_687_;
v___y_648_ = v___x_694_;
goto v___jp_646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(lean_object* v_f_697_, lean_object* v_v_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
if (lean_obj_tag(v_v_698_) == 0)
{
lean_object* v_code_701_; lean_object* v___x_702_; 
v_code_701_ = lean_ctor_get(v_v_698_, 0);
lean_inc_ref(v_code_701_);
lean_dec_ref_known(v_v_698_, 1);
lean_inc_ref(v___y_699_);
v___x_702_ = lean_apply_3(v_f_697_, v_code_701_, v___y_699_, v___y_700_);
return v___x_702_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec_ref_known(v_v_698_, 1);
lean_dec_ref(v_f_697_);
v___x_703_ = lean_box(0);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v___y_700_);
return v___x_704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg___boxed(lean_object* v_f_705_, lean_object* v_v_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v_f_705_, v_v_706_, v___y_707_, v___y_708_);
lean_dec_ref(v___y_707_);
return v_res_709_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(lean_object* v_m_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_buckets_712_; lean_object* v_fst_713_; lean_object* v_snd_714_; lean_object* v___x_715_; uint64_t v___y_717_; uint64_t v___y_718_; uint64_t v___y_734_; 
v_buckets_712_ = lean_ctor_get(v_m_710_, 1);
v_fst_713_ = lean_ctor_get(v_a_711_, 0);
v_snd_714_ = lean_ctor_get(v_a_711_, 1);
v___x_715_ = lean_array_get_size(v_buckets_712_);
if (lean_obj_tag(v_fst_713_) == 0)
{
uint64_t v___x_742_; 
v___x_742_ = 1723ULL;
v___y_734_ = v___x_742_;
goto v___jp_733_;
}
else
{
uint64_t v_hash_743_; 
v_hash_743_ = lean_ctor_get_uint64(v_fst_713_, sizeof(void*)*2);
v___y_734_ = v_hash_743_;
goto v___jp_733_;
}
v___jp_716_:
{
uint64_t v___x_719_; uint64_t v___x_720_; uint64_t v___x_721_; uint64_t v_fold_722_; uint64_t v___x_723_; uint64_t v___x_724_; uint64_t v___x_725_; size_t v___x_726_; size_t v___x_727_; size_t v___x_728_; size_t v___x_729_; size_t v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_719_ = lean_uint64_mix_hash(v___y_717_, v___y_718_);
v___x_720_ = 32ULL;
v___x_721_ = lean_uint64_shift_right(v___x_719_, v___x_720_);
v_fold_722_ = lean_uint64_xor(v___x_719_, v___x_721_);
v___x_723_ = 16ULL;
v___x_724_ = lean_uint64_shift_right(v_fold_722_, v___x_723_);
v___x_725_ = lean_uint64_xor(v_fold_722_, v___x_724_);
v___x_726_ = lean_uint64_to_usize(v___x_725_);
v___x_727_ = lean_usize_of_nat(v___x_715_);
v___x_728_ = ((size_t)1ULL);
v___x_729_ = lean_usize_sub(v___x_727_, v___x_728_);
v___x_730_ = lean_usize_land(v___x_726_, v___x_729_);
v___x_731_ = lean_array_uget_borrowed(v_buckets_712_, v___x_730_);
v___x_732_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_711_, v___x_731_);
return v___x_732_;
}
v___jp_733_:
{
uint64_t v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_735_ = 7ULL;
v___x_736_ = lean_unsigned_to_nat(0u);
v___x_737_ = lean_array_get_size(v_snd_714_);
v___x_738_ = lean_nat_dec_lt(v___x_736_, v___x_737_);
if (v___x_738_ == 0)
{
v___y_717_ = v___y_734_;
v___y_718_ = v___x_735_;
goto v___jp_716_;
}
else
{
size_t v___x_739_; size_t v___x_740_; uint64_t v___x_741_; 
v___x_739_ = ((size_t)0ULL);
v___x_740_ = lean_usize_of_nat(v___x_737_);
v___x_741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_714_, v___x_739_, v___x_740_, v___x_735_);
v___y_717_ = v___y_734_;
v___y_718_ = v___x_741_;
goto v___jp_716_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_710_ = stack[0].m_obj;
lean_object* v_a_711_ = stack[1].m_obj;
uint8_t v_res_744_;
v_res_744_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_m_710_, v_a_711_);
stack->m_num = v_res_744_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg___boxed(lean_object* v_m_745_, lean_object* v_a_746_){
_start:
{
uint8_t v_res_747_; lean_object* v_r_748_; 
v_res_747_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_m_745_, v_a_746_);
lean_dec_ref(v_a_746_);
lean_dec_ref(v_m_745_);
v_r_748_ = lean_box(v_res_747_);
return v_r_748_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(lean_object* v_upperBound_749_, lean_object* v_args_750_, lean_object* v_a_751_, lean_object* v_b_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_a_756_; lean_object* v_a_757_; uint8_t v___x_761_; 
v___x_761_ = lean_nat_dec_lt(v_a_751_, v_upperBound_749_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; 
lean_dec(v_a_751_);
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v_b_752_);
lean_ctor_set(v___x_762_, 1, v___y_754_);
return v___x_762_;
}
else
{
lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_763_ = lean_array_get_size(v_args_750_);
v___x_764_ = lean_nat_dec_lt(v_a_751_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = lean_box(0);
v___x_766_ = lean_array_push(v_b_752_, v___x_765_);
v_a_756_ = v___x_766_;
v_a_757_ = v___y_754_;
goto v___jp_755_;
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_array_fget_borrowed(v_args_750_, v_a_751_);
v___x_768_ = l_Lean_Compiler_LCNF_FixedParams_evalArg(v___x_767_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v_a_770_; lean_object* v___x_771_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
v_a_770_ = lean_ctor_get(v___x_768_, 1);
lean_inc(v_a_770_);
lean_dec_ref_known(v___x_768_, 2);
v___x_771_ = lean_array_push(v_b_752_, v_a_769_);
v_a_756_ = v___x_771_;
v_a_757_ = v_a_770_;
goto v___jp_755_;
}
else
{
lean_object* v_a_772_; lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec_ref(v_b_752_);
lean_dec(v_a_751_);
v_a_772_ = lean_ctor_get(v___x_768_, 0);
v_a_773_ = lean_ctor_get(v___x_768_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_768_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_inc(v_a_772_);
lean_dec(v___x_768_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_772_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
v___jp_755_:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_unsigned_to_nat(1u);
v___x_759_ = lean_nat_add(v_a_751_, v___x_758_);
lean_dec(v_a_751_);
v_a_751_ = v___x_759_;
v_b_752_ = v_a_756_;
v___y_754_ = v_a_757_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg___boxed(lean_object* v_upperBound_781_, lean_object* v_args_782_, lean_object* v_a_783_, lean_object* v_b_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v_upperBound_781_, v_args_782_, v_a_783_, v_b_784_, v___y_785_, v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec_ref(v_args_782_);
lean_dec(v_upperBound_781_);
return v_res_787_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(uint8_t v_a_788_, uint8_t v___x_789_, lean_object* v_as_790_, size_t v_i_791_, size_t v_stop_792_){
_start:
{
uint8_t v___x_793_; 
v___x_793_ = lean_usize_dec_eq(v_i_791_, v_stop_792_);
if (v___x_793_ == 0)
{
uint8_t v___x_794_; uint8_t v___y_796_; lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_794_ = 1;
v___x_800_ = lean_array_uget_borrowed(v_as_790_, v_i_791_);
v___x_801_ = lean_unbox(v___x_800_);
if (v___x_801_ == 0)
{
if (v_a_788_ == 0)
{
v___y_796_ = v___x_789_;
goto v___jp_795_;
}
else
{
uint8_t v___x_802_; 
v___x_802_ = lean_unbox(v___x_800_);
v___y_796_ = v___x_802_;
goto v___jp_795_;
}
}
else
{
v___y_796_ = v_a_788_;
goto v___jp_795_;
}
v___jp_795_:
{
if (v___y_796_ == 0)
{
size_t v___x_797_; size_t v___x_798_; 
v___x_797_ = ((size_t)1ULL);
v___x_798_ = lean_usize_add(v_i_791_, v___x_797_);
v_i_791_ = v___x_798_;
goto _start;
}
else
{
return v___x_794_;
}
}
}
else
{
uint8_t v___x_803_; 
v___x_803_ = 0;
return v___x_803_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_788_ = stack[0].m_num;
uint8_t v___x_789_ = stack[1].m_num;
lean_object* v_as_790_ = stack[2].m_obj;
size_t v_i_791_ = stack[3].m_num;
size_t v_stop_792_ = stack[4].m_num;
uint8_t v_res_804_;
v_res_804_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(v_a_788_, v___x_789_, v_as_790_, v_i_791_, v_stop_792_);
stack->m_num = v_res_804_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9___boxed(lean_object* v_a_805_, lean_object* v___x_806_, lean_object* v_as_807_, lean_object* v_i_808_, lean_object* v_stop_809_){
_start:
{
uint8_t v_a_boxed_810_; uint8_t v___x_13526__boxed_811_; size_t v_i_boxed_812_; size_t v_stop_boxed_813_; uint8_t v_res_814_; lean_object* v_r_815_; 
v_a_boxed_810_ = lean_unbox(v_a_805_);
v___x_13526__boxed_811_ = lean_unbox(v___x_806_);
v_i_boxed_812_ = lean_unbox_usize(v_i_808_);
lean_dec(v_i_808_);
v_stop_boxed_813_ = lean_unbox_usize(v_stop_809_);
lean_dec(v_stop_809_);
v_res_814_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(v_a_boxed_810_, v___x_13526__boxed_811_, v_as_807_, v_i_boxed_812_, v_stop_boxed_813_);
lean_dec_ref(v_as_807_);
v_r_815_ = lean_box(v_res_814_);
return v_r_815_;
}
}
uint8_t l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(uint8_t v___x_816_, lean_object* v_as_817_, uint8_t v_a_818_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_819_ = lean_unsigned_to_nat(0u);
v___x_820_ = lean_array_get_size(v_as_817_);
v___x_821_ = lean_nat_dec_lt(v___x_819_, v___x_820_);
if (v___x_821_ == 0)
{
return v___x_821_;
}
else
{
if (v___x_821_ == 0)
{
return v___x_821_;
}
else
{
size_t v___x_822_; size_t v___x_823_; uint8_t v___x_824_; 
v___x_822_ = ((size_t)0ULL);
v___x_823_ = lean_usize_of_nat(v___x_820_);
v___x_824_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(v_a_818_, v___x_816_, v_as_817_, v___x_822_, v___x_823_);
return v___x_824_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_816_ = stack[0].m_num;
lean_object* v_as_817_ = stack[1].m_obj;
uint8_t v_a_818_ = stack[2].m_num;
uint8_t v_res_825_;
v_res_825_ = l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(v___x_816_, v_as_817_, v_a_818_);
stack->m_num = v_res_825_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___boxed(lean_object* v___x_826_, lean_object* v_as_827_, lean_object* v_a_828_){
_start:
{
uint8_t v___x_13564__boxed_829_; uint8_t v_a_boxed_830_; uint8_t v_res_831_; lean_object* v_r_832_; 
v___x_13564__boxed_829_ = lean_unbox(v___x_826_);
v_a_boxed_830_ = lean_unbox(v_a_828_);
v_res_831_ = l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(v___x_13564__boxed_829_, v_as_827_, v_a_boxed_830_);
lean_dec_ref(v_as_827_);
v_r_832_ = lean_box(v_res_831_);
return v_r_832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0___boxed(lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_c_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0(v_a_835_, v_a_836_, v_c_837_, v___y_838_, v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec_ref(v_a_835_);
return v_res_840_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(lean_object* v_declName_841_, lean_object* v_args_842_, lean_object* v_as_843_, size_t v_sz_844_, size_t v_i_845_, lean_object* v_b_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_a_850_; lean_object* v_a_851_; uint8_t v___x_855_; 
v___x_855_ = lean_usize_dec_lt(v_i_845_, v_sz_844_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; 
lean_dec(v_declName_841_);
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v_b_846_);
lean_ctor_set(v___x_856_, 1, v___y_848_);
return v___x_856_;
}
else
{
lean_object* v_a_857_; lean_object* v_toSignature_858_; lean_object* v_value_859_; lean_object* v_name_860_; lean_object* v_params_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v_a_857_ = lean_array_uget_borrowed(v_as_843_, v_i_845_);
v_toSignature_858_ = lean_ctor_get(v_a_857_, 0);
v_value_859_ = lean_ctor_get(v_a_857_, 1);
v_name_860_ = lean_ctor_get(v_toSignature_858_, 0);
v_params_861_ = lean_ctor_get(v_toSignature_858_, 3);
v___x_862_ = lean_box(0);
v___x_863_ = lean_name_eq(v_declName_841_, v_name_860_);
if (v___x_863_ == 0)
{
v_a_850_ = v___x_862_;
v_a_851_ = v___y_848_;
goto v___jp_849_;
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_864_ = lean_array_get_size(v_params_861_);
v___x_865_ = lean_unsigned_to_nat(0u);
v___x_866_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0));
v___x_867_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v___x_864_, v_args_842_, v___x_865_, v___x_866_, v___y_847_, v___y_848_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v_a_869_; lean_object* v_visited_870_; lean_object* v_fixed_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v_a_868_ = lean_ctor_get(v___x_867_, 1);
lean_inc(v_a_868_);
v_a_869_ = lean_ctor_get(v___x_867_, 0);
lean_inc_n(v_a_869_, 2);
lean_dec_ref_known(v___x_867_, 2);
v_visited_870_ = lean_ctor_get(v_a_868_, 0);
v_fixed_871_ = lean_ctor_get(v_a_868_, 1);
lean_inc(v_declName_841_);
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v_declName_841_);
lean_ctor_set(v___x_872_, 1, v_a_869_);
v___x_873_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_visited_870_, v___x_872_);
if (v___x_873_ == 0)
{
lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_884_; 
lean_inc_ref(v_fixed_871_);
lean_inc_ref(v_visited_870_);
v_isSharedCheck_884_ = !lean_is_exclusive(v_a_868_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; lean_object* v_unused_886_; 
v_unused_885_ = lean_ctor_get(v_a_868_, 1);
lean_dec(v_unused_885_);
v_unused_886_ = lean_ctor_get(v_a_868_, 0);
lean_dec(v_unused_886_);
v___x_875_ = v_a_868_;
v_isShared_876_ = v_isSharedCheck_884_;
goto v_resetjp_874_;
}
else
{
lean_dec(v_a_868_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_884_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___f_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
lean_inc(v_a_857_);
v___f_877_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0___boxed), 5, 2);
lean_closure_set(v___f_877_, 0, v_a_857_);
lean_closure_set(v___f_877_, 1, v_a_869_);
v___x_878_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(v_visited_870_, v___x_872_, v___x_862_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_878_);
v___x_880_ = v___x_875_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_fixed_871_);
v___x_880_ = v_reuseFailAlloc_883_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; 
lean_inc_ref(v_value_859_);
v___x_881_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v___f_877_, v_value_859_, v___y_847_, v___x_880_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; 
v_a_882_ = lean_ctor_get(v___x_881_, 1);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 2);
v_a_850_ = v___x_862_;
v_a_851_ = v_a_882_;
goto v___jp_849_;
}
else
{
lean_dec(v_declName_841_);
return v___x_881_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_872_, 2);
lean_dec(v_a_869_);
v_a_850_ = v___x_862_;
v_a_851_ = v_a_868_;
goto v___jp_849_;
}
}
else
{
lean_object* v_a_887_; lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec(v_declName_841_);
v_a_887_ = lean_ctor_get(v___x_867_, 0);
v_a_888_ = lean_ctor_get(v___x_867_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_867_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_inc(v_a_887_);
lean_dec(v___x_867_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_887_);
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
}
}
v___jp_849_:
{
size_t v___x_852_; size_t v___x_853_; 
v___x_852_ = ((size_t)1ULL);
v___x_853_ = lean_usize_add(v_i_845_, v___x_852_);
v_i_845_ = v___x_853_;
v_b_846_ = v_a_850_;
v___y_848_ = v_a_851_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_841_ = stack[0].m_obj;
lean_object* v_args_842_ = stack[1].m_obj;
lean_object* v_as_843_ = stack[2].m_obj;
size_t v_sz_844_ = stack[3].m_num;
size_t v_i_845_ = stack[4].m_num;
lean_object* v_b_846_ = stack[5].m_obj;
lean_object* v___y_847_ = stack[6].m_obj;
lean_object* v___y_848_ = stack[7].m_obj;
lean_object* v_res_896_;
v_res_896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(v_declName_841_, v_args_842_, v_as_843_, v_sz_844_, v_i_845_, v_b_846_, v___y_847_, v___y_848_);
stack->m_obj
 = v_res_896_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp(lean_object* v_declName_897_, lean_object* v_args_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___y_902_; lean_object* v_decls_903_; lean_object* v___y_904_; lean_object* v_main_918_; lean_object* v_toSignature_919_; lean_object* v_decls_920_; lean_object* v_name_921_; lean_object* v_params_922_; uint8_t v___x_923_; 
v_main_918_ = lean_ctor_get(v_a_899_, 1);
v_toSignature_919_ = lean_ctor_get(v_main_918_, 0);
v_decls_920_ = lean_ctor_get(v_a_899_, 0);
v_name_921_ = lean_ctor_get(v_toSignature_919_, 0);
v_params_922_ = lean_ctor_get(v_toSignature_919_, 3);
v___x_923_ = lean_name_eq(v_declName_897_, v_name_921_);
if (v___x_923_ == 0)
{
v___y_902_ = v_a_899_;
v_decls_903_ = v_decls_920_;
v___y_904_ = v_a_900_;
goto v___jp_901_;
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_924_ = lean_array_get_size(v_params_922_);
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = lean_box(0);
v___x_927_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(v___x_924_, v_args_898_, v___x_925_, v___x_926_, v_a_899_, v_a_900_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_937_; 
v_a_928_ = lean_ctor_get(v___x_927_, 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v___x_927_, 0);
lean_dec(v_unused_938_);
v___x_930_ = v___x_927_;
v_isShared_931_ = v_isSharedCheck_937_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_937_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v_fixed_932_; uint8_t v___x_933_; 
v_fixed_932_ = lean_ctor_get(v_a_928_, 1);
v___x_933_ = l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(v___x_923_, v_fixed_932_, v___x_923_);
if (v___x_933_ == 0)
{
lean_object* v___x_935_; 
lean_dec(v_declName_897_);
if (v_isShared_931_ == 0)
{
lean_ctor_set_tag(v___x_930_, 1);
lean_ctor_set(v___x_930_, 0, v___x_926_);
v___x_935_ = v___x_930_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_a_928_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
else
{
lean_del_object(v___x_930_);
v___y_902_ = v_a_899_;
v_decls_903_ = v_decls_920_;
v___y_904_ = v_a_928_;
goto v___jp_901_;
}
}
}
else
{
lean_dec(v_declName_897_);
return v___x_927_;
}
}
v___jp_901_:
{
lean_object* v___x_905_; size_t v_sz_906_; size_t v___x_907_; lean_object* v___x_908_; 
v___x_905_ = lean_box(0);
v_sz_906_ = lean_array_size(v_decls_903_);
v___x_907_ = ((size_t)0ULL);
v___x_908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(v_declName_897_, v_args_898_, v_decls_903_, v_sz_906_, v___x_907_, v___x_905_, v___y_902_, v___y_904_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
v_a_909_ = lean_ctor_get(v___x_908_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; 
v_unused_917_ = lean_ctor_get(v___x_908_, 0);
lean_dec(v_unused_917_);
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_905_);
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
else
{
return v___x_908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalLetValue(lean_object* v_e_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
if (lean_obj_tag(v_e_939_) == 3)
{
lean_object* v_declName_942_; lean_object* v_args_943_; lean_object* v___x_944_; 
v_declName_942_ = lean_ctor_get(v_e_939_, 0);
lean_inc(v_declName_942_);
v_args_943_ = lean_ctor_get(v_e_939_, 2);
lean_inc_ref(v_args_943_);
lean_dec_ref_known(v_e_939_, 3);
v___x_944_ = l_Lean_Compiler_LCNF_FixedParams_evalApp(v_declName_942_, v_args_943_, v_a_940_, v_a_941_);
lean_dec_ref(v_args_943_);
return v___x_944_;
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; 
lean_dec(v_e_939_);
v___x_945_ = lean_box(0);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v_a_941_);
return v___x_946_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(lean_object* v_as_947_, size_t v_i_948_, size_t v_stop_949_, lean_object* v_b_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___y_954_; uint8_t v___x_961_; 
v___x_961_ = lean_usize_dec_eq(v_i_948_, v_stop_949_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
v___x_962_ = lean_array_uget_borrowed(v_as_947_, v_i_948_);
switch(lean_obj_tag(v___x_962_))
{
case 0:
{
lean_object* v_code_963_; 
v_code_963_ = lean_ctor_get(v___x_962_, 2);
lean_inc_ref(v_code_963_);
v___y_954_ = v_code_963_;
goto v___jp_953_;
}
case 1:
{
lean_object* v_code_964_; 
v_code_964_ = lean_ctor_get(v___x_962_, 1);
lean_inc_ref(v_code_964_);
v___y_954_ = v_code_964_;
goto v___jp_953_;
}
default: 
{
lean_object* v_code_965_; 
v_code_965_ = lean_ctor_get(v___x_962_, 0);
lean_inc_ref(v_code_965_);
v___y_954_ = v_code_965_;
goto v___jp_953_;
}
}
}
else
{
lean_object* v___x_966_; 
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v_b_950_);
lean_ctor_set(v___x_966_, 1, v___y_952_);
return v___x_966_;
}
v___jp_953_:
{
lean_object* v___x_955_; 
lean_inc_ref(v___y_951_);
v___x_955_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v___y_954_, v___y_951_, v___y_952_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v_a_957_; size_t v___x_958_; size_t v___x_959_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
v_a_957_ = lean_ctor_get(v___x_955_, 1);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_955_, 2);
v___x_958_ = ((size_t)1ULL);
v___x_959_ = lean_usize_add(v_i_948_, v___x_958_);
v_i_948_ = v___x_959_;
v_b_950_ = v_a_956_;
v___y_952_ = v_a_957_;
goto _start;
}
else
{
return v___x_955_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_947_ = stack[0].m_obj;
size_t v_i_948_ = stack[1].m_num;
size_t v_stop_949_ = stack[2].m_num;
lean_object* v_b_950_ = stack[3].m_obj;
lean_object* v___y_951_ = stack[4].m_obj;
lean_object* v___y_952_ = stack[5].m_obj;
lean_object* v_res_967_;
v_res_967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(v_as_947_, v_i_948_, v_stop_949_, v_b_950_, v___y_951_, v___y_952_);
stack->m_obj
 = v_res_967_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalCode(lean_object* v_code_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
switch(lean_obj_tag(v_code_968_))
{
case 0:
{
lean_object* v_decl_971_; lean_object* v_k_972_; lean_object* v_value_973_; lean_object* v___x_974_; 
v_decl_971_ = lean_ctor_get(v_code_968_, 0);
lean_inc_ref(v_decl_971_);
v_k_972_ = lean_ctor_get(v_code_968_, 1);
lean_inc_ref(v_k_972_);
lean_dec_ref_known(v_code_968_, 2);
v_value_973_ = lean_ctor_get(v_decl_971_, 3);
lean_inc(v_value_973_);
lean_dec_ref(v_decl_971_);
v___x_974_ = l_Lean_Compiler_LCNF_FixedParams_evalLetValue(v_value_973_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; 
v_a_975_ = lean_ctor_get(v___x_974_, 1);
lean_inc(v_a_975_);
lean_dec_ref_known(v___x_974_, 2);
v_code_968_ = v_k_972_;
v_a_970_ = v_a_975_;
goto _start;
}
else
{
lean_dec_ref(v_k_972_);
lean_dec_ref(v_a_969_);
return v___x_974_;
}
}
case 1:
{
lean_object* v_decl_977_; lean_object* v_k_978_; lean_object* v___x_979_; 
v_decl_977_ = lean_ctor_get(v_code_968_, 0);
lean_inc_ref_n(v_decl_977_, 2);
v_k_978_ = lean_ctor_get(v_code_968_, 1);
lean_inc_ref(v_k_978_);
lean_dec_ref_known(v_code_968_, 2);
v___x_979_ = l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(v_decl_977_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
if (lean_obj_tag(v_a_980_) == 1)
{
lean_object* v_a_981_; lean_object* v_val_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_996_; 
v_a_981_ = lean_ctor_get(v___x_979_, 1);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_979_, 2);
v_val_982_ = lean_ctor_get(v_a_980_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v_a_980_);
if (v_isSharedCheck_996_ == 0)
{
v___x_984_ = v_a_980_;
v_isShared_985_ = v_isSharedCheck_996_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_val_982_);
lean_dec(v_a_980_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_996_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v_fvarId_986_; lean_object* v_decls_987_; lean_object* v_main_988_; lean_object* v_assignment_989_; lean_object* v___x_991_; 
v_fvarId_986_ = lean_ctor_get(v_decl_977_, 0);
lean_inc(v_fvarId_986_);
lean_dec_ref(v_decl_977_);
v_decls_987_ = lean_ctor_get(v_a_969_, 0);
lean_inc_ref(v_decls_987_);
v_main_988_ = lean_ctor_get(v_a_969_, 1);
lean_inc_ref(v_main_988_);
v_assignment_989_ = lean_ctor_get(v_a_969_, 2);
lean_inc(v_assignment_989_);
lean_dec_ref(v_a_969_);
if (v_isShared_985_ == 0)
{
lean_ctor_set_tag(v___x_984_, 2);
v___x_991_ = v___x_984_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_val_982_);
v___x_991_ = v_reuseFailAlloc_995_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_986_, v___x_991_, v_assignment_989_);
v___x_993_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_993_, 0, v_decls_987_);
lean_ctor_set(v___x_993_, 1, v_main_988_);
lean_ctor_set(v___x_993_, 2, v___x_992_);
v_code_968_ = v_k_978_;
v_a_969_ = v___x_993_;
v_a_970_ = v_a_981_;
goto _start;
}
}
}
else
{
lean_object* v_a_997_; lean_object* v_value_998_; lean_object* v___x_999_; 
lean_dec(v_a_980_);
v_a_997_ = lean_ctor_get(v___x_979_, 1);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_979_, 2);
v_value_998_ = lean_ctor_get(v_decl_977_, 4);
lean_inc_ref(v_value_998_);
lean_dec_ref(v_decl_977_);
lean_inc_ref(v_a_969_);
v___x_999_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_value_998_, v_a_969_, v_a_997_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 1);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 2);
v_code_968_ = v_k_978_;
v_a_970_ = v_a_1000_;
goto _start;
}
else
{
lean_dec_ref(v_k_978_);
lean_dec_ref(v_a_969_);
return v___x_999_;
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v_k_978_);
lean_dec_ref(v_decl_977_);
lean_dec_ref(v_a_969_);
v_a_1002_ = lean_ctor_get(v___x_979_, 0);
v_a_1003_ = lean_ctor_get(v___x_979_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_979_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_inc(v_a_1002_);
lean_dec(v___x_979_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1002_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
case 2:
{
lean_object* v_decl_1011_; lean_object* v_k_1012_; lean_object* v_value_1013_; lean_object* v___x_1014_; 
v_decl_1011_ = lean_ctor_get(v_code_968_, 0);
lean_inc_ref(v_decl_1011_);
v_k_1012_ = lean_ctor_get(v_code_968_, 1);
lean_inc_ref(v_k_1012_);
lean_dec_ref_known(v_code_968_, 2);
v_value_1013_ = lean_ctor_get(v_decl_1011_, 4);
lean_inc_ref(v_value_1013_);
lean_dec_ref(v_decl_1011_);
lean_inc_ref(v_a_969_);
v___x_1014_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_value_1013_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 1);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___x_1014_, 2);
v_code_968_ = v_k_1012_;
v_a_970_ = v_a_1015_;
goto _start;
}
else
{
lean_dec_ref(v_k_1012_);
lean_dec_ref(v_a_969_);
return v___x_1014_;
}
}
case 3:
{
lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref(v_a_969_);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_code_968_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; lean_object* v_unused_1026_; 
v_unused_1025_ = lean_ctor_get(v_code_968_, 1);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_code_968_, 0);
lean_dec(v_unused_1026_);
v___x_1018_ = v_code_968_;
v_isShared_1019_ = v_isSharedCheck_1024_;
goto v_resetjp_1017_;
}
else
{
lean_dec(v_code_968_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1024_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1020_ = lean_box(0);
if (v_isShared_1019_ == 0)
{
lean_ctor_set_tag(v___x_1018_, 0);
lean_ctor_set(v___x_1018_, 1, v_a_970_);
lean_ctor_set(v___x_1018_, 0, v___x_1020_);
v___x_1022_ = v___x_1018_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_a_970_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
case 4:
{
lean_object* v_cases_1027_; lean_object* v_alts_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; 
v_cases_1027_ = lean_ctor_get(v_code_968_, 0);
lean_inc_ref(v_cases_1027_);
lean_dec_ref_known(v_code_968_, 1);
v_alts_1028_ = lean_ctor_get(v_cases_1027_, 3);
lean_inc_ref(v_alts_1028_);
lean_dec_ref(v_cases_1027_);
v___x_1029_ = lean_unsigned_to_nat(0u);
v___x_1030_ = lean_array_get_size(v_alts_1028_);
v___x_1031_ = lean_box(0);
v___x_1032_ = lean_nat_dec_lt(v___x_1029_, v___x_1030_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; 
lean_dec_ref(v_alts_1028_);
lean_dec_ref(v_a_969_);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v_a_970_);
return v___x_1033_;
}
else
{
uint8_t v___x_1034_; 
v___x_1034_ = lean_nat_dec_le(v___x_1030_, v___x_1030_);
if (v___x_1034_ == 0)
{
if (v___x_1032_ == 0)
{
lean_object* v___x_1035_; 
lean_dec_ref(v_alts_1028_);
lean_dec_ref(v_a_969_);
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1031_);
lean_ctor_set(v___x_1035_, 1, v_a_970_);
return v___x_1035_;
}
else
{
size_t v___x_1036_; size_t v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = ((size_t)0ULL);
v___x_1037_ = lean_usize_of_nat(v___x_1030_);
v___x_1038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(v_alts_1028_, v___x_1036_, v___x_1037_, v___x_1031_, v_a_969_, v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec_ref(v_alts_1028_);
return v___x_1038_;
}
}
else
{
size_t v___x_1039_; size_t v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = ((size_t)0ULL);
v___x_1040_ = lean_usize_of_nat(v___x_1030_);
v___x_1041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(v_alts_1028_, v___x_1039_, v___x_1040_, v___x_1031_, v_a_969_, v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec_ref(v_alts_1028_);
return v___x_1041_;
}
}
}
default: 
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_dec_ref(v_a_969_);
lean_dec_ref(v_code_968_);
v___x_1042_ = lean_box(0);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v_a_970_);
return v___x_1043_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0(lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_c_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_decls_1049_; lean_object* v_main_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v_decls_1049_ = lean_ctor_get(v___y_1047_, 0);
v_main_1050_ = lean_ctor_get(v___y_1047_, 1);
v___x_1051_ = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(v_a_1044_, v_a_1045_);
lean_inc_ref(v_main_1050_);
lean_inc_ref(v_decls_1049_);
v___x_1052_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1052_, 0, v_decls_1049_);
lean_ctor_set(v___x_1052_, 1, v_main_1050_);
lean_ctor_set(v___x_1052_, 2, v___x_1051_);
v___x_1053_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_c_1046_, v___x_1052_, v___y_1048_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalLetValue___boxed(lean_object* v_e_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_Compiler_LCNF_FixedParams_evalLetValue(v_e_1054_, v_a_1055_, v_a_1056_);
lean_dec_ref(v_a_1055_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9___boxed(lean_object* v_as_1058_, lean_object* v_i_1059_, lean_object* v_stop_1060_, lean_object* v_b_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
size_t v_i_boxed_1064_; size_t v_stop_boxed_1065_; lean_object* v_res_1066_; 
v_i_boxed_1064_ = lean_unbox_usize(v_i_1059_);
lean_dec(v_i_1059_);
v_stop_boxed_1065_ = lean_unbox_usize(v_stop_1060_);
lean_dec(v_stop_1060_);
v_res_1066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(v_as_1058_, v_i_boxed_1064_, v_stop_boxed_1065_, v_b_1061_, v___y_1062_, v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec_ref(v_as_1058_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp___boxed(lean_object* v_declName_1067_, lean_object* v_args_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_Compiler_LCNF_FixedParams_evalApp(v_declName_1067_, v_args_1068_, v_a_1069_, v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec_ref(v_args_1068_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___boxed(lean_object* v_declName_1072_, lean_object* v_args_1073_, lean_object* v_as_1074_, lean_object* v_sz_1075_, lean_object* v_i_1076_, lean_object* v_b_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
size_t v_sz_boxed_1080_; size_t v_i_boxed_1081_; lean_object* v_res_1082_; 
v_sz_boxed_1080_ = lean_unbox_usize(v_sz_1075_);
lean_dec(v_sz_1075_);
v_i_boxed_1081_ = lean_unbox_usize(v_i_1076_);
lean_dec(v_i_1076_);
v_res_1082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(v_declName_1072_, v_args_1073_, v_as_1074_, v_sz_boxed_1080_, v_i_boxed_1081_, v_b_1077_, v___y_1078_, v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec_ref(v_as_1074_);
lean_dec_ref(v_args_1073_);
return v_res_1082_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3(uint8_t v_pu_1083_, lean_object* v_f_1084_, lean_object* v_v_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v_f_1084_, v_v_1085_, v___y_1086_, v___y_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1083_ = stack[0].m_num;
lean_object* v_f_1084_ = stack[1].m_obj;
lean_object* v_v_1085_ = stack[2].m_obj;
lean_object* v___y_1086_ = stack[3].m_obj;
lean_object* v___y_1087_ = stack[4].m_obj;
lean_object* v_res_1089_;
v_res_1089_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3(v_pu_1083_, v_f_1084_, v_v_1085_, v___y_1086_, v___y_1087_);
stack->m_obj
 = v_res_1089_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___boxed(lean_object* v_pu_1090_, lean_object* v_f_1091_, lean_object* v_v_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
uint8_t v_pu_boxed_1095_; lean_object* v_res_1096_; 
v_pu_boxed_1095_ = lean_unbox(v_pu_1090_);
v_res_1096_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3(v_pu_boxed_1095_, v_f_1091_, v_v_1092_, v___y_1093_, v___y_1094_);
lean_dec_ref(v___y_1093_);
return v_res_1096_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1(lean_object* v_00_u03b2_1097_, lean_object* v_m_1098_, lean_object* v_a_1099_){
_start:
{
uint8_t v___x_1100_; 
v___x_1100_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_m_1098_, v_a_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1098_ = stack[1].m_obj;
lean_object* v_a_1099_ = stack[2].m_obj;
uint8_t v_res_1101_;
v_res_1101_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1(lean_box(0), v_m_1098_, v_a_1099_);
stack->m_num = v_res_1101_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___boxed(lean_object* v_00_u03b2_1102_, lean_object* v_m_1103_, lean_object* v_a_1104_){
_start:
{
uint8_t v_res_1105_; lean_object* v_r_1106_; 
v_res_1105_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1(v_00_u03b2_1102_, v_m_1103_, v_a_1104_);
lean_dec_ref(v_a_1104_);
lean_dec_ref(v_m_1103_);
v_r_1106_ = lean_box(v_res_1105_);
return v_r_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2(lean_object* v_00_u03b2_1107_, lean_object* v_m_1108_, lean_object* v_a_1109_, lean_object* v_b_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(v_m_1108_, v_a_1109_, v_b_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4(lean_object* v_upperBound_1112_, lean_object* v_args_1113_, lean_object* v_inst_1114_, lean_object* v_R_1115_, lean_object* v_a_1116_, lean_object* v_b_1117_, lean_object* v_c_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v_upperBound_1112_, v_args_1113_, v_a_1116_, v_b_1117_, v___y_1119_, v___y_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___boxed(lean_object* v_upperBound_1122_, lean_object* v_args_1123_, lean_object* v_inst_1124_, lean_object* v_R_1125_, lean_object* v_a_1126_, lean_object* v_b_1127_, lean_object* v_c_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4(v_upperBound_1122_, v_args_1123_, v_inst_1124_, v_R_1125_, v_a_1126_, v_b_1127_, v_c_1128_, v___y_1129_, v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec_ref(v_args_1123_);
lean_dec(v_upperBound_1122_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7(lean_object* v_upperBound_1132_, lean_object* v_args_1133_, lean_object* v_inst_1134_, lean_object* v_R_1135_, lean_object* v_a_1136_, lean_object* v_b_1137_, lean_object* v_c_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(v_upperBound_1132_, v_args_1133_, v_a_1136_, v_b_1137_, v___y_1139_, v___y_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___boxed(lean_object* v_upperBound_1142_, lean_object* v_args_1143_, lean_object* v_inst_1144_, lean_object* v_R_1145_, lean_object* v_a_1146_, lean_object* v_b_1147_, lean_object* v_c_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7(v_upperBound_1142_, v_args_1143_, v_inst_1144_, v_R_1145_, v_a_1146_, v_b_1147_, v_c_1148_, v___y_1149_, v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec_ref(v_args_1143_);
lean_dec(v_upperBound_1142_);
return v_res_1151_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1(lean_object* v_00_u03b2_1152_, lean_object* v_a_1153_, lean_object* v_x_1154_){
_start:
{
uint8_t v___x_1155_; 
v___x_1155_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_1153_, v_x_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1153_ = stack[1].m_obj;
lean_object* v_x_1154_ = stack[2].m_obj;
uint8_t v_res_1156_;
v_res_1156_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1(lean_box(0), v_a_1153_, v_x_1154_);
stack->m_num = v_res_1156_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1157_, lean_object* v_a_1158_, lean_object* v_x_1159_){
_start:
{
uint8_t v_res_1160_; lean_object* v_r_1161_; 
v_res_1160_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1(v_00_u03b2_1157_, v_a_1158_, v_x_1159_);
lean_dec(v_x_1159_);
lean_dec_ref(v_a_1158_);
v_r_1161_ = lean_box(v_res_1160_);
return v_r_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4(lean_object* v_00_u03b2_1162_, lean_object* v_data_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(v_data_1163_);
return v___x_1164_;
}
}
uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4(lean_object* v_xs_1165_, lean_object* v_ys_1166_, lean_object* v_hsz_1167_, lean_object* v_x_1168_, lean_object* v_x_1169_){
_start:
{
uint8_t v___x_1170_; 
v___x_1170_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(v_xs_1165_, v_ys_1166_, v_x_1168_);
return v___x_1170_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1165_ = stack[0].m_obj;
lean_object* v_ys_1166_ = stack[1].m_obj;
lean_object* v_x_1168_ = stack[3].m_obj;
uint8_t v_res_1171_;
v_res_1171_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4(v_xs_1165_, v_ys_1166_, lean_box(0), v_x_1168_, lean_box(0));
stack->m_num = v_res_1171_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___boxed(lean_object* v_xs_1172_, lean_object* v_ys_1173_, lean_object* v_hsz_1174_, lean_object* v_x_1175_, lean_object* v_x_1176_){
_start:
{
uint8_t v_res_1177_; lean_object* v_r_1178_; 
v_res_1177_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4(v_xs_1172_, v_ys_1173_, v_hsz_1174_, v_x_1175_, v_x_1176_);
lean_dec_ref(v_ys_1173_);
lean_dec_ref(v_xs_1172_);
v_r_1178_ = lean_box(v_res_1177_);
return v_r_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_1179_, lean_object* v_i_1180_, lean_object* v_source_1181_, lean_object* v_target_1182_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(v_i_1180_, v_source_1181_, v_target_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14(lean_object* v_00_u03b2_1184_, lean_object* v_x_1185_, lean_object* v_x_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(v_x_1185_, v_x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(lean_object* v_upperBound_1188_, lean_object* v_a_1189_, lean_object* v_b_1190_){
_start:
{
uint8_t v___x_1191_; 
v___x_1191_ = lean_nat_dec_lt(v_a_1189_, v_upperBound_1188_);
if (v___x_1191_ == 0)
{
lean_dec(v_a_1189_);
return v_b_1190_;
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_inc(v_a_1189_);
v___x_1192_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1192_, 0, v_a_1189_);
v___x_1193_ = lean_array_push(v_b_1190_, v___x_1192_);
v___x_1194_ = lean_unsigned_to_nat(1u);
v___x_1195_ = lean_nat_add(v_a_1189_, v___x_1194_);
lean_dec(v_a_1189_);
v_a_1189_ = v___x_1195_;
v_b_1190_ = v___x_1193_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg___boxed(lean_object* v_upperBound_1197_, lean_object* v_a_1198_, lean_object* v_b_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_upperBound_1197_, v_a_1198_, v_b_1199_);
lean_dec(v_upperBound_1197_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(lean_object* v_numParams_1201_){
_start:
{
lean_object* v___x_1202_; lean_object* v_values_1203_; lean_object* v___x_1204_; 
v___x_1202_ = lean_unsigned_to_nat(0u);
v_values_1203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0));
v___x_1204_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_numParams_1201_, v___x_1202_, v_values_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkInitialValues___boxed(lean_object* v_numParams_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(v_numParams_1205_);
lean_dec(v_numParams_1205_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0(lean_object* v_upperBound_1207_, lean_object* v_inst_1208_, lean_object* v_R_1209_, lean_object* v_a_1210_, lean_object* v_b_1211_, lean_object* v_c_1212_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_upperBound_1207_, v_a_1210_, v_b_1211_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___boxed(lean_object* v_upperBound_1214_, lean_object* v_inst_1215_, lean_object* v_R_1216_, lean_object* v_a_1217_, lean_object* v_b_1218_, lean_object* v_c_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0(v_upperBound_1214_, v_inst_1215_, v_R_1216_, v_a_1217_, v_b_1218_, v_c_1219_);
lean_dec(v_upperBound_1214_);
return v_res_1220_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = lean_box(0);
v___x_1222_ = lean_unsigned_to_nat(16u);
v___x_1223_ = lean_mk_array(v___x_1222_, v___x_1221_);
return v___x_1223_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0);
v___x_1225_ = lean_unsigned_to_nat(0u);
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v___x_1224_);
return v___x_1226_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(lean_object* v_decls_1227_, lean_object* v_as_1228_, size_t v_sz_1229_, size_t v_i_1230_, lean_object* v_b_1231_){
_start:
{
lean_object* v_a_1233_; uint8_t v___x_1237_; 
v___x_1237_ = lean_usize_dec_lt(v_i_1230_, v_sz_1229_);
if (v___x_1237_ == 0)
{
lean_dec_ref(v_decls_1227_);
return v_b_1231_;
}
else
{
lean_object* v_a_1238_; lean_object* v_toSignature_1239_; lean_object* v_value_1240_; lean_object* v_name_1241_; lean_object* v_params_1242_; lean_object* v_s_1244_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_a_1238_ = lean_array_uget_borrowed(v_as_1228_, v_i_1230_);
v_toSignature_1239_ = lean_ctor_get(v_a_1238_, 0);
v_value_1240_ = lean_ctor_get(v_a_1238_, 1);
v_name_1241_ = lean_ctor_get(v_toSignature_1239_, 0);
v_params_1242_ = lean_ctor_get(v_toSignature_1239_, 3);
v___x_1247_ = lean_array_get_size(v_params_1242_);
v___x_1248_ = l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(v___x_1247_);
v___x_1249_ = lean_box(v___x_1237_);
v___x_1250_ = lean_mk_array(v___x_1247_, v___x_1249_);
if (lean_obj_tag(v_value_1240_) == 0)
{
lean_object* v_code_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v_a_1257_; 
v_code_1251_ = lean_ctor_get(v_value_1240_, 0);
v___x_1252_ = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(v_a_1238_, v___x_1248_);
lean_inc(v_a_1238_);
lean_inc_ref(v_decls_1227_);
v___x_1253_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1253_, 0, v_decls_1227_);
lean_ctor_set(v___x_1253_, 1, v_a_1238_);
lean_ctor_set(v___x_1253_, 2, v___x_1252_);
v___x_1254_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1);
v___x_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
lean_ctor_set(v___x_1255_, 1, v___x_1250_);
lean_inc_ref(v_code_1251_);
v___x_1256_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_code_1251_, v___x_1253_, v___x_1255_);
v_a_1257_ = lean_ctor_get(v___x_1256_, 1);
lean_inc(v_a_1257_);
lean_dec_ref(v___x_1256_);
v_s_1244_ = v_a_1257_;
goto v___jp_1243_;
}
else
{
lean_object* v___x_1258_; 
lean_dec_ref(v___x_1248_);
lean_inc(v_name_1241_);
v___x_1258_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1241_, v___x_1250_, v_b_1231_);
v_a_1233_ = v___x_1258_;
goto v___jp_1232_;
}
v___jp_1243_:
{
lean_object* v_fixed_1245_; lean_object* v___x_1246_; 
v_fixed_1245_ = lean_ctor_get(v_s_1244_, 1);
lean_inc_ref(v_fixed_1245_);
lean_dec_ref(v_s_1244_);
lean_inc(v_name_1241_);
v___x_1246_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1241_, v_fixed_1245_, v_b_1231_);
v_a_1233_ = v___x_1246_;
goto v___jp_1232_;
}
}
v___jp_1232_:
{
size_t v___x_1234_; size_t v___x_1235_; 
v___x_1234_ = ((size_t)1ULL);
v___x_1235_ = lean_usize_add(v_i_1230_, v___x_1234_);
v_i_1230_ = v___x_1235_;
v_b_1231_ = v_a_1233_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_1227_ = stack[0].m_obj;
lean_object* v_as_1228_ = stack[1].m_obj;
size_t v_sz_1229_ = stack[2].m_num;
size_t v_i_1230_ = stack[3].m_num;
lean_object* v_b_1231_ = stack[4].m_obj;
lean_object* v_res_1259_;
v_res_1259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(v_decls_1227_, v_as_1228_, v_sz_1229_, v_i_1230_, v_b_1231_);
stack->m_obj
 = v_res_1259_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___boxed(lean_object* v_decls_1260_, lean_object* v_as_1261_, lean_object* v_sz_1262_, lean_object* v_i_1263_, lean_object* v_b_1264_){
_start:
{
size_t v_sz_boxed_1265_; size_t v_i_boxed_1266_; lean_object* v_res_1267_; 
v_sz_boxed_1265_ = lean_unbox_usize(v_sz_1262_);
lean_dec(v_sz_1262_);
v_i_boxed_1266_ = lean_unbox_usize(v_i_1263_);
lean_dec(v_i_1263_);
v_res_1267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(v_decls_1260_, v_as_1261_, v_sz_boxed_1265_, v_i_boxed_1266_, v_b_1264_);
lean_dec_ref(v_as_1261_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFixedParamsMap(lean_object* v_decls_1268_){
_start:
{
lean_object* v_result_1269_; size_t v_sz_1270_; size_t v___x_1271_; lean_object* v___x_1272_; 
v_result_1269_ = lean_box(1);
v_sz_1270_ = lean_array_size(v_decls_1268_);
v___x_1271_ = ((size_t)0ULL);
lean_inc_ref(v_decls_1268_);
v___x_1272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(v_decls_1268_, v_decls_1268_, v_sz_1270_, v___x_1271_, v_result_1269_);
lean_dec_ref(v_decls_1268_);
return v___x_1272_;
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
