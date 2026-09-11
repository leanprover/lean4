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
uint8_t v___x_3428__boxed_338_; lean_object* v_res_339_; 
v___x_3428__boxed_338_ = lean_unbox(v___x_333_);
v_res_339_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_331_, v_args_332_, v___x_3428__boxed_338_, v_range_334_, v_b_335_, v_i_336_, v___y_337_);
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
lean_dec_ref_known(v_value_351_, 2);
lean_dec_ref(v_decl_352_);
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
uint8_t v___x_3632__boxed_442_; lean_object* v_res_443_; 
v___x_3632__boxed_442_ = lean_unbox(v___x_434_);
v_res_443_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0(v_params_432_, v_args_433_, v___x_3632__boxed_442_, v_range_435_, v_b_436_, v_i_437_, v_hs_438_, v_hl_439_, v___y_440_, v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec_ref(v_range_435_);
lean_dec_ref(v_args_433_);
lean_dec_ref(v_params_432_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(lean_object* v_upperBound_444_, lean_object* v_args_445_, lean_object* v_a_446_, lean_object* v_b_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_a_451_; lean_object* v_a_452_; uint8_t v___x_456_; 
v___x_456_ = lean_nat_dec_lt(v_a_446_, v_upperBound_444_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
lean_dec(v_a_446_);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v_b_447_);
lean_ctor_set(v___x_457_, 1, v___y_449_);
return v___x_457_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_458_ = lean_box(0);
v___x_459_ = lean_array_get_size(v_args_445_);
v___x_460_ = lean_nat_dec_lt(v_a_446_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v_visited_461_; lean_object* v_fixed_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_471_; 
v_visited_461_ = lean_ctor_get(v___y_449_, 0);
v_fixed_462_ = lean_ctor_get(v___y_449_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v___y_449_);
if (v_isSharedCheck_471_ == 0)
{
v___x_464_ = v___y_449_;
v_isShared_465_ = v_isSharedCheck_471_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_fixed_462_);
lean_inc(v_visited_461_);
lean_dec(v___y_449_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_471_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_466_ = lean_box(v___x_460_);
v___x_467_ = lean_array_set(v_fixed_462_, v_a_446_, v___x_466_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v___x_467_);
v___x_469_ = v___x_464_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_visited_461_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
v_a_451_ = v___x_458_;
v_a_452_ = v___x_469_;
goto v___jp_450_;
}
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_array_fget_borrowed(v_args_445_, v_a_446_);
v___x_473_ = l_Lean_Compiler_LCNF_FixedParams_evalArg(v___x_472_, v___y_448_, v___y_449_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v_a_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
v_a_475_ = lean_ctor_get(v___x_473_, 1);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_473_, 2);
lean_inc(v_a_446_);
v___x_476_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_476_, 0, v_a_446_);
v___x_477_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v_a_474_, v___x_476_);
lean_dec_ref_known(v___x_476_, 1);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = lean_box(1);
v___x_479_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v_a_474_, v___x_478_);
lean_dec(v_a_474_);
if (v___x_479_ == 0)
{
lean_object* v_visited_480_; lean_object* v_fixed_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_490_; 
v_visited_480_ = lean_ctor_get(v_a_475_, 0);
v_fixed_481_ = lean_ctor_get(v_a_475_, 1);
v_isSharedCheck_490_ = !lean_is_exclusive(v_a_475_);
if (v_isSharedCheck_490_ == 0)
{
v___x_483_ = v_a_475_;
v_isShared_484_ = v_isSharedCheck_490_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_fixed_481_);
lean_inc(v_visited_480_);
lean_dec(v_a_475_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_490_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_485_ = lean_box(v___x_479_);
v___x_486_ = lean_array_set(v_fixed_481_, v_a_446_, v___x_485_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v___x_486_);
v___x_488_ = v___x_483_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_visited_480_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
v_a_451_ = v___x_458_;
v_a_452_ = v___x_488_;
goto v___jp_450_;
}
}
}
else
{
v_a_451_ = v___x_458_;
v_a_452_ = v_a_475_;
goto v___jp_450_;
}
}
else
{
lean_dec(v_a_474_);
v_a_451_ = v___x_458_;
v_a_452_ = v_a_475_;
goto v___jp_450_;
}
}
else
{
lean_object* v_a_491_; lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
lean_dec(v_a_446_);
v_a_491_ = lean_ctor_get(v___x_473_, 0);
v_a_492_ = lean_ctor_get(v___x_473_, 1);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_473_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_inc(v_a_491_);
lean_dec(v___x_473_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_491_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
v___jp_450_:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_unsigned_to_nat(1u);
v___x_454_ = lean_nat_add(v_a_446_, v___x_453_);
lean_dec(v_a_446_);
v_a_446_ = v___x_454_;
v_b_447_ = v_a_451_;
v___y_449_ = v_a_452_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg___boxed(lean_object* v_upperBound_500_, lean_object* v_args_501_, lean_object* v_a_502_, lean_object* v_b_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(v_upperBound_500_, v_args_501_, v_a_502_, v_b_503_, v___y_504_, v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec_ref(v_args_501_);
lean_dec(v_upperBound_500_);
return v_res_506_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(lean_object* v_xs_507_, lean_object* v_ys_508_, lean_object* v_x_509_){
_start:
{
lean_object* v_zero_510_; uint8_t v_isZero_511_; 
v_zero_510_ = lean_unsigned_to_nat(0u);
v_isZero_511_ = lean_nat_dec_eq(v_x_509_, v_zero_510_);
if (v_isZero_511_ == 1)
{
lean_dec(v_x_509_);
return v_isZero_511_;
}
else
{
lean_object* v_one_512_; lean_object* v_n_513_; lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v_one_512_ = lean_unsigned_to_nat(1u);
v_n_513_ = lean_nat_sub(v_x_509_, v_one_512_);
lean_dec(v_x_509_);
v___x_514_ = lean_array_fget_borrowed(v_xs_507_, v_n_513_);
v___x_515_ = lean_array_fget_borrowed(v_ys_508_, v_n_513_);
v___x_516_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v___x_514_, v___x_515_);
if (v___x_516_ == 0)
{
lean_dec(v_n_513_);
return v___x_516_;
}
else
{
v_x_509_ = v_n_513_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_xs_518_, lean_object* v_ys_519_, lean_object* v_x_520_){
_start:
{
uint8_t v_res_521_; lean_object* v_r_522_; 
v_res_521_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(v_xs_518_, v_ys_519_, v_x_520_);
lean_dec_ref(v_ys_519_);
lean_dec_ref(v_xs_518_);
v_r_522_ = lean_box(v_res_521_);
return v_r_522_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(lean_object* v_a_523_, lean_object* v_x_524_){
_start:
{
if (lean_obj_tag(v_x_524_) == 0)
{
uint8_t v___x_525_; 
v___x_525_ = 0;
return v___x_525_;
}
else
{
lean_object* v_key_526_; lean_object* v_tail_527_; uint8_t v___y_529_; lean_object* v_fst_531_; lean_object* v_snd_532_; lean_object* v_fst_533_; lean_object* v_snd_534_; uint8_t v___x_535_; 
v_key_526_ = lean_ctor_get(v_x_524_, 0);
v_tail_527_ = lean_ctor_get(v_x_524_, 2);
v_fst_531_ = lean_ctor_get(v_key_526_, 0);
v_snd_532_ = lean_ctor_get(v_key_526_, 1);
v_fst_533_ = lean_ctor_get(v_a_523_, 0);
v_snd_534_ = lean_ctor_get(v_a_523_, 1);
v___x_535_ = lean_name_eq(v_fst_531_, v_fst_533_);
if (v___x_535_ == 0)
{
v___y_529_ = v___x_535_;
goto v___jp_528_;
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_536_ = lean_array_get_size(v_snd_532_);
v___x_537_ = lean_array_get_size(v_snd_534_);
v___x_538_ = lean_nat_dec_eq(v___x_536_, v___x_537_);
if (v___x_538_ == 0)
{
v_x_524_ = v_tail_527_;
goto _start;
}
else
{
uint8_t v___x_540_; 
v___x_540_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(v_snd_532_, v_snd_534_, v___x_536_);
v___y_529_ = v___x_540_;
goto v___jp_528_;
}
}
v___jp_528_:
{
if (v___y_529_ == 0)
{
v_x_524_ = v_tail_527_;
goto _start;
}
else
{
return v___y_529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg___boxed(lean_object* v_a_541_, lean_object* v_x_542_){
_start:
{
uint8_t v_res_543_; lean_object* v_r_544_; 
v_res_543_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_541_, v_x_542_);
lean_dec(v_x_542_);
lean_dec_ref(v_a_541_);
v_r_544_ = lean_box(v_res_543_);
return v_r_544_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(lean_object* v_as_545_, size_t v_i_546_, size_t v_stop_547_, uint64_t v_b_548_){
_start:
{
uint8_t v___x_549_; 
v___x_549_ = lean_usize_dec_eq(v_i_546_, v_stop_547_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; uint64_t v___x_551_; uint64_t v___x_552_; size_t v___x_553_; size_t v___x_554_; 
v___x_550_ = lean_array_uget_borrowed(v_as_545_, v_i_546_);
v___x_551_ = l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash(v___x_550_);
v___x_552_ = lean_uint64_mix_hash(v_b_548_, v___x_551_);
v___x_553_ = ((size_t)1ULL);
v___x_554_ = lean_usize_add(v_i_546_, v___x_553_);
v_i_546_ = v___x_554_;
v_b_548_ = v___x_552_;
goto _start;
}
else
{
return v_b_548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2___boxed(lean_object* v_as_556_, lean_object* v_i_557_, lean_object* v_stop_558_, lean_object* v_b_559_){
_start:
{
size_t v_i_boxed_560_; size_t v_stop_boxed_561_; uint64_t v_b_boxed_562_; uint64_t v_res_563_; lean_object* v_r_564_; 
v_i_boxed_560_ = lean_unbox_usize(v_i_557_);
lean_dec(v_i_557_);
v_stop_boxed_561_ = lean_unbox_usize(v_stop_558_);
lean_dec(v_stop_558_);
v_b_boxed_562_ = lean_unbox_uint64(v_b_559_);
lean_dec_ref(v_b_559_);
v_res_563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_as_556_, v_i_boxed_560_, v_stop_boxed_561_, v_b_boxed_562_);
lean_dec_ref(v_as_556_);
v_r_564_ = lean_box_uint64(v_res_563_);
return v_r_564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
return v_x_565_;
}
else
{
lean_object* v_key_567_; lean_object* v_value_568_; lean_object* v_tail_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_608_; 
v_key_567_ = lean_ctor_get(v_x_566_, 0);
v_value_568_ = lean_ctor_get(v_x_566_, 1);
v_tail_569_ = lean_ctor_get(v_x_566_, 2);
v_isSharedCheck_608_ = !lean_is_exclusive(v_x_566_);
if (v_isSharedCheck_608_ == 0)
{
v___x_571_ = v_x_566_;
v_isShared_572_ = v_isSharedCheck_608_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_tail_569_);
lean_inc(v_value_568_);
lean_inc(v_key_567_);
lean_dec(v_x_566_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_608_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v_fst_573_; lean_object* v_snd_574_; lean_object* v___x_575_; uint64_t v___y_577_; uint64_t v___y_578_; uint64_t v___y_598_; 
v_fst_573_ = lean_ctor_get(v_key_567_, 0);
v_snd_574_ = lean_ctor_get(v_key_567_, 1);
v___x_575_ = lean_array_get_size(v_x_565_);
if (lean_obj_tag(v_fst_573_) == 0)
{
uint64_t v___x_606_; 
v___x_606_ = 1723ULL;
v___y_598_ = v___x_606_;
goto v___jp_597_;
}
else
{
uint64_t v_hash_607_; 
v_hash_607_ = lean_ctor_get_uint64(v_fst_573_, sizeof(void*)*2);
v___y_598_ = v_hash_607_;
goto v___jp_597_;
}
v___jp_576_:
{
uint64_t v___x_579_; uint64_t v___x_580_; uint64_t v___x_581_; uint64_t v_fold_582_; uint64_t v___x_583_; uint64_t v___x_584_; uint64_t v___x_585_; size_t v___x_586_; size_t v___x_587_; size_t v___x_588_; size_t v___x_589_; size_t v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_579_ = lean_uint64_mix_hash(v___y_577_, v___y_578_);
v___x_580_ = 32ULL;
v___x_581_ = lean_uint64_shift_right(v___x_579_, v___x_580_);
v_fold_582_ = lean_uint64_xor(v___x_579_, v___x_581_);
v___x_583_ = 16ULL;
v___x_584_ = lean_uint64_shift_right(v_fold_582_, v___x_583_);
v___x_585_ = lean_uint64_xor(v_fold_582_, v___x_584_);
v___x_586_ = lean_uint64_to_usize(v___x_585_);
v___x_587_ = lean_usize_of_nat(v___x_575_);
v___x_588_ = ((size_t)1ULL);
v___x_589_ = lean_usize_sub(v___x_587_, v___x_588_);
v___x_590_ = lean_usize_land(v___x_586_, v___x_589_);
v___x_591_ = lean_array_uget_borrowed(v_x_565_, v___x_590_);
lean_inc(v___x_591_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 2, v___x_591_);
v___x_593_ = v___x_571_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_key_567_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_value_568_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v___x_591_);
v___x_593_ = v_reuseFailAlloc_596_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_594_; 
v___x_594_ = lean_array_uset(v_x_565_, v___x_590_, v___x_593_);
v_x_565_ = v___x_594_;
v_x_566_ = v_tail_569_;
goto _start;
}
}
v___jp_597_:
{
uint64_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_599_ = 7ULL;
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = lean_array_get_size(v_snd_574_);
v___x_602_ = lean_nat_dec_lt(v___x_600_, v___x_601_);
if (v___x_602_ == 0)
{
v___y_577_ = v___y_598_;
v___y_578_ = v___x_599_;
goto v___jp_576_;
}
else
{
size_t v___x_603_; size_t v___x_604_; uint64_t v___x_605_; 
v___x_603_ = ((size_t)0ULL);
v___x_604_ = lean_usize_of_nat(v___x_601_);
v___x_605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_574_, v___x_603_, v___x_604_, v___x_599_);
v___y_577_ = v___y_598_;
v___y_578_ = v___x_605_;
goto v___jp_576_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(lean_object* v_i_609_, lean_object* v_source_610_, lean_object* v_target_611_){
_start:
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_array_get_size(v_source_610_);
v___x_613_ = lean_nat_dec_lt(v_i_609_, v___x_612_);
if (v___x_613_ == 0)
{
lean_dec_ref(v_source_610_);
lean_dec(v_i_609_);
return v_target_611_;
}
else
{
lean_object* v_es_614_; lean_object* v___x_615_; lean_object* v_source_616_; lean_object* v_target_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v_es_614_ = lean_array_fget(v_source_610_, v_i_609_);
v___x_615_ = lean_box(0);
v_source_616_ = lean_array_fset(v_source_610_, v_i_609_, v___x_615_);
v_target_617_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(v_target_611_, v_es_614_);
v___x_618_ = lean_unsigned_to_nat(1u);
v___x_619_ = lean_nat_add(v_i_609_, v___x_618_);
lean_dec(v_i_609_);
v_i_609_ = v___x_619_;
v_source_610_ = v_source_616_;
v_target_611_ = v_target_617_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(lean_object* v_data_621_){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v_nbuckets_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_622_ = lean_array_get_size(v_data_621_);
v___x_623_ = lean_unsigned_to_nat(2u);
v_nbuckets_624_ = lean_nat_mul(v___x_622_, v___x_623_);
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = lean_box(0);
v___x_627_ = lean_mk_array(v_nbuckets_624_, v___x_626_);
v___x_628_ = lean_array_propagate_mark(v_data_621_, v___x_627_);
v___x_629_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(v___x_625_, v_data_621_, v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(lean_object* v_m_630_, lean_object* v_a_631_, lean_object* v_b_632_){
_start:
{
lean_object* v_size_633_; lean_object* v_buckets_634_; lean_object* v_fst_635_; lean_object* v_snd_636_; lean_object* v___x_637_; uint64_t v___y_639_; uint64_t v___y_640_; uint64_t v___y_679_; 
v_size_633_ = lean_ctor_get(v_m_630_, 0);
v_buckets_634_ = lean_ctor_get(v_m_630_, 1);
v_fst_635_ = lean_ctor_get(v_a_631_, 0);
v_snd_636_ = lean_ctor_get(v_a_631_, 1);
v___x_637_ = lean_array_get_size(v_buckets_634_);
if (lean_obj_tag(v_fst_635_) == 0)
{
uint64_t v___x_687_; 
v___x_687_ = 1723ULL;
v___y_679_ = v___x_687_;
goto v___jp_678_;
}
else
{
uint64_t v_hash_688_; 
v_hash_688_ = lean_ctor_get_uint64(v_fst_635_, sizeof(void*)*2);
v___y_679_ = v_hash_688_;
goto v___jp_678_;
}
v___jp_638_:
{
uint64_t v___x_641_; uint64_t v___x_642_; uint64_t v___x_643_; uint64_t v_fold_644_; uint64_t v___x_645_; uint64_t v___x_646_; uint64_t v___x_647_; size_t v___x_648_; size_t v___x_649_; size_t v___x_650_; size_t v___x_651_; size_t v___x_652_; lean_object* v_bkt_653_; uint8_t v___x_654_; 
v___x_641_ = lean_uint64_mix_hash(v___y_639_, v___y_640_);
v___x_642_ = 32ULL;
v___x_643_ = lean_uint64_shift_right(v___x_641_, v___x_642_);
v_fold_644_ = lean_uint64_xor(v___x_641_, v___x_643_);
v___x_645_ = 16ULL;
v___x_646_ = lean_uint64_shift_right(v_fold_644_, v___x_645_);
v___x_647_ = lean_uint64_xor(v_fold_644_, v___x_646_);
v___x_648_ = lean_uint64_to_usize(v___x_647_);
v___x_649_ = lean_usize_of_nat(v___x_637_);
v___x_650_ = ((size_t)1ULL);
v___x_651_ = lean_usize_sub(v___x_649_, v___x_650_);
v___x_652_ = lean_usize_land(v___x_648_, v___x_651_);
v_bkt_653_ = lean_array_uget_borrowed(v_buckets_634_, v___x_652_);
v___x_654_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_631_, v_bkt_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_675_; 
lean_inc_ref(v_buckets_634_);
lean_inc(v_size_633_);
v_isSharedCheck_675_ = !lean_is_exclusive(v_m_630_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; lean_object* v_unused_677_; 
v_unused_676_ = lean_ctor_get(v_m_630_, 1);
lean_dec(v_unused_676_);
v_unused_677_ = lean_ctor_get(v_m_630_, 0);
lean_dec(v_unused_677_);
v___x_656_ = v_m_630_;
v_isShared_657_ = v_isSharedCheck_675_;
goto v_resetjp_655_;
}
else
{
lean_dec(v_m_630_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_675_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v_size_x27_659_; lean_object* v___x_660_; lean_object* v_buckets_x27_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_658_ = lean_unsigned_to_nat(1u);
v_size_x27_659_ = lean_nat_add(v_size_633_, v___x_658_);
lean_dec(v_size_633_);
lean_inc(v_bkt_653_);
v___x_660_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_660_, 0, v_a_631_);
lean_ctor_set(v___x_660_, 1, v_b_632_);
lean_ctor_set(v___x_660_, 2, v_bkt_653_);
v_buckets_x27_661_ = lean_array_uset(v_buckets_634_, v___x_652_, v___x_660_);
v___x_662_ = lean_unsigned_to_nat(4u);
v___x_663_ = lean_nat_mul(v_size_x27_659_, v___x_662_);
v___x_664_ = lean_unsigned_to_nat(3u);
v___x_665_ = lean_nat_div(v___x_663_, v___x_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_array_get_size(v_buckets_x27_661_);
v___x_667_ = lean_nat_dec_le(v___x_665_, v___x_666_);
lean_dec(v___x_665_);
if (v___x_667_ == 0)
{
lean_object* v_val_668_; lean_object* v___x_670_; 
v_val_668_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(v_buckets_x27_661_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 1, v_val_668_);
lean_ctor_set(v___x_656_, 0, v_size_x27_659_);
v___x_670_ = v___x_656_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_size_x27_659_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_val_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
else
{
lean_object* v___x_673_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 1, v_buckets_x27_661_);
lean_ctor_set(v___x_656_, 0, v_size_x27_659_);
v___x_673_ = v___x_656_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_size_x27_659_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_buckets_x27_661_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
else
{
lean_dec(v_b_632_);
lean_dec_ref(v_a_631_);
return v_m_630_;
}
}
v___jp_678_:
{
uint64_t v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_680_ = 7ULL;
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = lean_array_get_size(v_snd_636_);
v___x_683_ = lean_nat_dec_lt(v___x_681_, v___x_682_);
if (v___x_683_ == 0)
{
v___y_639_ = v___y_679_;
v___y_640_ = v___x_680_;
goto v___jp_638_;
}
else
{
size_t v___x_684_; size_t v___x_685_; uint64_t v___x_686_; 
v___x_684_ = ((size_t)0ULL);
v___x_685_ = lean_usize_of_nat(v___x_682_);
v___x_686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_636_, v___x_684_, v___x_685_, v___x_680_);
v___y_639_ = v___y_679_;
v___y_640_ = v___x_686_;
goto v___jp_638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(lean_object* v_f_689_, lean_object* v_v_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
if (lean_obj_tag(v_v_690_) == 0)
{
lean_object* v_code_693_; lean_object* v___x_694_; 
v_code_693_ = lean_ctor_get(v_v_690_, 0);
lean_inc_ref(v_code_693_);
lean_dec_ref_known(v_v_690_, 1);
lean_inc_ref(v___y_691_);
v___x_694_ = lean_apply_3(v_f_689_, v_code_693_, v___y_691_, v___y_692_);
return v___x_694_;
}
else
{
lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec_ref_known(v_v_690_, 1);
lean_dec_ref(v_f_689_);
v___x_695_ = lean_box(0);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v___y_692_);
return v___x_696_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg___boxed(lean_object* v_f_697_, lean_object* v_v_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v_f_697_, v_v_698_, v___y_699_, v___y_700_);
lean_dec_ref(v___y_699_);
return v_res_701_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(lean_object* v_m_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_buckets_704_; lean_object* v_fst_705_; lean_object* v_snd_706_; lean_object* v___x_707_; uint64_t v___y_709_; uint64_t v___y_710_; uint64_t v___y_726_; 
v_buckets_704_ = lean_ctor_get(v_m_702_, 1);
v_fst_705_ = lean_ctor_get(v_a_703_, 0);
v_snd_706_ = lean_ctor_get(v_a_703_, 1);
v___x_707_ = lean_array_get_size(v_buckets_704_);
if (lean_obj_tag(v_fst_705_) == 0)
{
uint64_t v___x_734_; 
v___x_734_ = 1723ULL;
v___y_726_ = v___x_734_;
goto v___jp_725_;
}
else
{
uint64_t v_hash_735_; 
v_hash_735_ = lean_ctor_get_uint64(v_fst_705_, sizeof(void*)*2);
v___y_726_ = v_hash_735_;
goto v___jp_725_;
}
v___jp_708_:
{
uint64_t v___x_711_; uint64_t v___x_712_; uint64_t v___x_713_; uint64_t v_fold_714_; uint64_t v___x_715_; uint64_t v___x_716_; uint64_t v___x_717_; size_t v___x_718_; size_t v___x_719_; size_t v___x_720_; size_t v___x_721_; size_t v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_711_ = lean_uint64_mix_hash(v___y_709_, v___y_710_);
v___x_712_ = 32ULL;
v___x_713_ = lean_uint64_shift_right(v___x_711_, v___x_712_);
v_fold_714_ = lean_uint64_xor(v___x_711_, v___x_713_);
v___x_715_ = 16ULL;
v___x_716_ = lean_uint64_shift_right(v_fold_714_, v___x_715_);
v___x_717_ = lean_uint64_xor(v_fold_714_, v___x_716_);
v___x_718_ = lean_uint64_to_usize(v___x_717_);
v___x_719_ = lean_usize_of_nat(v___x_707_);
v___x_720_ = ((size_t)1ULL);
v___x_721_ = lean_usize_sub(v___x_719_, v___x_720_);
v___x_722_ = lean_usize_land(v___x_718_, v___x_721_);
v___x_723_ = lean_array_uget_borrowed(v_buckets_704_, v___x_722_);
v___x_724_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_703_, v___x_723_);
return v___x_724_;
}
v___jp_725_:
{
uint64_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_727_ = 7ULL;
v___x_728_ = lean_unsigned_to_nat(0u);
v___x_729_ = lean_array_get_size(v_snd_706_);
v___x_730_ = lean_nat_dec_lt(v___x_728_, v___x_729_);
if (v___x_730_ == 0)
{
v___y_709_ = v___y_726_;
v___y_710_ = v___x_727_;
goto v___jp_708_;
}
else
{
size_t v___x_731_; size_t v___x_732_; uint64_t v___x_733_; 
v___x_731_ = ((size_t)0ULL);
v___x_732_ = lean_usize_of_nat(v___x_729_);
v___x_733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_706_, v___x_731_, v___x_732_, v___x_727_);
v___y_709_ = v___y_726_;
v___y_710_ = v___x_733_;
goto v___jp_708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg___boxed(lean_object* v_m_736_, lean_object* v_a_737_){
_start:
{
uint8_t v_res_738_; lean_object* v_r_739_; 
v_res_738_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_m_736_, v_a_737_);
lean_dec_ref(v_a_737_);
lean_dec_ref(v_m_736_);
v_r_739_ = lean_box(v_res_738_);
return v_r_739_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(lean_object* v_upperBound_740_, lean_object* v_args_741_, lean_object* v_a_742_, lean_object* v_b_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_a_747_; lean_object* v_a_748_; uint8_t v___x_752_; 
v___x_752_ = lean_nat_dec_lt(v_a_742_, v_upperBound_740_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; 
lean_dec(v_a_742_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v_b_743_);
lean_ctor_set(v___x_753_, 1, v___y_745_);
return v___x_753_;
}
else
{
lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_754_ = lean_array_get_size(v_args_741_);
v___x_755_ = lean_nat_dec_lt(v_a_742_, v___x_754_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_box(0);
v___x_757_ = lean_array_push(v_b_743_, v___x_756_);
v_a_747_ = v___x_757_;
v_a_748_ = v___y_745_;
goto v___jp_746_;
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_array_fget_borrowed(v_args_741_, v_a_742_);
v___x_759_ = l_Lean_Compiler_LCNF_FixedParams_evalArg(v___x_758_, v___y_744_, v___y_745_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v_a_761_; lean_object* v___x_762_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
v_a_761_ = lean_ctor_get(v___x_759_, 1);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_759_, 2);
v___x_762_ = lean_array_push(v_b_743_, v_a_760_);
v_a_747_ = v___x_762_;
v_a_748_ = v_a_761_;
goto v___jp_746_;
}
else
{
lean_object* v_a_763_; lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec_ref(v_b_743_);
lean_dec(v_a_742_);
v_a_763_ = lean_ctor_get(v___x_759_, 0);
v_a_764_ = lean_ctor_get(v___x_759_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_759_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_inc(v_a_763_);
lean_dec(v___x_759_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_763_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
v___jp_746_:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_unsigned_to_nat(1u);
v___x_750_ = lean_nat_add(v_a_742_, v___x_749_);
lean_dec(v_a_742_);
v_a_742_ = v___x_750_;
v_b_743_ = v_a_747_;
v___y_745_ = v_a_748_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg___boxed(lean_object* v_upperBound_772_, lean_object* v_args_773_, lean_object* v_a_774_, lean_object* v_b_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v_upperBound_772_, v_args_773_, v_a_774_, v_b_775_, v___y_776_, v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec_ref(v_args_773_);
lean_dec(v_upperBound_772_);
return v_res_778_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(uint8_t v_a_779_, uint8_t v___x_780_, lean_object* v_as_781_, size_t v_i_782_, size_t v_stop_783_){
_start:
{
uint8_t v___x_784_; 
v___x_784_ = lean_usize_dec_eq(v_i_782_, v_stop_783_);
if (v___x_784_ == 0)
{
uint8_t v___x_785_; uint8_t v___y_787_; lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_785_ = 1;
v___x_791_ = lean_array_uget_borrowed(v_as_781_, v_i_782_);
v___x_792_ = lean_unbox(v___x_791_);
if (v___x_792_ == 0)
{
if (v_a_779_ == 0)
{
v___y_787_ = v___x_780_;
goto v___jp_786_;
}
else
{
uint8_t v___x_793_; 
v___x_793_ = lean_unbox(v___x_791_);
v___y_787_ = v___x_793_;
goto v___jp_786_;
}
}
else
{
v___y_787_ = v_a_779_;
goto v___jp_786_;
}
v___jp_786_:
{
if (v___y_787_ == 0)
{
size_t v___x_788_; size_t v___x_789_; 
v___x_788_ = ((size_t)1ULL);
v___x_789_ = lean_usize_add(v_i_782_, v___x_788_);
v_i_782_ = v___x_789_;
goto _start;
}
else
{
return v___x_785_;
}
}
}
else
{
uint8_t v___x_794_; 
v___x_794_ = 0;
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9___boxed(lean_object* v_a_795_, lean_object* v___x_796_, lean_object* v_as_797_, lean_object* v_i_798_, lean_object* v_stop_799_){
_start:
{
uint8_t v_a_boxed_800_; uint8_t v___x_13446__boxed_801_; size_t v_i_boxed_802_; size_t v_stop_boxed_803_; uint8_t v_res_804_; lean_object* v_r_805_; 
v_a_boxed_800_ = lean_unbox(v_a_795_);
v___x_13446__boxed_801_ = lean_unbox(v___x_796_);
v_i_boxed_802_ = lean_unbox_usize(v_i_798_);
lean_dec(v_i_798_);
v_stop_boxed_803_ = lean_unbox_usize(v_stop_799_);
lean_dec(v_stop_799_);
v_res_804_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(v_a_boxed_800_, v___x_13446__boxed_801_, v_as_797_, v_i_boxed_802_, v_stop_boxed_803_);
lean_dec_ref(v_as_797_);
v_r_805_ = lean_box(v_res_804_);
return v_r_805_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(uint8_t v___x_806_, lean_object* v_as_807_, uint8_t v_a_808_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_809_ = lean_unsigned_to_nat(0u);
v___x_810_ = lean_array_get_size(v_as_807_);
v___x_811_ = lean_nat_dec_lt(v___x_809_, v___x_810_);
if (v___x_811_ == 0)
{
return v___x_811_;
}
else
{
if (v___x_811_ == 0)
{
return v___x_811_;
}
else
{
size_t v___x_812_; size_t v___x_813_; uint8_t v___x_814_; 
v___x_812_ = ((size_t)0ULL);
v___x_813_ = lean_usize_of_nat(v___x_810_);
v___x_814_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(v_a_808_, v___x_806_, v_as_807_, v___x_812_, v___x_813_);
return v___x_814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___boxed(lean_object* v___x_815_, lean_object* v_as_816_, lean_object* v_a_817_){
_start:
{
uint8_t v___x_13471__boxed_818_; uint8_t v_a_boxed_819_; uint8_t v_res_820_; lean_object* v_r_821_; 
v___x_13471__boxed_818_ = lean_unbox(v___x_815_);
v_a_boxed_819_ = lean_unbox(v_a_817_);
v_res_820_ = l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(v___x_13471__boxed_818_, v_as_816_, v_a_boxed_819_);
lean_dec_ref(v_as_816_);
v_r_821_ = lean_box(v_res_820_);
return v_r_821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0___boxed(lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_c_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0(v_a_824_, v_a_825_, v_c_826_, v___y_827_, v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec_ref(v_a_824_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(lean_object* v_declName_830_, lean_object* v_args_831_, lean_object* v_as_832_, size_t v_sz_833_, size_t v_i_834_, lean_object* v_b_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_a_839_; lean_object* v_a_840_; uint8_t v___x_844_; 
v___x_844_ = lean_usize_dec_lt(v_i_834_, v_sz_833_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; 
lean_dec(v_declName_830_);
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v_b_835_);
lean_ctor_set(v___x_845_, 1, v___y_837_);
return v___x_845_;
}
else
{
lean_object* v_a_846_; lean_object* v_toSignature_847_; lean_object* v_value_848_; lean_object* v_name_849_; lean_object* v_params_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v_a_846_ = lean_array_uget_borrowed(v_as_832_, v_i_834_);
v_toSignature_847_ = lean_ctor_get(v_a_846_, 0);
v_value_848_ = lean_ctor_get(v_a_846_, 1);
v_name_849_ = lean_ctor_get(v_toSignature_847_, 0);
v_params_850_ = lean_ctor_get(v_toSignature_847_, 3);
v___x_851_ = lean_box(0);
v___x_852_ = lean_name_eq(v_declName_830_, v_name_849_);
if (v___x_852_ == 0)
{
v_a_839_ = v___x_851_;
v_a_840_ = v___y_837_;
goto v___jp_838_;
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_853_ = lean_array_get_size(v_params_850_);
v___x_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0));
v___x_856_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v___x_853_, v_args_831_, v___x_854_, v___x_855_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v_a_858_; lean_object* v_visited_859_; lean_object* v_fixed_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v_a_857_ = lean_ctor_get(v___x_856_, 1);
lean_inc(v_a_857_);
v_a_858_ = lean_ctor_get(v___x_856_, 0);
lean_inc_n(v_a_858_, 2);
lean_dec_ref_known(v___x_856_, 2);
v_visited_859_ = lean_ctor_get(v_a_857_, 0);
v_fixed_860_ = lean_ctor_get(v_a_857_, 1);
lean_inc(v_declName_830_);
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v_declName_830_);
lean_ctor_set(v___x_861_, 1, v_a_858_);
v___x_862_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_visited_859_, v___x_861_);
if (v___x_862_ == 0)
{
lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_873_; 
lean_inc_ref(v_fixed_860_);
lean_inc_ref(v_visited_859_);
v_isSharedCheck_873_ = !lean_is_exclusive(v_a_857_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; lean_object* v_unused_875_; 
v_unused_874_ = lean_ctor_get(v_a_857_, 1);
lean_dec(v_unused_874_);
v_unused_875_ = lean_ctor_get(v_a_857_, 0);
lean_dec(v_unused_875_);
v___x_864_ = v_a_857_;
v_isShared_865_ = v_isSharedCheck_873_;
goto v_resetjp_863_;
}
else
{
lean_dec(v_a_857_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_873_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___f_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
lean_inc(v_a_846_);
v___f_866_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0___boxed), 5, 2);
lean_closure_set(v___f_866_, 0, v_a_846_);
lean_closure_set(v___f_866_, 1, v_a_858_);
v___x_867_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(v_visited_859_, v___x_861_, v___x_851_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_867_);
v___x_869_ = v___x_864_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_fixed_860_);
v___x_869_ = v_reuseFailAlloc_872_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; 
lean_inc_ref(v_value_848_);
v___x_870_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v___f_866_, v_value_848_, v___y_836_, v___x_869_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; 
v_a_871_ = lean_ctor_get(v___x_870_, 1);
lean_inc(v_a_871_);
lean_dec_ref_known(v___x_870_, 2);
v_a_839_ = v___x_851_;
v_a_840_ = v_a_871_;
goto v___jp_838_;
}
else
{
lean_dec(v_declName_830_);
return v___x_870_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_861_, 2);
lean_dec(v_a_858_);
v_a_839_ = v___x_851_;
v_a_840_ = v_a_857_;
goto v___jp_838_;
}
}
else
{
lean_object* v_a_876_; lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_dec(v_declName_830_);
v_a_876_ = lean_ctor_get(v___x_856_, 0);
v_a_877_ = lean_ctor_get(v___x_856_, 1);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_856_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_inc(v_a_876_);
lean_dec(v___x_856_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_876_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
v___jp_838_:
{
size_t v___x_841_; size_t v___x_842_; 
v___x_841_ = ((size_t)1ULL);
v___x_842_ = lean_usize_add(v_i_834_, v___x_841_);
v_i_834_ = v___x_842_;
v_b_835_ = v_a_839_;
v___y_837_ = v_a_840_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp(lean_object* v_declName_885_, lean_object* v_args_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v___y_890_; lean_object* v_decls_891_; lean_object* v___y_892_; lean_object* v_main_906_; lean_object* v_toSignature_907_; lean_object* v_decls_908_; lean_object* v_name_909_; lean_object* v_params_910_; uint8_t v___x_911_; 
v_main_906_ = lean_ctor_get(v_a_887_, 1);
v_toSignature_907_ = lean_ctor_get(v_main_906_, 0);
v_decls_908_ = lean_ctor_get(v_a_887_, 0);
v_name_909_ = lean_ctor_get(v_toSignature_907_, 0);
v_params_910_ = lean_ctor_get(v_toSignature_907_, 3);
v___x_911_ = lean_name_eq(v_declName_885_, v_name_909_);
if (v___x_911_ == 0)
{
v___y_890_ = v_a_887_;
v_decls_891_ = v_decls_908_;
v___y_892_ = v_a_888_;
goto v___jp_889_;
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_912_ = lean_array_get_size(v_params_910_);
v___x_913_ = lean_unsigned_to_nat(0u);
v___x_914_ = lean_box(0);
v___x_915_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(v___x_912_, v_args_886_, v___x_913_, v___x_914_, v_a_887_, v_a_888_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_925_; 
v_a_916_ = lean_ctor_get(v___x_915_, 1);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_925_ == 0)
{
lean_object* v_unused_926_; 
v_unused_926_ = lean_ctor_get(v___x_915_, 0);
lean_dec(v_unused_926_);
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_925_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_925_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v_fixed_920_; uint8_t v___x_921_; 
v_fixed_920_ = lean_ctor_get(v_a_916_, 1);
v___x_921_ = l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(v___x_911_, v_fixed_920_, v___x_911_);
if (v___x_921_ == 0)
{
lean_object* v___x_923_; 
lean_dec(v_declName_885_);
if (v_isShared_919_ == 0)
{
lean_ctor_set_tag(v___x_918_, 1);
lean_ctor_set(v___x_918_, 0, v___x_914_);
v___x_923_ = v___x_918_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_a_916_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
else
{
lean_del_object(v___x_918_);
v___y_890_ = v_a_887_;
v_decls_891_ = v_decls_908_;
v___y_892_ = v_a_916_;
goto v___jp_889_;
}
}
}
else
{
lean_dec(v_declName_885_);
return v___x_915_;
}
}
v___jp_889_:
{
lean_object* v___x_893_; size_t v_sz_894_; size_t v___x_895_; lean_object* v___x_896_; 
v___x_893_ = lean_box(0);
v_sz_894_ = lean_array_size(v_decls_891_);
v___x_895_ = ((size_t)0ULL);
v___x_896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(v_declName_885_, v_args_886_, v_decls_891_, v_sz_894_, v___x_895_, v___x_893_, v___y_890_, v___y_892_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
v_a_897_ = lean_ctor_get(v___x_896_, 1);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_904_ == 0)
{
lean_object* v_unused_905_; 
v_unused_905_ = lean_ctor_get(v___x_896_, 0);
lean_dec(v_unused_905_);
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_893_);
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
else
{
return v___x_896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalLetValue(lean_object* v_e_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
if (lean_obj_tag(v_e_927_) == 3)
{
lean_object* v_declName_930_; lean_object* v_args_931_; lean_object* v___x_932_; 
v_declName_930_ = lean_ctor_get(v_e_927_, 0);
lean_inc(v_declName_930_);
v_args_931_ = lean_ctor_get(v_e_927_, 2);
lean_inc_ref(v_args_931_);
lean_dec_ref_known(v_e_927_, 3);
v___x_932_ = l_Lean_Compiler_LCNF_FixedParams_evalApp(v_declName_930_, v_args_931_, v_a_928_, v_a_929_);
lean_dec_ref(v_args_931_);
return v___x_932_;
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec(v_e_927_);
v___x_933_ = lean_box(0);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v_a_929_);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(lean_object* v_as_935_, size_t v_i_936_, size_t v_stop_937_, lean_object* v_b_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___y_942_; uint8_t v___x_949_; 
v___x_949_ = lean_usize_dec_eq(v_i_936_, v_stop_937_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
v___x_950_ = lean_array_uget_borrowed(v_as_935_, v_i_936_);
switch(lean_obj_tag(v___x_950_))
{
case 0:
{
lean_object* v_code_951_; 
v_code_951_ = lean_ctor_get(v___x_950_, 2);
lean_inc_ref(v_code_951_);
v___y_942_ = v_code_951_;
goto v___jp_941_;
}
case 1:
{
lean_object* v_code_952_; 
v_code_952_ = lean_ctor_get(v___x_950_, 1);
lean_inc_ref(v_code_952_);
v___y_942_ = v_code_952_;
goto v___jp_941_;
}
default: 
{
lean_object* v_code_953_; 
v_code_953_ = lean_ctor_get(v___x_950_, 0);
lean_inc_ref(v_code_953_);
v___y_942_ = v_code_953_;
goto v___jp_941_;
}
}
}
else
{
lean_object* v___x_954_; 
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v_b_938_);
lean_ctor_set(v___x_954_, 1, v___y_940_);
return v___x_954_;
}
v___jp_941_:
{
lean_object* v___x_943_; 
lean_inc_ref(v___y_939_);
v___x_943_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v___y_942_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v_a_945_; size_t v___x_946_; size_t v___x_947_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_944_);
v_a_945_ = lean_ctor_get(v___x_943_, 1);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_943_, 2);
v___x_946_ = ((size_t)1ULL);
v___x_947_ = lean_usize_add(v_i_936_, v___x_946_);
v_i_936_ = v___x_947_;
v_b_938_ = v_a_944_;
v___y_940_ = v_a_945_;
goto _start;
}
else
{
return v___x_943_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalCode(lean_object* v_code_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
switch(lean_obj_tag(v_code_955_))
{
case 0:
{
lean_object* v_decl_958_; lean_object* v_k_959_; lean_object* v_value_960_; lean_object* v___x_961_; 
v_decl_958_ = lean_ctor_get(v_code_955_, 0);
lean_inc_ref(v_decl_958_);
v_k_959_ = lean_ctor_get(v_code_955_, 1);
lean_inc_ref(v_k_959_);
lean_dec_ref_known(v_code_955_, 2);
v_value_960_ = lean_ctor_get(v_decl_958_, 3);
lean_inc(v_value_960_);
lean_dec_ref(v_decl_958_);
v___x_961_ = l_Lean_Compiler_LCNF_FixedParams_evalLetValue(v_value_960_, v_a_956_, v_a_957_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; 
v_a_962_ = lean_ctor_get(v___x_961_, 1);
lean_inc(v_a_962_);
lean_dec_ref_known(v___x_961_, 2);
v_code_955_ = v_k_959_;
v_a_957_ = v_a_962_;
goto _start;
}
else
{
lean_dec_ref(v_k_959_);
lean_dec_ref(v_a_956_);
return v___x_961_;
}
}
case 1:
{
lean_object* v_decl_964_; lean_object* v_k_965_; lean_object* v___x_966_; 
v_decl_964_ = lean_ctor_get(v_code_955_, 0);
lean_inc_ref_n(v_decl_964_, 2);
v_k_965_ = lean_ctor_get(v_code_955_, 1);
lean_inc_ref(v_k_965_);
lean_dec_ref_known(v_code_955_, 2);
v___x_966_ = l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(v_decl_964_, v_a_956_, v_a_957_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
if (lean_obj_tag(v_a_967_) == 1)
{
lean_object* v_a_968_; lean_object* v_val_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_983_; 
v_a_968_ = lean_ctor_get(v___x_966_, 1);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_966_, 2);
v_val_969_ = lean_ctor_get(v_a_967_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v_a_967_);
if (v_isSharedCheck_983_ == 0)
{
v___x_971_ = v_a_967_;
v_isShared_972_ = v_isSharedCheck_983_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_val_969_);
lean_dec(v_a_967_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_983_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v_fvarId_973_; lean_object* v_decls_974_; lean_object* v_main_975_; lean_object* v_assignment_976_; lean_object* v___x_978_; 
v_fvarId_973_ = lean_ctor_get(v_decl_964_, 0);
lean_inc(v_fvarId_973_);
lean_dec_ref(v_decl_964_);
v_decls_974_ = lean_ctor_get(v_a_956_, 0);
lean_inc_ref(v_decls_974_);
v_main_975_ = lean_ctor_get(v_a_956_, 1);
lean_inc_ref(v_main_975_);
v_assignment_976_ = lean_ctor_get(v_a_956_, 2);
lean_inc(v_assignment_976_);
lean_dec_ref(v_a_956_);
if (v_isShared_972_ == 0)
{
lean_ctor_set_tag(v___x_971_, 2);
v___x_978_ = v___x_971_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_val_969_);
v___x_978_ = v_reuseFailAlloc_982_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_973_, v___x_978_, v_assignment_976_);
v___x_980_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_980_, 0, v_decls_974_);
lean_ctor_set(v___x_980_, 1, v_main_975_);
lean_ctor_set(v___x_980_, 2, v___x_979_);
v_code_955_ = v_k_965_;
v_a_956_ = v___x_980_;
v_a_957_ = v_a_968_;
goto _start;
}
}
}
else
{
lean_object* v_a_984_; lean_object* v_value_985_; lean_object* v___x_986_; 
lean_dec(v_a_967_);
v_a_984_ = lean_ctor_get(v___x_966_, 1);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_966_, 2);
v_value_985_ = lean_ctor_get(v_decl_964_, 4);
lean_inc_ref(v_value_985_);
lean_dec_ref(v_decl_964_);
lean_inc_ref(v_a_956_);
v___x_986_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_value_985_, v_a_956_, v_a_984_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; 
v_a_987_ = lean_ctor_get(v___x_986_, 1);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 2);
v_code_955_ = v_k_965_;
v_a_957_ = v_a_987_;
goto _start;
}
else
{
lean_dec_ref(v_k_965_);
lean_dec_ref(v_a_956_);
return v___x_986_;
}
}
}
else
{
lean_object* v_a_989_; lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec_ref(v_k_965_);
lean_dec_ref(v_decl_964_);
lean_dec_ref(v_a_956_);
v_a_989_ = lean_ctor_get(v___x_966_, 0);
v_a_990_ = lean_ctor_get(v___x_966_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_966_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_inc(v_a_989_);
lean_dec(v___x_966_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_989_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
case 2:
{
lean_object* v_decl_998_; lean_object* v_k_999_; lean_object* v_value_1000_; lean_object* v___x_1001_; 
v_decl_998_ = lean_ctor_get(v_code_955_, 0);
lean_inc_ref(v_decl_998_);
v_k_999_ = lean_ctor_get(v_code_955_, 1);
lean_inc_ref(v_k_999_);
lean_dec_ref_known(v_code_955_, 2);
v_value_1000_ = lean_ctor_get(v_decl_998_, 4);
lean_inc_ref(v_value_1000_);
lean_dec_ref(v_decl_998_);
lean_inc_ref(v_a_956_);
v___x_1001_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_value_1000_, v_a_956_, v_a_957_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 1);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 2);
v_code_955_ = v_k_999_;
v_a_957_ = v_a_1002_;
goto _start;
}
else
{
lean_dec_ref(v_k_999_);
lean_dec_ref(v_a_956_);
return v___x_1001_;
}
}
case 3:
{
lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v_a_956_);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_code_955_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; lean_object* v_unused_1013_; 
v_unused_1012_ = lean_ctor_get(v_code_955_, 1);
lean_dec(v_unused_1012_);
v_unused_1013_ = lean_ctor_get(v_code_955_, 0);
lean_dec(v_unused_1013_);
v___x_1005_ = v_code_955_;
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
else
{
lean_dec(v_code_955_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1007_ = lean_box(0);
if (v_isShared_1006_ == 0)
{
lean_ctor_set_tag(v___x_1005_, 0);
lean_ctor_set(v___x_1005_, 1, v_a_957_);
lean_ctor_set(v___x_1005_, 0, v___x_1007_);
v___x_1009_ = v___x_1005_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_a_957_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
case 4:
{
lean_object* v_cases_1014_; lean_object* v_alts_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v_cases_1014_ = lean_ctor_get(v_code_955_, 0);
lean_inc_ref(v_cases_1014_);
lean_dec_ref_known(v_code_955_, 1);
v_alts_1015_ = lean_ctor_get(v_cases_1014_, 3);
lean_inc_ref(v_alts_1015_);
lean_dec_ref(v_cases_1014_);
v___x_1016_ = lean_unsigned_to_nat(0u);
v___x_1017_ = lean_array_get_size(v_alts_1015_);
v___x_1018_ = lean_box(0);
v___x_1019_ = lean_nat_dec_lt(v___x_1016_, v___x_1017_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
lean_dec_ref(v_alts_1015_);
lean_dec_ref(v_a_956_);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v_a_957_);
return v___x_1020_;
}
else
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_nat_dec_le(v___x_1017_, v___x_1017_);
if (v___x_1021_ == 0)
{
if (v___x_1019_ == 0)
{
lean_object* v___x_1022_; 
lean_dec_ref(v_alts_1015_);
lean_dec_ref(v_a_956_);
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1018_);
lean_ctor_set(v___x_1022_, 1, v_a_957_);
return v___x_1022_;
}
else
{
size_t v___x_1023_; size_t v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = ((size_t)0ULL);
v___x_1024_ = lean_usize_of_nat(v___x_1017_);
v___x_1025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(v_alts_1015_, v___x_1023_, v___x_1024_, v___x_1018_, v_a_956_, v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec_ref(v_alts_1015_);
return v___x_1025_;
}
}
else
{
size_t v___x_1026_; size_t v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = ((size_t)0ULL);
v___x_1027_ = lean_usize_of_nat(v___x_1017_);
v___x_1028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(v_alts_1015_, v___x_1026_, v___x_1027_, v___x_1018_, v_a_956_, v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec_ref(v_alts_1015_);
return v___x_1028_;
}
}
}
default: 
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_dec_ref(v_a_956_);
lean_dec_ref(v_code_955_);
v___x_1029_ = lean_box(0);
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v_a_957_);
return v___x_1030_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0(lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_c_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_decls_1036_; lean_object* v_main_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_decls_1036_ = lean_ctor_get(v___y_1034_, 0);
v_main_1037_ = lean_ctor_get(v___y_1034_, 1);
v___x_1038_ = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(v_a_1031_, v_a_1032_);
lean_inc_ref(v_main_1037_);
lean_inc_ref(v_decls_1036_);
v___x_1039_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1039_, 0, v_decls_1036_);
lean_ctor_set(v___x_1039_, 1, v_main_1037_);
lean_ctor_set(v___x_1039_, 2, v___x_1038_);
v___x_1040_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_c_1033_, v___x_1039_, v___y_1035_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalLetValue___boxed(lean_object* v_e_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_Compiler_LCNF_FixedParams_evalLetValue(v_e_1041_, v_a_1042_, v_a_1043_);
lean_dec_ref(v_a_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9___boxed(lean_object* v_as_1045_, lean_object* v_i_1046_, lean_object* v_stop_1047_, lean_object* v_b_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
size_t v_i_boxed_1051_; size_t v_stop_boxed_1052_; lean_object* v_res_1053_; 
v_i_boxed_1051_ = lean_unbox_usize(v_i_1046_);
lean_dec(v_i_1046_);
v_stop_boxed_1052_ = lean_unbox_usize(v_stop_1047_);
lean_dec(v_stop_1047_);
v_res_1053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(v_as_1045_, v_i_boxed_1051_, v_stop_boxed_1052_, v_b_1048_, v___y_1049_, v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec_ref(v_as_1045_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp___boxed(lean_object* v_declName_1054_, lean_object* v_args_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Compiler_LCNF_FixedParams_evalApp(v_declName_1054_, v_args_1055_, v_a_1056_, v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec_ref(v_args_1055_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___boxed(lean_object* v_declName_1059_, lean_object* v_args_1060_, lean_object* v_as_1061_, lean_object* v_sz_1062_, lean_object* v_i_1063_, lean_object* v_b_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
size_t v_sz_boxed_1067_; size_t v_i_boxed_1068_; lean_object* v_res_1069_; 
v_sz_boxed_1067_ = lean_unbox_usize(v_sz_1062_);
lean_dec(v_sz_1062_);
v_i_boxed_1068_ = lean_unbox_usize(v_i_1063_);
lean_dec(v_i_1063_);
v_res_1069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(v_declName_1059_, v_args_1060_, v_as_1061_, v_sz_boxed_1067_, v_i_boxed_1068_, v_b_1064_, v___y_1065_, v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec_ref(v_as_1061_);
lean_dec_ref(v_args_1060_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3(uint8_t v_pu_1070_, lean_object* v_f_1071_, lean_object* v_v_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v_f_1071_, v_v_1072_, v___y_1073_, v___y_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___boxed(lean_object* v_pu_1076_, lean_object* v_f_1077_, lean_object* v_v_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
uint8_t v_pu_boxed_1081_; lean_object* v_res_1082_; 
v_pu_boxed_1081_ = lean_unbox(v_pu_1076_);
v_res_1082_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3(v_pu_boxed_1081_, v_f_1077_, v_v_1078_, v___y_1079_, v___y_1080_);
lean_dec_ref(v___y_1079_);
return v_res_1082_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1(lean_object* v_00_u03b2_1083_, lean_object* v_m_1084_, lean_object* v_a_1085_){
_start:
{
uint8_t v___x_1086_; 
v___x_1086_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_m_1084_, v_a_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___boxed(lean_object* v_00_u03b2_1087_, lean_object* v_m_1088_, lean_object* v_a_1089_){
_start:
{
uint8_t v_res_1090_; lean_object* v_r_1091_; 
v_res_1090_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1(v_00_u03b2_1087_, v_m_1088_, v_a_1089_);
lean_dec_ref(v_a_1089_);
lean_dec_ref(v_m_1088_);
v_r_1091_ = lean_box(v_res_1090_);
return v_r_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2(lean_object* v_00_u03b2_1092_, lean_object* v_m_1093_, lean_object* v_a_1094_, lean_object* v_b_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(v_m_1093_, v_a_1094_, v_b_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4(lean_object* v_upperBound_1097_, lean_object* v_args_1098_, lean_object* v_inst_1099_, lean_object* v_R_1100_, lean_object* v_a_1101_, lean_object* v_b_1102_, lean_object* v_c_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v_upperBound_1097_, v_args_1098_, v_a_1101_, v_b_1102_, v___y_1104_, v___y_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___boxed(lean_object* v_upperBound_1107_, lean_object* v_args_1108_, lean_object* v_inst_1109_, lean_object* v_R_1110_, lean_object* v_a_1111_, lean_object* v_b_1112_, lean_object* v_c_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4(v_upperBound_1107_, v_args_1108_, v_inst_1109_, v_R_1110_, v_a_1111_, v_b_1112_, v_c_1113_, v___y_1114_, v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec_ref(v_args_1108_);
lean_dec(v_upperBound_1107_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7(lean_object* v_upperBound_1117_, lean_object* v_args_1118_, lean_object* v_inst_1119_, lean_object* v_R_1120_, lean_object* v_a_1121_, lean_object* v_b_1122_, lean_object* v_c_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(v_upperBound_1117_, v_args_1118_, v_a_1121_, v_b_1122_, v___y_1124_, v___y_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___boxed(lean_object* v_upperBound_1127_, lean_object* v_args_1128_, lean_object* v_inst_1129_, lean_object* v_R_1130_, lean_object* v_a_1131_, lean_object* v_b_1132_, lean_object* v_c_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7(v_upperBound_1127_, v_args_1128_, v_inst_1129_, v_R_1130_, v_a_1131_, v_b_1132_, v_c_1133_, v___y_1134_, v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec_ref(v_args_1128_);
lean_dec(v_upperBound_1127_);
return v_res_1136_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1(lean_object* v_00_u03b2_1137_, lean_object* v_a_1138_, lean_object* v_x_1139_){
_start:
{
uint8_t v___x_1140_; 
v___x_1140_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_1138_, v_x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1141_, lean_object* v_a_1142_, lean_object* v_x_1143_){
_start:
{
uint8_t v_res_1144_; lean_object* v_r_1145_; 
v_res_1144_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1(v_00_u03b2_1141_, v_a_1142_, v_x_1143_);
lean_dec(v_x_1143_);
lean_dec_ref(v_a_1142_);
v_r_1145_ = lean_box(v_res_1144_);
return v_r_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4(lean_object* v_00_u03b2_1146_, lean_object* v_data_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(v_data_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4(lean_object* v_xs_1149_, lean_object* v_ys_1150_, lean_object* v_hsz_1151_, lean_object* v_x_1152_, lean_object* v_x_1153_){
_start:
{
uint8_t v___x_1154_; 
v___x_1154_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(v_xs_1149_, v_ys_1150_, v_x_1152_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___boxed(lean_object* v_xs_1155_, lean_object* v_ys_1156_, lean_object* v_hsz_1157_, lean_object* v_x_1158_, lean_object* v_x_1159_){
_start:
{
uint8_t v_res_1160_; lean_object* v_r_1161_; 
v_res_1160_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4(v_xs_1155_, v_ys_1156_, v_hsz_1157_, v_x_1158_, v_x_1159_);
lean_dec_ref(v_ys_1156_);
lean_dec_ref(v_xs_1155_);
v_r_1161_ = lean_box(v_res_1160_);
return v_r_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_1162_, lean_object* v_i_1163_, lean_object* v_source_1164_, lean_object* v_target_1165_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(v_i_1163_, v_source_1164_, v_target_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14(lean_object* v_00_u03b2_1167_, lean_object* v_x_1168_, lean_object* v_x_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(v_x_1168_, v_x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(lean_object* v_upperBound_1171_, lean_object* v_a_1172_, lean_object* v_b_1173_){
_start:
{
uint8_t v___x_1174_; 
v___x_1174_ = lean_nat_dec_lt(v_a_1172_, v_upperBound_1171_);
if (v___x_1174_ == 0)
{
lean_dec(v_a_1172_);
return v_b_1173_;
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_inc(v_a_1172_);
v___x_1175_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1175_, 0, v_a_1172_);
v___x_1176_ = lean_array_push(v_b_1173_, v___x_1175_);
v___x_1177_ = lean_unsigned_to_nat(1u);
v___x_1178_ = lean_nat_add(v_a_1172_, v___x_1177_);
lean_dec(v_a_1172_);
v_a_1172_ = v___x_1178_;
v_b_1173_ = v___x_1176_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg___boxed(lean_object* v_upperBound_1180_, lean_object* v_a_1181_, lean_object* v_b_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_upperBound_1180_, v_a_1181_, v_b_1182_);
lean_dec(v_upperBound_1180_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(lean_object* v_numParams_1184_){
_start:
{
lean_object* v___x_1185_; lean_object* v_values_1186_; lean_object* v___x_1187_; 
v___x_1185_ = lean_unsigned_to_nat(0u);
v_values_1186_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0));
v___x_1187_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_numParams_1184_, v___x_1185_, v_values_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkInitialValues___boxed(lean_object* v_numParams_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(v_numParams_1188_);
lean_dec(v_numParams_1188_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0(lean_object* v_upperBound_1190_, lean_object* v_inst_1191_, lean_object* v_R_1192_, lean_object* v_a_1193_, lean_object* v_b_1194_, lean_object* v_c_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_upperBound_1190_, v_a_1193_, v_b_1194_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___boxed(lean_object* v_upperBound_1197_, lean_object* v_inst_1198_, lean_object* v_R_1199_, lean_object* v_a_1200_, lean_object* v_b_1201_, lean_object* v_c_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0(v_upperBound_1197_, v_inst_1198_, v_R_1199_, v_a_1200_, v_b_1201_, v_c_1202_);
lean_dec(v_upperBound_1197_);
return v_res_1203_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = lean_box(0);
v___x_1205_ = lean_unsigned_to_nat(16u);
v___x_1206_ = lean_mk_array(v___x_1205_, v___x_1204_);
return v___x_1206_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0);
v___x_1208_ = lean_unsigned_to_nat(0u);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1207_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(lean_object* v_decls_1210_, lean_object* v_as_1211_, size_t v_sz_1212_, size_t v_i_1213_, lean_object* v_b_1214_){
_start:
{
lean_object* v_a_1216_; uint8_t v___x_1220_; 
v___x_1220_ = lean_usize_dec_lt(v_i_1213_, v_sz_1212_);
if (v___x_1220_ == 0)
{
lean_dec_ref(v_decls_1210_);
return v_b_1214_;
}
else
{
lean_object* v_a_1221_; lean_object* v_toSignature_1222_; lean_object* v_value_1223_; lean_object* v_name_1224_; lean_object* v_params_1225_; lean_object* v_s_1227_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v_a_1221_ = lean_array_uget_borrowed(v_as_1211_, v_i_1213_);
v_toSignature_1222_ = lean_ctor_get(v_a_1221_, 0);
v_value_1223_ = lean_ctor_get(v_a_1221_, 1);
v_name_1224_ = lean_ctor_get(v_toSignature_1222_, 0);
v_params_1225_ = lean_ctor_get(v_toSignature_1222_, 3);
v___x_1230_ = lean_array_get_size(v_params_1225_);
v___x_1231_ = l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(v___x_1230_);
v___x_1232_ = lean_box(v___x_1220_);
v___x_1233_ = lean_mk_array(v___x_1230_, v___x_1232_);
if (lean_obj_tag(v_value_1223_) == 0)
{
lean_object* v_code_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_a_1240_; 
v_code_1234_ = lean_ctor_get(v_value_1223_, 0);
v___x_1235_ = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(v_a_1221_, v___x_1231_);
lean_inc(v_a_1221_);
lean_inc_ref(v_decls_1210_);
v___x_1236_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1236_, 0, v_decls_1210_);
lean_ctor_set(v___x_1236_, 1, v_a_1221_);
lean_ctor_set(v___x_1236_, 2, v___x_1235_);
v___x_1237_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1);
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set(v___x_1238_, 1, v___x_1233_);
lean_inc_ref(v_code_1234_);
v___x_1239_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_code_1234_, v___x_1236_, v___x_1238_);
v_a_1240_ = lean_ctor_get(v___x_1239_, 1);
lean_inc(v_a_1240_);
lean_dec_ref(v___x_1239_);
v_s_1227_ = v_a_1240_;
goto v___jp_1226_;
}
else
{
lean_object* v___x_1241_; 
lean_dec_ref(v___x_1231_);
lean_inc(v_name_1224_);
v___x_1241_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1224_, v___x_1233_, v_b_1214_);
v_a_1216_ = v___x_1241_;
goto v___jp_1215_;
}
v___jp_1226_:
{
lean_object* v_fixed_1228_; lean_object* v___x_1229_; 
v_fixed_1228_ = lean_ctor_get(v_s_1227_, 1);
lean_inc_ref(v_fixed_1228_);
lean_dec_ref(v_s_1227_);
lean_inc(v_name_1224_);
v___x_1229_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1224_, v_fixed_1228_, v_b_1214_);
v_a_1216_ = v___x_1229_;
goto v___jp_1215_;
}
}
v___jp_1215_:
{
size_t v___x_1217_; size_t v___x_1218_; 
v___x_1217_ = ((size_t)1ULL);
v___x_1218_ = lean_usize_add(v_i_1213_, v___x_1217_);
v_i_1213_ = v___x_1218_;
v_b_1214_ = v_a_1216_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___boxed(lean_object* v_decls_1242_, lean_object* v_as_1243_, lean_object* v_sz_1244_, lean_object* v_i_1245_, lean_object* v_b_1246_){
_start:
{
size_t v_sz_boxed_1247_; size_t v_i_boxed_1248_; lean_object* v_res_1249_; 
v_sz_boxed_1247_ = lean_unbox_usize(v_sz_1244_);
lean_dec(v_sz_1244_);
v_i_boxed_1248_ = lean_unbox_usize(v_i_1245_);
lean_dec(v_i_1245_);
v_res_1249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(v_decls_1242_, v_as_1243_, v_sz_boxed_1247_, v_i_boxed_1248_, v_b_1246_);
lean_dec_ref(v_as_1243_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFixedParamsMap(lean_object* v_decls_1250_){
_start:
{
lean_object* v_result_1251_; size_t v_sz_1252_; size_t v___x_1253_; lean_object* v___x_1254_; 
v_result_1251_ = lean_box(1);
v_sz_1252_ = lean_array_size(v_decls_1250_);
v___x_1253_ = ((size_t)0ULL);
lean_inc_ref(v_decls_1250_);
v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(v_decls_1250_, v_decls_1250_, v_sz_1252_, v___x_1253_, v_result_1251_);
lean_dec_ref(v_decls_1250_);
return v___x_1254_;
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
