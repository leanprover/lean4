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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalLetValue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalCode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_t_7_);
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
uint8_t v_x_275__boxed_80_; uint8_t v_res_81_; lean_object* v_r_82_; 
v_x_275__boxed_80_ = lean_unbox(v_x_79_);
v_res_81_ = l_Lean_Compiler_LCNF_FixedParams_abort___redArg___lam__0(v_x_275__boxed_80_);
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
lean_dec_ref(v___x_161_);
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
v___x_262_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_256_, v___x_257_, v_fst_241_);
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
lean_dec_ref(v___x_326_);
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
uint8_t v___x_3933__boxed_338_; lean_object* v_res_339_; 
v___x_3933__boxed_338_ = lean_unbox(v___x_333_);
v_res_339_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_331_, v_args_332_, v___x_3933__boxed_338_, v_range_334_, v_b_335_, v_i_336_, v___y_337_);
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
lean_object* v_params_354_; lean_object* v_k_355_; lean_object* v_fvarId_356_; lean_object* v_fvarId_357_; lean_object* v_args_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_424_; 
v_params_354_ = lean_ctor_get(v_decl_340_, 2);
lean_inc_ref(v_params_354_);
lean_dec_ref(v_decl_340_);
v_k_355_ = lean_ctor_get(v_value_351_, 1);
lean_inc_ref(v_k_355_);
lean_dec_ref(v_value_351_);
v_fvarId_356_ = lean_ctor_get(v_decl_352_, 0);
lean_inc(v_fvarId_356_);
lean_dec_ref(v_decl_352_);
v_fvarId_357_ = lean_ctor_get(v_value_353_, 0);
v_args_358_ = lean_ctor_get(v_value_353_, 1);
v_isSharedCheck_424_ = !lean_is_exclusive(v_value_353_);
if (v_isSharedCheck_424_ == 0)
{
v___x_360_ = v_value_353_;
v_isShared_361_ = v_isSharedCheck_424_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_args_358_);
lean_inc(v_fvarId_357_);
lean_dec(v_value_353_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_424_;
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
lean_dec_ref(v_a_341_);
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
lean_dec_ref(v_k_355_);
v___x_370_ = l_Lean_instBEqFVarId_beq(v_fvarId_369_, v_fvarId_356_);
lean_dec(v_fvarId_356_);
lean_dec(v_fvarId_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_373_; 
lean_dec_ref(v_args_358_);
lean_dec(v_fvarId_357_);
lean_dec_ref(v_params_354_);
lean_dec_ref(v_a_341_);
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
lean_object* v_assignment_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_417_; 
lean_del_object(v___x_360_);
v_assignment_375_ = lean_ctor_get(v_a_341_, 2);
v_isSharedCheck_417_ = !lean_is_exclusive(v_a_341_);
if (v_isSharedCheck_417_ == 0)
{
lean_object* v_unused_418_; lean_object* v_unused_419_; 
v_unused_418_ = lean_ctor_get(v_a_341_, 1);
lean_dec(v_unused_418_);
v_unused_419_ = lean_ctor_get(v_a_341_, 0);
lean_dec(v_unused_419_);
v___x_377_ = v_a_341_;
v_isShared_378_ = v_isSharedCheck_417_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_assignment_375_);
lean_dec(v_a_341_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_417_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; 
v___x_379_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(v_assignment_375_, v_fvarId_357_);
lean_dec(v_fvarId_357_);
lean_dec(v_assignment_375_);
if (lean_obj_tag(v___x_379_) == 1)
{
lean_object* v_val_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_416_; 
v_val_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_416_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_416_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_val_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_416_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
if (lean_obj_tag(v_val_380_) == 2)
{
lean_object* v_i_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v_i_384_ = lean_ctor_get(v_val_380_, 0);
lean_inc(v_i_384_);
lean_dec_ref(v_val_380_);
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = lean_unsigned_to_nat(1u);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 2, v___x_386_);
lean_ctor_set(v___x_377_, 1, v___x_363_);
lean_ctor_set(v___x_377_, 0, v___x_385_);
v___x_388_ = v___x_377_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_415_, 2, v___x_386_);
v___x_388_ = v_reuseFailAlloc_415_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v_a_391_; lean_object* v_fst_392_; 
v___x_389_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__0));
v___x_390_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_354_, v_args_358_, v___x_370_, v___x_388_, v___x_389_, v___x_385_, v_a_342_);
lean_dec_ref(v___x_388_);
lean_dec_ref(v_args_358_);
lean_dec_ref(v_params_354_);
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
v_fst_392_ = lean_ctor_get(v_a_391_, 0);
lean_inc(v_fst_392_);
lean_dec(v_a_391_);
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
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v_i_384_);
v___x_398_ = v___x_382_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_i_384_);
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
lean_dec(v_i_384_);
lean_del_object(v___x_382_);
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
lean_dec_ref(v_fst_392_);
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
}
else
{
lean_del_object(v___x_382_);
lean_dec(v_val_380_);
lean_del_object(v___x_377_);
lean_dec_ref(v_args_358_);
lean_dec_ref(v_params_354_);
v___y_348_ = v_a_342_;
goto v___jp_347_;
}
}
}
else
{
lean_dec(v___x_379_);
lean_del_object(v___x_377_);
lean_dec_ref(v_args_358_);
lean_dec_ref(v_params_354_);
v___y_348_ = v_a_342_;
goto v___jp_347_;
}
}
}
}
else
{
lean_object* v___x_420_; lean_object* v___x_422_; 
lean_dec_ref(v_args_358_);
lean_dec(v_fvarId_357_);
lean_dec(v_fvarId_356_);
lean_dec_ref(v_k_355_);
lean_dec_ref(v_params_354_);
lean_dec_ref(v_a_341_);
v___x_420_ = lean_box(0);
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 0);
lean_ctor_set(v___x_360_, 1, v_a_342_);
lean_ctor_set(v___x_360_, 0, v___x_420_);
v___x_422_ = v___x_360_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_a_342_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
}
else
{
lean_dec(v_value_353_);
lean_dec_ref(v_decl_352_);
lean_dec_ref(v_value_351_);
lean_dec_ref(v_a_341_);
lean_dec_ref(v_decl_340_);
v___y_344_ = v_a_342_;
goto v___jp_343_;
}
}
else
{
lean_dec_ref(v_value_351_);
lean_dec_ref(v_a_341_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0(lean_object* v_params_425_, lean_object* v_args_426_, uint8_t v___x_427_, lean_object* v_range_428_, lean_object* v_b_429_, lean_object* v_i_430_, lean_object* v_hs_431_, lean_object* v_hl_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_425_, v_args_426_, v___x_427_, v_range_428_, v_b_429_, v_i_430_, v___y_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___boxed(lean_object* v_params_436_, lean_object* v_args_437_, lean_object* v___x_438_, lean_object* v_range_439_, lean_object* v_b_440_, lean_object* v_i_441_, lean_object* v_hs_442_, lean_object* v_hl_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
uint8_t v___x_4154__boxed_446_; lean_object* v_res_447_; 
v___x_4154__boxed_446_ = lean_unbox(v___x_438_);
v_res_447_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0(v_params_436_, v_args_437_, v___x_4154__boxed_446_, v_range_439_, v_b_440_, v_i_441_, v_hs_442_, v_hl_443_, v___y_444_, v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec_ref(v_range_439_);
lean_dec_ref(v_args_437_);
lean_dec_ref(v_params_436_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(lean_object* v_upperBound_448_, lean_object* v_args_449_, lean_object* v_a_450_, lean_object* v_b_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_a_455_; lean_object* v_a_456_; uint8_t v___x_460_; 
v___x_460_ = lean_nat_dec_lt(v_a_450_, v_upperBound_448_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; 
lean_dec(v_a_450_);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v_b_451_);
lean_ctor_set(v___x_461_, 1, v___y_453_);
return v___x_461_;
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_462_ = lean_box(0);
v___x_463_ = lean_array_get_size(v_args_449_);
v___x_464_ = lean_nat_dec_lt(v_a_450_, v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v_visited_465_; lean_object* v_fixed_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_475_; 
v_visited_465_ = lean_ctor_get(v___y_453_, 0);
v_fixed_466_ = lean_ctor_get(v___y_453_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v___y_453_);
if (v_isSharedCheck_475_ == 0)
{
v___x_468_ = v___y_453_;
v_isShared_469_ = v_isSharedCheck_475_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_fixed_466_);
lean_inc(v_visited_465_);
lean_dec(v___y_453_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_475_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_470_ = lean_box(v___x_464_);
v___x_471_ = lean_array_set(v_fixed_466_, v_a_450_, v___x_470_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v___x_471_);
v___x_473_ = v___x_468_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_visited_465_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
v_a_455_ = v___x_462_;
v_a_456_ = v___x_473_;
goto v___jp_454_;
}
}
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_array_fget_borrowed(v_args_449_, v_a_450_);
v___x_477_ = l_Lean_Compiler_LCNF_FixedParams_evalArg(v___x_476_, v___y_452_, v___y_453_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v_a_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_478_);
v_a_479_ = lean_ctor_get(v___x_477_, 1);
lean_inc(v_a_479_);
lean_dec_ref(v___x_477_);
lean_inc(v_a_450_);
v___x_480_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_480_, 0, v_a_450_);
v___x_481_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v_a_478_, v___x_480_);
lean_dec_ref(v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = lean_box(1);
v___x_483_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v_a_478_, v___x_482_);
lean_dec(v_a_478_);
if (v___x_483_ == 0)
{
lean_object* v_visited_484_; lean_object* v_fixed_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_494_; 
v_visited_484_ = lean_ctor_get(v_a_479_, 0);
v_fixed_485_ = lean_ctor_get(v_a_479_, 1);
v_isSharedCheck_494_ = !lean_is_exclusive(v_a_479_);
if (v_isSharedCheck_494_ == 0)
{
v___x_487_ = v_a_479_;
v_isShared_488_ = v_isSharedCheck_494_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_fixed_485_);
lean_inc(v_visited_484_);
lean_dec(v_a_479_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_494_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_489_ = lean_box(v___x_483_);
v___x_490_ = lean_array_set(v_fixed_485_, v_a_450_, v___x_489_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v___x_490_);
v___x_492_ = v___x_487_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_visited_484_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
v_a_455_ = v___x_462_;
v_a_456_ = v___x_492_;
goto v___jp_454_;
}
}
}
else
{
v_a_455_ = v___x_462_;
v_a_456_ = v_a_479_;
goto v___jp_454_;
}
}
else
{
lean_dec(v_a_478_);
v_a_455_ = v___x_462_;
v_a_456_ = v_a_479_;
goto v___jp_454_;
}
}
else
{
lean_object* v_a_495_; lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec(v_a_450_);
v_a_495_ = lean_ctor_get(v___x_477_, 0);
v_a_496_ = lean_ctor_get(v___x_477_, 1);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_477_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_inc(v_a_495_);
lean_dec(v___x_477_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_495_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
v___jp_454_:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_add(v_a_450_, v___x_457_);
lean_dec(v_a_450_);
v_a_450_ = v___x_458_;
v_b_451_ = v_a_455_;
v___y_453_ = v_a_456_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg___boxed(lean_object* v_upperBound_504_, lean_object* v_args_505_, lean_object* v_a_506_, lean_object* v_b_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(v_upperBound_504_, v_args_505_, v_a_506_, v_b_507_, v___y_508_, v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec_ref(v_args_505_);
lean_dec(v_upperBound_504_);
return v_res_510_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(lean_object* v_xs_511_, lean_object* v_ys_512_, lean_object* v_x_513_){
_start:
{
lean_object* v_zero_514_; uint8_t v_isZero_515_; 
v_zero_514_ = lean_unsigned_to_nat(0u);
v_isZero_515_ = lean_nat_dec_eq(v_x_513_, v_zero_514_);
if (v_isZero_515_ == 1)
{
lean_dec(v_x_513_);
return v_isZero_515_;
}
else
{
lean_object* v_one_516_; lean_object* v_n_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v_one_516_ = lean_unsigned_to_nat(1u);
v_n_517_ = lean_nat_sub(v_x_513_, v_one_516_);
lean_dec(v_x_513_);
v___x_518_ = lean_array_fget_borrowed(v_xs_511_, v_n_517_);
v___x_519_ = lean_array_fget_borrowed(v_ys_512_, v_n_517_);
v___x_520_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v___x_518_, v___x_519_);
if (v___x_520_ == 0)
{
lean_dec(v_n_517_);
return v___x_520_;
}
else
{
v_x_513_ = v_n_517_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_xs_522_, lean_object* v_ys_523_, lean_object* v_x_524_){
_start:
{
uint8_t v_res_525_; lean_object* v_r_526_; 
v_res_525_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(v_xs_522_, v_ys_523_, v_x_524_);
lean_dec_ref(v_ys_523_);
lean_dec_ref(v_xs_522_);
v_r_526_ = lean_box(v_res_525_);
return v_r_526_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(lean_object* v_a_527_, lean_object* v_x_528_){
_start:
{
if (lean_obj_tag(v_x_528_) == 0)
{
uint8_t v___x_529_; 
v___x_529_ = 0;
return v___x_529_;
}
else
{
lean_object* v_key_530_; lean_object* v_tail_531_; uint8_t v___y_533_; lean_object* v_fst_535_; lean_object* v_snd_536_; lean_object* v_fst_537_; lean_object* v_snd_538_; uint8_t v___x_539_; 
v_key_530_ = lean_ctor_get(v_x_528_, 0);
v_tail_531_ = lean_ctor_get(v_x_528_, 2);
v_fst_535_ = lean_ctor_get(v_key_530_, 0);
v_snd_536_ = lean_ctor_get(v_key_530_, 1);
v_fst_537_ = lean_ctor_get(v_a_527_, 0);
v_snd_538_ = lean_ctor_get(v_a_527_, 1);
v___x_539_ = lean_name_eq(v_fst_535_, v_fst_537_);
if (v___x_539_ == 0)
{
v___y_533_ = v___x_539_;
goto v___jp_532_;
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_540_ = lean_array_get_size(v_snd_536_);
v___x_541_ = lean_array_get_size(v_snd_538_);
v___x_542_ = lean_nat_dec_eq(v___x_540_, v___x_541_);
if (v___x_542_ == 0)
{
v_x_528_ = v_tail_531_;
goto _start;
}
else
{
uint8_t v___x_544_; 
v___x_544_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(v_snd_536_, v_snd_538_, v___x_540_);
v___y_533_ = v___x_544_;
goto v___jp_532_;
}
}
v___jp_532_:
{
if (v___y_533_ == 0)
{
v_x_528_ = v_tail_531_;
goto _start;
}
else
{
return v___y_533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg___boxed(lean_object* v_a_545_, lean_object* v_x_546_){
_start:
{
uint8_t v_res_547_; lean_object* v_r_548_; 
v_res_547_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_545_, v_x_546_);
lean_dec(v_x_546_);
lean_dec_ref(v_a_545_);
v_r_548_ = lean_box(v_res_547_);
return v_r_548_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(lean_object* v_as_549_, size_t v_i_550_, size_t v_stop_551_, uint64_t v_b_552_){
_start:
{
uint8_t v___x_553_; 
v___x_553_ = lean_usize_dec_eq(v_i_550_, v_stop_551_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; uint64_t v___x_555_; uint64_t v___x_556_; size_t v___x_557_; size_t v___x_558_; 
v___x_554_ = lean_array_uget_borrowed(v_as_549_, v_i_550_);
v___x_555_ = l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash(v___x_554_);
v___x_556_ = lean_uint64_mix_hash(v_b_552_, v___x_555_);
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_add(v_i_550_, v___x_557_);
v_i_550_ = v___x_558_;
v_b_552_ = v___x_556_;
goto _start;
}
else
{
return v_b_552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2___boxed(lean_object* v_as_560_, lean_object* v_i_561_, lean_object* v_stop_562_, lean_object* v_b_563_){
_start:
{
size_t v_i_boxed_564_; size_t v_stop_boxed_565_; uint64_t v_b_boxed_566_; uint64_t v_res_567_; lean_object* v_r_568_; 
v_i_boxed_564_ = lean_unbox_usize(v_i_561_);
lean_dec(v_i_561_);
v_stop_boxed_565_ = lean_unbox_usize(v_stop_562_);
lean_dec(v_stop_562_);
v_b_boxed_566_ = lean_unbox_uint64(v_b_563_);
lean_dec_ref(v_b_563_);
v_res_567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_as_560_, v_i_boxed_564_, v_stop_boxed_565_, v_b_boxed_566_);
lean_dec_ref(v_as_560_);
v_r_568_ = lean_box_uint64(v_res_567_);
return v_r_568_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_569_; uint64_t v___x_570_; 
v___x_569_ = lean_unsigned_to_nat(1723u);
v___x_570_ = lean_uint64_of_nat(v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
if (lean_obj_tag(v_x_572_) == 0)
{
return v_x_571_;
}
else
{
lean_object* v_key_573_; lean_object* v_value_574_; lean_object* v_tail_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_618_; 
v_key_573_ = lean_ctor_get(v_x_572_, 0);
v_value_574_ = lean_ctor_get(v_x_572_, 1);
v_tail_575_ = lean_ctor_get(v_x_572_, 2);
v_isSharedCheck_618_ = !lean_is_exclusive(v_x_572_);
if (v_isSharedCheck_618_ == 0)
{
v___x_577_ = v_x_572_;
v_isShared_578_ = v_isSharedCheck_618_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_tail_575_);
lean_inc(v_value_574_);
lean_inc(v_key_573_);
lean_dec(v_x_572_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_618_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v_fst_579_; lean_object* v_snd_580_; lean_object* v___x_581_; uint64_t v___y_583_; uint64_t v___y_584_; uint64_t v___y_604_; 
v_fst_579_ = lean_ctor_get(v_key_573_, 0);
v_snd_580_ = lean_ctor_get(v_key_573_, 1);
v___x_581_ = lean_array_get_size(v_x_571_);
if (lean_obj_tag(v_fst_579_) == 0)
{
uint64_t v___x_616_; 
v___x_616_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0);
v___y_604_ = v___x_616_;
goto v___jp_603_;
}
else
{
uint64_t v_hash_617_; 
v_hash_617_ = lean_ctor_get_uint64(v_fst_579_, sizeof(void*)*2);
v___y_604_ = v_hash_617_;
goto v___jp_603_;
}
v___jp_582_:
{
uint64_t v___x_585_; uint64_t v___x_586_; uint64_t v___x_587_; uint64_t v_fold_588_; uint64_t v___x_589_; uint64_t v___x_590_; uint64_t v___x_591_; size_t v___x_592_; size_t v___x_593_; size_t v___x_594_; size_t v___x_595_; size_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_585_ = lean_uint64_mix_hash(v___y_583_, v___y_584_);
v___x_586_ = 32ULL;
v___x_587_ = lean_uint64_shift_right(v___x_585_, v___x_586_);
v_fold_588_ = lean_uint64_xor(v___x_585_, v___x_587_);
v___x_589_ = 16ULL;
v___x_590_ = lean_uint64_shift_right(v_fold_588_, v___x_589_);
v___x_591_ = lean_uint64_xor(v_fold_588_, v___x_590_);
v___x_592_ = lean_uint64_to_usize(v___x_591_);
v___x_593_ = lean_usize_of_nat(v___x_581_);
v___x_594_ = ((size_t)1ULL);
v___x_595_ = lean_usize_sub(v___x_593_, v___x_594_);
v___x_596_ = lean_usize_land(v___x_592_, v___x_595_);
v___x_597_ = lean_array_uget_borrowed(v_x_571_, v___x_596_);
lean_inc(v___x_597_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 2, v___x_597_);
v___x_599_ = v___x_577_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_key_573_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_value_574_);
lean_ctor_set(v_reuseFailAlloc_602_, 2, v___x_597_);
v___x_599_ = v_reuseFailAlloc_602_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; 
v___x_600_ = lean_array_uset(v_x_571_, v___x_596_, v___x_599_);
v_x_571_ = v___x_600_;
v_x_572_ = v_tail_575_;
goto _start;
}
}
v___jp_603_:
{
uint64_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_605_ = 7ULL;
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = lean_array_get_size(v_snd_580_);
v___x_608_ = lean_nat_dec_lt(v___x_606_, v___x_607_);
if (v___x_608_ == 0)
{
v___y_583_ = v___y_604_;
v___y_584_ = v___x_605_;
goto v___jp_582_;
}
else
{
uint8_t v___x_609_; 
v___x_609_ = lean_nat_dec_le(v___x_607_, v___x_607_);
if (v___x_609_ == 0)
{
if (v___x_608_ == 0)
{
v___y_583_ = v___y_604_;
v___y_584_ = v___x_605_;
goto v___jp_582_;
}
else
{
size_t v___x_610_; size_t v___x_611_; uint64_t v___x_612_; 
v___x_610_ = ((size_t)0ULL);
v___x_611_ = lean_usize_of_nat(v___x_607_);
v___x_612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_580_, v___x_610_, v___x_611_, v___x_605_);
v___y_583_ = v___y_604_;
v___y_584_ = v___x_612_;
goto v___jp_582_;
}
}
else
{
size_t v___x_613_; size_t v___x_614_; uint64_t v___x_615_; 
v___x_613_ = ((size_t)0ULL);
v___x_614_ = lean_usize_of_nat(v___x_607_);
v___x_615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_580_, v___x_613_, v___x_614_, v___x_605_);
v___y_583_ = v___y_604_;
v___y_584_ = v___x_615_;
goto v___jp_582_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(lean_object* v_i_619_, lean_object* v_source_620_, lean_object* v_target_621_){
_start:
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_array_get_size(v_source_620_);
v___x_623_ = lean_nat_dec_lt(v_i_619_, v___x_622_);
if (v___x_623_ == 0)
{
lean_dec_ref(v_source_620_);
lean_dec(v_i_619_);
return v_target_621_;
}
else
{
lean_object* v_es_624_; lean_object* v___x_625_; lean_object* v_source_626_; lean_object* v_target_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_es_624_ = lean_array_fget(v_source_620_, v_i_619_);
v___x_625_ = lean_box(0);
v_source_626_ = lean_array_fset(v_source_620_, v_i_619_, v___x_625_);
v_target_627_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(v_target_621_, v_es_624_);
v___x_628_ = lean_unsigned_to_nat(1u);
v___x_629_ = lean_nat_add(v_i_619_, v___x_628_);
lean_dec(v_i_619_);
v_i_619_ = v___x_629_;
v_source_620_ = v_source_626_;
v_target_621_ = v_target_627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(lean_object* v_data_631_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_nbuckets_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_632_ = lean_array_get_size(v_data_631_);
v___x_633_ = lean_unsigned_to_nat(2u);
v_nbuckets_634_ = lean_nat_mul(v___x_632_, v___x_633_);
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_box(0);
v___x_637_ = lean_mk_array(v_nbuckets_634_, v___x_636_);
v___x_638_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(v___x_635_, v_data_631_, v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(lean_object* v_m_639_, lean_object* v_a_640_, lean_object* v_b_641_){
_start:
{
lean_object* v_size_642_; lean_object* v_buckets_643_; lean_object* v_fst_644_; lean_object* v_snd_645_; lean_object* v___x_646_; uint64_t v___y_648_; uint64_t v___y_649_; uint64_t v___y_688_; 
v_size_642_ = lean_ctor_get(v_m_639_, 0);
v_buckets_643_ = lean_ctor_get(v_m_639_, 1);
v_fst_644_ = lean_ctor_get(v_a_640_, 0);
v_snd_645_ = lean_ctor_get(v_a_640_, 1);
v___x_646_ = lean_array_get_size(v_buckets_643_);
if (lean_obj_tag(v_fst_644_) == 0)
{
uint64_t v___x_700_; 
v___x_700_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0);
v___y_688_ = v___x_700_;
goto v___jp_687_;
}
else
{
uint64_t v_hash_701_; 
v_hash_701_ = lean_ctor_get_uint64(v_fst_644_, sizeof(void*)*2);
v___y_688_ = v_hash_701_;
goto v___jp_687_;
}
v___jp_647_:
{
uint64_t v___x_650_; uint64_t v___x_651_; uint64_t v___x_652_; uint64_t v_fold_653_; uint64_t v___x_654_; uint64_t v___x_655_; uint64_t v___x_656_; size_t v___x_657_; size_t v___x_658_; size_t v___x_659_; size_t v___x_660_; size_t v___x_661_; lean_object* v_bkt_662_; uint8_t v___x_663_; 
v___x_650_ = lean_uint64_mix_hash(v___y_648_, v___y_649_);
v___x_651_ = 32ULL;
v___x_652_ = lean_uint64_shift_right(v___x_650_, v___x_651_);
v_fold_653_ = lean_uint64_xor(v___x_650_, v___x_652_);
v___x_654_ = 16ULL;
v___x_655_ = lean_uint64_shift_right(v_fold_653_, v___x_654_);
v___x_656_ = lean_uint64_xor(v_fold_653_, v___x_655_);
v___x_657_ = lean_uint64_to_usize(v___x_656_);
v___x_658_ = lean_usize_of_nat(v___x_646_);
v___x_659_ = ((size_t)1ULL);
v___x_660_ = lean_usize_sub(v___x_658_, v___x_659_);
v___x_661_ = lean_usize_land(v___x_657_, v___x_660_);
v_bkt_662_ = lean_array_uget_borrowed(v_buckets_643_, v___x_661_);
v___x_663_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_640_, v_bkt_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_684_; 
lean_inc_ref(v_buckets_643_);
lean_inc(v_size_642_);
v_isSharedCheck_684_ = !lean_is_exclusive(v_m_639_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; lean_object* v_unused_686_; 
v_unused_685_ = lean_ctor_get(v_m_639_, 1);
lean_dec(v_unused_685_);
v_unused_686_ = lean_ctor_get(v_m_639_, 0);
lean_dec(v_unused_686_);
v___x_665_ = v_m_639_;
v_isShared_666_ = v_isSharedCheck_684_;
goto v_resetjp_664_;
}
else
{
lean_dec(v_m_639_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_684_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v_size_x27_668_; lean_object* v___x_669_; lean_object* v_buckets_x27_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_667_ = lean_unsigned_to_nat(1u);
v_size_x27_668_ = lean_nat_add(v_size_642_, v___x_667_);
lean_dec(v_size_642_);
lean_inc(v_bkt_662_);
v___x_669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_669_, 0, v_a_640_);
lean_ctor_set(v___x_669_, 1, v_b_641_);
lean_ctor_set(v___x_669_, 2, v_bkt_662_);
v_buckets_x27_670_ = lean_array_uset(v_buckets_643_, v___x_661_, v___x_669_);
v___x_671_ = lean_unsigned_to_nat(4u);
v___x_672_ = lean_nat_mul(v_size_x27_668_, v___x_671_);
v___x_673_ = lean_unsigned_to_nat(3u);
v___x_674_ = lean_nat_div(v___x_672_, v___x_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_array_get_size(v_buckets_x27_670_);
v___x_676_ = lean_nat_dec_le(v___x_674_, v___x_675_);
lean_dec(v___x_674_);
if (v___x_676_ == 0)
{
lean_object* v_val_677_; lean_object* v___x_679_; 
v_val_677_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(v_buckets_x27_670_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v_val_677_);
lean_ctor_set(v___x_665_, 0, v_size_x27_668_);
v___x_679_ = v___x_665_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_size_x27_668_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_val_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
else
{
lean_object* v___x_682_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v_buckets_x27_670_);
lean_ctor_set(v___x_665_, 0, v_size_x27_668_);
v___x_682_ = v___x_665_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_size_x27_668_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_buckets_x27_670_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
else
{
lean_dec(v_b_641_);
lean_dec_ref(v_a_640_);
return v_m_639_;
}
}
v___jp_687_:
{
uint64_t v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_689_ = 7ULL;
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_array_get_size(v_snd_645_);
v___x_692_ = lean_nat_dec_lt(v___x_690_, v___x_691_);
if (v___x_692_ == 0)
{
v___y_648_ = v___y_688_;
v___y_649_ = v___x_689_;
goto v___jp_647_;
}
else
{
uint8_t v___x_693_; 
v___x_693_ = lean_nat_dec_le(v___x_691_, v___x_691_);
if (v___x_693_ == 0)
{
if (v___x_692_ == 0)
{
v___y_648_ = v___y_688_;
v___y_649_ = v___x_689_;
goto v___jp_647_;
}
else
{
size_t v___x_694_; size_t v___x_695_; uint64_t v___x_696_; 
v___x_694_ = ((size_t)0ULL);
v___x_695_ = lean_usize_of_nat(v___x_691_);
v___x_696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_645_, v___x_694_, v___x_695_, v___x_689_);
v___y_648_ = v___y_688_;
v___y_649_ = v___x_696_;
goto v___jp_647_;
}
}
else
{
size_t v___x_697_; size_t v___x_698_; uint64_t v___x_699_; 
v___x_697_ = ((size_t)0ULL);
v___x_698_ = lean_usize_of_nat(v___x_691_);
v___x_699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_645_, v___x_697_, v___x_698_, v___x_689_);
v___y_648_ = v___y_688_;
v___y_649_ = v___x_699_;
goto v___jp_647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(lean_object* v_f_702_, lean_object* v_v_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
if (lean_obj_tag(v_v_703_) == 0)
{
lean_object* v_code_706_; lean_object* v___x_707_; 
v_code_706_ = lean_ctor_get(v_v_703_, 0);
lean_inc_ref(v_code_706_);
lean_dec_ref(v_v_703_);
v___x_707_ = lean_apply_3(v_f_702_, v_code_706_, v___y_704_, v___y_705_);
return v___x_707_;
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; 
lean_dec_ref(v_v_703_);
lean_dec_ref(v___y_704_);
lean_dec_ref(v_f_702_);
v___x_708_ = lean_box(0);
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___y_705_);
return v___x_709_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(lean_object* v_m_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_buckets_712_; lean_object* v_fst_713_; lean_object* v_snd_714_; lean_object* v___x_715_; uint64_t v___y_717_; uint64_t v___y_718_; uint64_t v___y_734_; 
v_buckets_712_ = lean_ctor_get(v_m_710_, 1);
v_fst_713_ = lean_ctor_get(v_a_711_, 0);
v_snd_714_ = lean_ctor_get(v_a_711_, 1);
v___x_715_ = lean_array_get_size(v_buckets_712_);
if (lean_obj_tag(v_fst_713_) == 0)
{
uint64_t v___x_746_; 
v___x_746_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0);
v___y_734_ = v___x_746_;
goto v___jp_733_;
}
else
{
uint64_t v_hash_747_; 
v_hash_747_ = lean_ctor_get_uint64(v_fst_713_, sizeof(void*)*2);
v___y_734_ = v_hash_747_;
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
uint8_t v___x_739_; 
v___x_739_ = lean_nat_dec_le(v___x_737_, v___x_737_);
if (v___x_739_ == 0)
{
if (v___x_738_ == 0)
{
v___y_717_ = v___y_734_;
v___y_718_ = v___x_735_;
goto v___jp_716_;
}
else
{
size_t v___x_740_; size_t v___x_741_; uint64_t v___x_742_; 
v___x_740_ = ((size_t)0ULL);
v___x_741_ = lean_usize_of_nat(v___x_737_);
v___x_742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_714_, v___x_740_, v___x_741_, v___x_735_);
v___y_717_ = v___y_734_;
v___y_718_ = v___x_742_;
goto v___jp_716_;
}
}
else
{
size_t v___x_743_; size_t v___x_744_; uint64_t v___x_745_; 
v___x_743_ = ((size_t)0ULL);
v___x_744_ = lean_usize_of_nat(v___x_737_);
v___x_745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_714_, v___x_743_, v___x_744_, v___x_735_);
v___y_717_ = v___y_734_;
v___y_718_ = v___x_745_;
goto v___jp_716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg___boxed(lean_object* v_m_748_, lean_object* v_a_749_){
_start:
{
uint8_t v_res_750_; lean_object* v_r_751_; 
v_res_750_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_m_748_, v_a_749_);
lean_dec_ref(v_a_749_);
lean_dec_ref(v_m_748_);
v_r_751_ = lean_box(v_res_750_);
return v_r_751_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(lean_object* v_upperBound_752_, lean_object* v_args_753_, lean_object* v_a_754_, lean_object* v_b_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_a_759_; lean_object* v_a_760_; uint8_t v___x_764_; 
v___x_764_ = lean_nat_dec_lt(v_a_754_, v_upperBound_752_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; 
lean_dec(v_a_754_);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v_b_755_);
lean_ctor_set(v___x_765_, 1, v___y_757_);
return v___x_765_;
}
else
{
lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_766_ = lean_array_get_size(v_args_753_);
v___x_767_ = lean_nat_dec_lt(v_a_754_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_box(0);
v___x_769_ = lean_array_push(v_b_755_, v___x_768_);
v_a_759_ = v___x_769_;
v_a_760_ = v___y_757_;
goto v___jp_758_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_array_fget_borrowed(v_args_753_, v_a_754_);
v___x_771_ = l_Lean_Compiler_LCNF_FixedParams_evalArg(v___x_770_, v___y_756_, v___y_757_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v_a_773_; lean_object* v___x_774_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
v_a_773_ = lean_ctor_get(v___x_771_, 1);
lean_inc(v_a_773_);
lean_dec_ref(v___x_771_);
v___x_774_ = lean_array_push(v_b_755_, v_a_772_);
v_a_759_ = v___x_774_;
v_a_760_ = v_a_773_;
goto v___jp_758_;
}
else
{
lean_object* v_a_775_; lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec_ref(v_b_755_);
lean_dec(v_a_754_);
v_a_775_ = lean_ctor_get(v___x_771_, 0);
v_a_776_ = lean_ctor_get(v___x_771_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_771_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_inc(v_a_775_);
lean_dec(v___x_771_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_775_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
v___jp_758_:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_unsigned_to_nat(1u);
v___x_762_ = lean_nat_add(v_a_754_, v___x_761_);
lean_dec(v_a_754_);
v_a_754_ = v___x_762_;
v_b_755_ = v_a_759_;
v___y_757_ = v_a_760_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg___boxed(lean_object* v_upperBound_784_, lean_object* v_args_785_, lean_object* v_a_786_, lean_object* v_b_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v_upperBound_784_, v_args_785_, v_a_786_, v_b_787_, v___y_788_, v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec_ref(v_args_785_);
lean_dec(v_upperBound_784_);
return v_res_790_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(uint8_t v_a_791_, lean_object* v_as_792_, size_t v_i_793_, size_t v_stop_794_){
_start:
{
uint8_t v___x_799_; 
v___x_799_ = lean_usize_dec_eq(v_i_793_, v_stop_794_);
if (v___x_799_ == 0)
{
uint8_t v___x_800_; lean_object* v___x_801_; 
v___x_800_ = 1;
v___x_801_ = lean_array_uget_borrowed(v_as_792_, v_i_793_);
if (v_a_791_ == 0)
{
uint8_t v___x_802_; 
v___x_802_ = lean_unbox(v___x_801_);
if (v___x_802_ == 0)
{
return v___x_800_;
}
else
{
goto v___jp_795_;
}
}
else
{
uint8_t v___x_803_; 
v___x_803_ = lean_unbox(v___x_801_);
if (v___x_803_ == 0)
{
goto v___jp_795_;
}
else
{
return v___x_800_;
}
}
}
else
{
uint8_t v___x_804_; 
v___x_804_ = 0;
return v___x_804_;
}
v___jp_795_:
{
size_t v___x_796_; size_t v___x_797_; 
v___x_796_ = ((size_t)1ULL);
v___x_797_ = lean_usize_add(v_i_793_, v___x_796_);
v_i_793_ = v___x_797_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9___boxed(lean_object* v_a_805_, lean_object* v_as_806_, lean_object* v_i_807_, lean_object* v_stop_808_){
_start:
{
uint8_t v_a_boxed_809_; size_t v_i_boxed_810_; size_t v_stop_boxed_811_; uint8_t v_res_812_; lean_object* v_r_813_; 
v_a_boxed_809_ = lean_unbox(v_a_805_);
v_i_boxed_810_ = lean_unbox_usize(v_i_807_);
lean_dec(v_i_807_);
v_stop_boxed_811_ = lean_unbox_usize(v_stop_808_);
lean_dec(v_stop_808_);
v_res_812_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(v_a_boxed_809_, v_as_806_, v_i_boxed_810_, v_stop_boxed_811_);
lean_dec_ref(v_as_806_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(lean_object* v_as_814_, uint8_t v_a_815_){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_816_ = lean_unsigned_to_nat(0u);
v___x_817_ = lean_array_get_size(v_as_814_);
v___x_818_ = lean_nat_dec_lt(v___x_816_, v___x_817_);
if (v___x_818_ == 0)
{
return v___x_818_;
}
else
{
if (v___x_818_ == 0)
{
return v___x_818_;
}
else
{
size_t v___x_819_; size_t v___x_820_; uint8_t v___x_821_; 
v___x_819_ = ((size_t)0ULL);
v___x_820_ = lean_usize_of_nat(v___x_817_);
v___x_821_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(v_a_815_, v_as_814_, v___x_819_, v___x_820_);
return v___x_821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___boxed(lean_object* v_as_822_, lean_object* v_a_823_){
_start:
{
uint8_t v_a_boxed_824_; uint8_t v_res_825_; lean_object* v_r_826_; 
v_a_boxed_824_ = lean_unbox(v_a_823_);
v_res_825_ = l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(v_as_822_, v_a_boxed_824_);
lean_dec_ref(v_as_822_);
v_r_826_ = lean_box(v_res_825_);
return v_r_826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0___boxed(lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_c_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0(v_a_829_, v_a_830_, v_c_831_, v___y_832_, v___y_833_);
lean_dec_ref(v_a_829_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(lean_object* v_declName_835_, lean_object* v_args_836_, lean_object* v_as_837_, size_t v_sz_838_, size_t v_i_839_, lean_object* v_b_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_a_844_; lean_object* v_a_845_; uint8_t v___x_849_; 
v___x_849_ = lean_usize_dec_lt(v_i_839_, v_sz_838_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
lean_dec_ref(v___y_841_);
lean_dec(v_declName_835_);
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v_b_840_);
lean_ctor_set(v___x_850_, 1, v___y_842_);
return v___x_850_;
}
else
{
lean_object* v_a_851_; lean_object* v_toSignature_852_; lean_object* v_value_853_; lean_object* v_name_854_; lean_object* v_params_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v_a_851_ = lean_array_uget_borrowed(v_as_837_, v_i_839_);
v_toSignature_852_ = lean_ctor_get(v_a_851_, 0);
v_value_853_ = lean_ctor_get(v_a_851_, 1);
v_name_854_ = lean_ctor_get(v_toSignature_852_, 0);
v_params_855_ = lean_ctor_get(v_toSignature_852_, 3);
v___x_856_ = lean_box(0);
v___x_857_ = lean_name_eq(v_declName_835_, v_name_854_);
if (v___x_857_ == 0)
{
v_a_844_ = v___x_856_;
v_a_845_ = v___y_842_;
goto v___jp_843_;
}
else
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_858_ = lean_array_get_size(v_params_855_);
v___x_859_ = lean_unsigned_to_nat(0u);
v___x_860_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0));
v___x_861_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v___x_858_, v_args_836_, v___x_859_, v___x_860_, v___y_841_, v___y_842_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v_a_863_; lean_object* v_visited_864_; lean_object* v_fixed_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v_a_862_ = lean_ctor_get(v___x_861_, 1);
lean_inc(v_a_862_);
v_a_863_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_863_);
lean_dec_ref(v___x_861_);
v_visited_864_ = lean_ctor_get(v_a_862_, 0);
v_fixed_865_ = lean_ctor_get(v_a_862_, 1);
lean_inc(v_a_863_);
lean_inc(v_declName_835_);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v_declName_835_);
lean_ctor_set(v___x_866_, 1, v_a_863_);
v___x_867_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_visited_864_, v___x_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_878_; 
lean_inc_ref(v_fixed_865_);
lean_inc_ref(v_visited_864_);
v_isSharedCheck_878_ = !lean_is_exclusive(v_a_862_);
if (v_isSharedCheck_878_ == 0)
{
lean_object* v_unused_879_; lean_object* v_unused_880_; 
v_unused_879_ = lean_ctor_get(v_a_862_, 1);
lean_dec(v_unused_879_);
v_unused_880_ = lean_ctor_get(v_a_862_, 0);
lean_dec(v_unused_880_);
v___x_869_ = v_a_862_;
v_isShared_870_ = v_isSharedCheck_878_;
goto v_resetjp_868_;
}
else
{
lean_dec(v_a_862_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_878_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___f_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
lean_inc(v_a_851_);
v___f_871_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0___boxed), 5, 2);
lean_closure_set(v___f_871_, 0, v_a_851_);
lean_closure_set(v___f_871_, 1, v_a_863_);
v___x_872_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(v_visited_864_, v___x_866_, v___x_856_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_872_);
v___x_874_ = v___x_869_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_fixed_865_);
v___x_874_ = v_reuseFailAlloc_877_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_875_; 
lean_inc_ref(v___y_841_);
lean_inc_ref(v_value_853_);
v___x_875_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v___f_871_, v_value_853_, v___y_841_, v___x_874_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; 
v_a_876_ = lean_ctor_get(v___x_875_, 1);
lean_inc(v_a_876_);
lean_dec_ref(v___x_875_);
v_a_844_ = v___x_856_;
v_a_845_ = v_a_876_;
goto v___jp_843_;
}
else
{
lean_dec_ref(v___y_841_);
lean_dec(v_declName_835_);
return v___x_875_;
}
}
}
}
else
{
lean_dec_ref(v___x_866_);
lean_dec(v_a_863_);
v_a_844_ = v___x_856_;
v_a_845_ = v_a_862_;
goto v___jp_843_;
}
}
else
{
lean_object* v_a_881_; lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_dec_ref(v___y_841_);
lean_dec(v_declName_835_);
v_a_881_ = lean_ctor_get(v___x_861_, 0);
v_a_882_ = lean_ctor_get(v___x_861_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_861_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_inc(v_a_881_);
lean_dec(v___x_861_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_881_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
v___jp_843_:
{
size_t v___x_846_; size_t v___x_847_; 
v___x_846_ = ((size_t)1ULL);
v___x_847_ = lean_usize_add(v_i_839_, v___x_846_);
v_i_839_ = v___x_847_;
v_b_840_ = v_a_844_;
v___y_842_ = v_a_845_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp(lean_object* v_declName_890_, lean_object* v_args_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v___y_895_; lean_object* v_decls_896_; lean_object* v___y_897_; lean_object* v_main_911_; lean_object* v_toSignature_912_; lean_object* v_decls_913_; lean_object* v_name_914_; lean_object* v_params_915_; uint8_t v___x_916_; 
v_main_911_ = lean_ctor_get(v_a_892_, 1);
v_toSignature_912_ = lean_ctor_get(v_main_911_, 0);
v_decls_913_ = lean_ctor_get(v_a_892_, 0);
lean_inc_ref(v_decls_913_);
v_name_914_ = lean_ctor_get(v_toSignature_912_, 0);
v_params_915_ = lean_ctor_get(v_toSignature_912_, 3);
v___x_916_ = lean_name_eq(v_declName_890_, v_name_914_);
if (v___x_916_ == 0)
{
v___y_895_ = v_a_892_;
v_decls_896_ = v_decls_913_;
v___y_897_ = v_a_893_;
goto v___jp_894_;
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_917_ = lean_array_get_size(v_params_915_);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = lean_box(0);
v___x_920_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(v___x_917_, v_args_891_, v___x_918_, v___x_919_, v_a_892_, v_a_893_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_930_; 
v_a_921_ = lean_ctor_get(v___x_920_, 1);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v___x_920_, 0);
lean_dec(v_unused_931_);
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_930_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_930_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_fixed_925_; uint8_t v___x_926_; 
v_fixed_925_ = lean_ctor_get(v_a_921_, 1);
v___x_926_ = l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(v_fixed_925_, v___x_916_);
if (v___x_926_ == 0)
{
lean_object* v___x_928_; 
lean_dec_ref(v_decls_913_);
lean_dec_ref(v_a_892_);
lean_dec(v_declName_890_);
if (v_isShared_924_ == 0)
{
lean_ctor_set_tag(v___x_923_, 1);
lean_ctor_set(v___x_923_, 0, v___x_919_);
v___x_928_ = v___x_923_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_a_921_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
else
{
lean_del_object(v___x_923_);
v___y_895_ = v_a_892_;
v_decls_896_ = v_decls_913_;
v___y_897_ = v_a_921_;
goto v___jp_894_;
}
}
}
else
{
lean_dec_ref(v_decls_913_);
lean_dec_ref(v_a_892_);
lean_dec(v_declName_890_);
return v___x_920_;
}
}
v___jp_894_:
{
lean_object* v___x_898_; size_t v_sz_899_; size_t v___x_900_; lean_object* v___x_901_; 
v___x_898_ = lean_box(0);
v_sz_899_ = lean_array_size(v_decls_896_);
v___x_900_ = ((size_t)0ULL);
v___x_901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(v_declName_890_, v_args_891_, v_decls_896_, v_sz_899_, v___x_900_, v___x_898_, v___y_895_, v___y_897_);
lean_dec_ref(v_decls_896_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
v_a_902_ = lean_ctor_get(v___x_901_, 1);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_909_ == 0)
{
lean_object* v_unused_910_; 
v_unused_910_ = lean_ctor_get(v___x_901_, 0);
lean_dec(v_unused_910_);
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_898_);
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
else
{
return v___x_901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalLetValue(lean_object* v_e_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
if (lean_obj_tag(v_e_932_) == 3)
{
lean_object* v_declName_935_; lean_object* v_args_936_; lean_object* v___x_937_; 
v_declName_935_ = lean_ctor_get(v_e_932_, 0);
lean_inc(v_declName_935_);
v_args_936_ = lean_ctor_get(v_e_932_, 2);
lean_inc_ref(v_args_936_);
lean_dec_ref(v_e_932_);
v___x_937_ = l_Lean_Compiler_LCNF_FixedParams_evalApp(v_declName_935_, v_args_936_, v_a_933_, v_a_934_);
lean_dec_ref(v_args_936_);
return v___x_937_;
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec_ref(v_a_933_);
lean_dec(v_e_932_);
v___x_938_ = lean_box(0);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v_a_934_);
return v___x_939_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(lean_object* v_as_940_, size_t v_i_941_, size_t v_stop_942_, lean_object* v_b_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___y_947_; uint8_t v___x_954_; 
v___x_954_ = lean_usize_dec_eq(v_i_941_, v_stop_942_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; 
v___x_955_ = lean_array_uget_borrowed(v_as_940_, v_i_941_);
switch(lean_obj_tag(v___x_955_))
{
case 0:
{
lean_object* v_code_956_; 
v_code_956_ = lean_ctor_get(v___x_955_, 2);
lean_inc_ref(v_code_956_);
v___y_947_ = v_code_956_;
goto v___jp_946_;
}
case 1:
{
lean_object* v_code_957_; 
v_code_957_ = lean_ctor_get(v___x_955_, 1);
lean_inc_ref(v_code_957_);
v___y_947_ = v_code_957_;
goto v___jp_946_;
}
default: 
{
lean_object* v_code_958_; 
v_code_958_ = lean_ctor_get(v___x_955_, 0);
lean_inc_ref(v_code_958_);
v___y_947_ = v_code_958_;
goto v___jp_946_;
}
}
}
else
{
lean_object* v___x_959_; 
lean_dec_ref(v___y_944_);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v_b_943_);
lean_ctor_set(v___x_959_, 1, v___y_945_);
return v___x_959_;
}
v___jp_946_:
{
lean_object* v___x_948_; 
lean_inc_ref(v___y_944_);
v___x_948_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v___y_947_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v_a_950_; size_t v___x_951_; size_t v___x_952_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
v_a_950_ = lean_ctor_get(v___x_948_, 1);
lean_inc(v_a_950_);
lean_dec_ref(v___x_948_);
v___x_951_ = ((size_t)1ULL);
v___x_952_ = lean_usize_add(v_i_941_, v___x_951_);
v_i_941_ = v___x_952_;
v_b_943_ = v_a_949_;
v___y_945_ = v_a_950_;
goto _start;
}
else
{
lean_dec_ref(v___y_944_);
return v___x_948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalCode(lean_object* v_code_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
switch(lean_obj_tag(v_code_960_))
{
case 0:
{
lean_object* v_decl_963_; lean_object* v_k_964_; lean_object* v_value_965_; lean_object* v___x_966_; 
v_decl_963_ = lean_ctor_get(v_code_960_, 0);
lean_inc_ref(v_decl_963_);
v_k_964_ = lean_ctor_get(v_code_960_, 1);
lean_inc_ref(v_k_964_);
lean_dec_ref(v_code_960_);
v_value_965_ = lean_ctor_get(v_decl_963_, 3);
lean_inc(v_value_965_);
lean_dec_ref(v_decl_963_);
lean_inc_ref(v_a_961_);
v___x_966_ = l_Lean_Compiler_LCNF_FixedParams_evalLetValue(v_value_965_, v_a_961_, v_a_962_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; 
v_a_967_ = lean_ctor_get(v___x_966_, 1);
lean_inc(v_a_967_);
lean_dec_ref(v___x_966_);
v_code_960_ = v_k_964_;
v_a_962_ = v_a_967_;
goto _start;
}
else
{
lean_dec_ref(v_k_964_);
lean_dec_ref(v_a_961_);
return v___x_966_;
}
}
case 1:
{
lean_object* v_decl_969_; lean_object* v_k_970_; lean_object* v___x_971_; 
v_decl_969_ = lean_ctor_get(v_code_960_, 0);
lean_inc_ref(v_decl_969_);
v_k_970_ = lean_ctor_get(v_code_960_, 1);
lean_inc_ref(v_k_970_);
lean_dec_ref(v_code_960_);
lean_inc_ref(v_a_961_);
lean_inc_ref(v_decl_969_);
v___x_971_ = l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(v_decl_969_, v_a_961_, v_a_962_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
if (lean_obj_tag(v_a_972_) == 1)
{
lean_object* v_a_973_; lean_object* v_val_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_994_; 
v_a_973_ = lean_ctor_get(v___x_971_, 1);
lean_inc(v_a_973_);
lean_dec_ref(v___x_971_);
v_val_974_ = lean_ctor_get(v_a_972_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v_a_972_);
if (v_isSharedCheck_994_ == 0)
{
v___x_976_ = v_a_972_;
v_isShared_977_ = v_isSharedCheck_994_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_val_974_);
lean_dec(v_a_972_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_994_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v_fvarId_978_; lean_object* v_decls_979_; lean_object* v_main_980_; lean_object* v_assignment_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_993_; 
v_fvarId_978_ = lean_ctor_get(v_decl_969_, 0);
lean_inc(v_fvarId_978_);
lean_dec_ref(v_decl_969_);
v_decls_979_ = lean_ctor_get(v_a_961_, 0);
v_main_980_ = lean_ctor_get(v_a_961_, 1);
v_assignment_981_ = lean_ctor_get(v_a_961_, 2);
v_isSharedCheck_993_ = !lean_is_exclusive(v_a_961_);
if (v_isSharedCheck_993_ == 0)
{
v___x_983_ = v_a_961_;
v_isShared_984_ = v_isSharedCheck_993_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_assignment_981_);
lean_inc(v_main_980_);
lean_inc(v_decls_979_);
lean_dec(v_a_961_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_993_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set_tag(v___x_976_, 2);
v___x_986_ = v___x_976_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_val_974_);
v___x_986_ = v_reuseFailAlloc_992_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_987_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_978_, v___x_986_, v_assignment_981_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 2, v___x_987_);
v___x_989_ = v___x_983_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_decls_979_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_main_980_);
lean_ctor_set(v_reuseFailAlloc_991_, 2, v___x_987_);
v___x_989_ = v_reuseFailAlloc_991_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
v_code_960_ = v_k_970_;
v_a_961_ = v___x_989_;
v_a_962_ = v_a_973_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_995_; lean_object* v_value_996_; lean_object* v___x_997_; 
lean_dec(v_a_972_);
v_a_995_ = lean_ctor_get(v___x_971_, 1);
lean_inc(v_a_995_);
lean_dec_ref(v___x_971_);
v_value_996_ = lean_ctor_get(v_decl_969_, 4);
lean_inc_ref(v_value_996_);
lean_dec_ref(v_decl_969_);
lean_inc_ref(v_a_961_);
v___x_997_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_value_996_, v_a_961_, v_a_995_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; 
v_a_998_ = lean_ctor_get(v___x_997_, 1);
lean_inc(v_a_998_);
lean_dec_ref(v___x_997_);
v_code_960_ = v_k_970_;
v_a_962_ = v_a_998_;
goto _start;
}
else
{
lean_dec_ref(v_k_970_);
lean_dec_ref(v_a_961_);
return v___x_997_;
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec_ref(v_k_970_);
lean_dec_ref(v_decl_969_);
lean_dec_ref(v_a_961_);
v_a_1000_ = lean_ctor_get(v___x_971_, 0);
v_a_1001_ = lean_ctor_get(v___x_971_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_971_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_inc(v_a_1000_);
lean_dec(v___x_971_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1000_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
case 2:
{
lean_object* v_decl_1009_; lean_object* v_k_1010_; lean_object* v_value_1011_; lean_object* v___x_1012_; 
v_decl_1009_ = lean_ctor_get(v_code_960_, 0);
lean_inc_ref(v_decl_1009_);
v_k_1010_ = lean_ctor_get(v_code_960_, 1);
lean_inc_ref(v_k_1010_);
lean_dec_ref(v_code_960_);
v_value_1011_ = lean_ctor_get(v_decl_1009_, 4);
lean_inc_ref(v_value_1011_);
lean_dec_ref(v_decl_1009_);
lean_inc_ref(v_a_961_);
v___x_1012_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_value_1011_, v_a_961_, v_a_962_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 1);
lean_inc(v_a_1013_);
lean_dec_ref(v___x_1012_);
v_code_960_ = v_k_1010_;
v_a_962_ = v_a_1013_;
goto _start;
}
else
{
lean_dec_ref(v_k_1010_);
lean_dec_ref(v_a_961_);
return v___x_1012_;
}
}
case 3:
{
lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref(v_a_961_);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_code_960_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; lean_object* v_unused_1024_; 
v_unused_1023_ = lean_ctor_get(v_code_960_, 1);
lean_dec(v_unused_1023_);
v_unused_1024_ = lean_ctor_get(v_code_960_, 0);
lean_dec(v_unused_1024_);
v___x_1016_ = v_code_960_;
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
else
{
lean_dec(v_code_960_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1018_ = lean_box(0);
if (v_isShared_1017_ == 0)
{
lean_ctor_set_tag(v___x_1016_, 0);
lean_ctor_set(v___x_1016_, 1, v_a_962_);
lean_ctor_set(v___x_1016_, 0, v___x_1018_);
v___x_1020_ = v___x_1016_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_a_962_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
case 4:
{
lean_object* v_cases_1025_; lean_object* v_alts_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v_cases_1025_ = lean_ctor_get(v_code_960_, 0);
lean_inc_ref(v_cases_1025_);
lean_dec_ref(v_code_960_);
v_alts_1026_ = lean_ctor_get(v_cases_1025_, 3);
lean_inc_ref(v_alts_1026_);
lean_dec_ref(v_cases_1025_);
v___x_1027_ = lean_unsigned_to_nat(0u);
v___x_1028_ = lean_array_get_size(v_alts_1026_);
v___x_1029_ = lean_box(0);
v___x_1030_ = lean_nat_dec_lt(v___x_1027_, v___x_1028_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; 
lean_dec_ref(v_alts_1026_);
lean_dec_ref(v_a_961_);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v_a_962_);
return v___x_1031_;
}
else
{
uint8_t v___x_1032_; 
v___x_1032_ = lean_nat_dec_le(v___x_1028_, v___x_1028_);
if (v___x_1032_ == 0)
{
if (v___x_1030_ == 0)
{
lean_object* v___x_1033_; 
lean_dec_ref(v_alts_1026_);
lean_dec_ref(v_a_961_);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1029_);
lean_ctor_set(v___x_1033_, 1, v_a_962_);
return v___x_1033_;
}
else
{
size_t v___x_1034_; size_t v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = ((size_t)0ULL);
v___x_1035_ = lean_usize_of_nat(v___x_1028_);
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(v_alts_1026_, v___x_1034_, v___x_1035_, v___x_1029_, v_a_961_, v_a_962_);
lean_dec_ref(v_alts_1026_);
return v___x_1036_;
}
}
else
{
size_t v___x_1037_; size_t v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = ((size_t)0ULL);
v___x_1038_ = lean_usize_of_nat(v___x_1028_);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(v_alts_1026_, v___x_1037_, v___x_1038_, v___x_1029_, v_a_961_, v_a_962_);
lean_dec_ref(v_alts_1026_);
return v___x_1039_;
}
}
}
default: 
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
lean_dec_ref(v_a_961_);
lean_dec_ref(v_code_960_);
v___x_1040_ = lean_box(0);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v_a_962_);
return v___x_1041_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0(lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_c_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_decls_1047_; lean_object* v_main_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1057_; 
v_decls_1047_ = lean_ctor_get(v___y_1045_, 0);
v_main_1048_ = lean_ctor_get(v___y_1045_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___y_1045_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v___y_1045_, 2);
lean_dec(v_unused_1058_);
v___x_1050_ = v___y_1045_;
v_isShared_1051_ = v_isSharedCheck_1057_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_main_1048_);
lean_inc(v_decls_1047_);
lean_dec(v___y_1045_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1057_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1052_ = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(v_a_1042_, v_a_1043_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 2, v___x_1052_);
v___x_1054_ = v___x_1050_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_decls_1047_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_main_1048_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_c_1044_, v___x_1054_, v___y_1046_);
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9___boxed(lean_object* v_as_1059_, lean_object* v_i_1060_, lean_object* v_stop_1061_, lean_object* v_b_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
size_t v_i_boxed_1065_; size_t v_stop_boxed_1066_; lean_object* v_res_1067_; 
v_i_boxed_1065_ = lean_unbox_usize(v_i_1060_);
lean_dec(v_i_1060_);
v_stop_boxed_1066_ = lean_unbox_usize(v_stop_1061_);
lean_dec(v_stop_1061_);
v_res_1067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(v_as_1059_, v_i_boxed_1065_, v_stop_boxed_1066_, v_b_1062_, v___y_1063_, v___y_1064_);
lean_dec_ref(v_as_1059_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_evalApp___boxed(lean_object* v_declName_1068_, lean_object* v_args_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_Compiler_LCNF_FixedParams_evalApp(v_declName_1068_, v_args_1069_, v_a_1070_, v_a_1071_);
lean_dec_ref(v_args_1069_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___boxed(lean_object* v_declName_1073_, lean_object* v_args_1074_, lean_object* v_as_1075_, lean_object* v_sz_1076_, lean_object* v_i_1077_, lean_object* v_b_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
size_t v_sz_boxed_1081_; size_t v_i_boxed_1082_; lean_object* v_res_1083_; 
v_sz_boxed_1081_ = lean_unbox_usize(v_sz_1076_);
lean_dec(v_sz_1076_);
v_i_boxed_1082_ = lean_unbox_usize(v_i_1077_);
lean_dec(v_i_1077_);
v_res_1083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(v_declName_1073_, v_args_1074_, v_as_1075_, v_sz_boxed_1081_, v_i_boxed_1082_, v_b_1078_, v___y_1079_, v___y_1080_);
lean_dec_ref(v_as_1075_);
lean_dec_ref(v_args_1074_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3(uint8_t v_pu_1084_, lean_object* v_f_1085_, lean_object* v_v_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v_f_1085_, v_v_1086_, v___y_1087_, v___y_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___boxed(lean_object* v_pu_1090_, lean_object* v_f_1091_, lean_object* v_v_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
uint8_t v_pu_boxed_1095_; lean_object* v_res_1096_; 
v_pu_boxed_1095_ = lean_unbox(v_pu_1090_);
v_res_1096_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3(v_pu_boxed_1095_, v_f_1091_, v_v_1092_, v___y_1093_, v___y_1094_);
return v_res_1096_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1(lean_object* v_00_u03b2_1097_, lean_object* v_m_1098_, lean_object* v_a_1099_){
_start:
{
uint8_t v___x_1100_; 
v___x_1100_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_m_1098_, v_a_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___boxed(lean_object* v_00_u03b2_1101_, lean_object* v_m_1102_, lean_object* v_a_1103_){
_start:
{
uint8_t v_res_1104_; lean_object* v_r_1105_; 
v_res_1104_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1(v_00_u03b2_1101_, v_m_1102_, v_a_1103_);
lean_dec_ref(v_a_1103_);
lean_dec_ref(v_m_1102_);
v_r_1105_ = lean_box(v_res_1104_);
return v_r_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2(lean_object* v_00_u03b2_1106_, lean_object* v_m_1107_, lean_object* v_a_1108_, lean_object* v_b_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(v_m_1107_, v_a_1108_, v_b_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4(lean_object* v_upperBound_1111_, lean_object* v_args_1112_, lean_object* v_inst_1113_, lean_object* v_R_1114_, lean_object* v_a_1115_, lean_object* v_b_1116_, lean_object* v_c_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v_upperBound_1111_, v_args_1112_, v_a_1115_, v_b_1116_, v___y_1118_, v___y_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___boxed(lean_object* v_upperBound_1121_, lean_object* v_args_1122_, lean_object* v_inst_1123_, lean_object* v_R_1124_, lean_object* v_a_1125_, lean_object* v_b_1126_, lean_object* v_c_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4(v_upperBound_1121_, v_args_1122_, v_inst_1123_, v_R_1124_, v_a_1125_, v_b_1126_, v_c_1127_, v___y_1128_, v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec_ref(v_args_1122_);
lean_dec(v_upperBound_1121_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7(lean_object* v_upperBound_1131_, lean_object* v_args_1132_, lean_object* v_inst_1133_, lean_object* v_R_1134_, lean_object* v_a_1135_, lean_object* v_b_1136_, lean_object* v_c_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(v_upperBound_1131_, v_args_1132_, v_a_1135_, v_b_1136_, v___y_1138_, v___y_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___boxed(lean_object* v_upperBound_1141_, lean_object* v_args_1142_, lean_object* v_inst_1143_, lean_object* v_R_1144_, lean_object* v_a_1145_, lean_object* v_b_1146_, lean_object* v_c_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7(v_upperBound_1141_, v_args_1142_, v_inst_1143_, v_R_1144_, v_a_1145_, v_b_1146_, v_c_1147_, v___y_1148_, v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec_ref(v_args_1142_);
lean_dec(v_upperBound_1141_);
return v_res_1150_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1(lean_object* v_00_u03b2_1151_, lean_object* v_a_1152_, lean_object* v_x_1153_){
_start:
{
uint8_t v___x_1154_; 
v___x_1154_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_1152_, v_x_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1155_, lean_object* v_a_1156_, lean_object* v_x_1157_){
_start:
{
uint8_t v_res_1158_; lean_object* v_r_1159_; 
v_res_1158_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1(v_00_u03b2_1155_, v_a_1156_, v_x_1157_);
lean_dec(v_x_1157_);
lean_dec_ref(v_a_1156_);
v_r_1159_ = lean_box(v_res_1158_);
return v_r_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4(lean_object* v_00_u03b2_1160_, lean_object* v_data_1161_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(v_data_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4(lean_object* v_xs_1163_, lean_object* v_ys_1164_, lean_object* v_hsz_1165_, lean_object* v_x_1166_, lean_object* v_x_1167_){
_start:
{
uint8_t v___x_1168_; 
v___x_1168_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(v_xs_1163_, v_ys_1164_, v_x_1166_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___boxed(lean_object* v_xs_1169_, lean_object* v_ys_1170_, lean_object* v_hsz_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_){
_start:
{
uint8_t v_res_1174_; lean_object* v_r_1175_; 
v_res_1174_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4(v_xs_1169_, v_ys_1170_, v_hsz_1171_, v_x_1172_, v_x_1173_);
lean_dec_ref(v_ys_1170_);
lean_dec_ref(v_xs_1169_);
v_r_1175_ = lean_box(v_res_1174_);
return v_r_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_1176_, lean_object* v_i_1177_, lean_object* v_source_1178_, lean_object* v_target_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(v_i_1177_, v_source_1178_, v_target_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14(lean_object* v_00_u03b2_1181_, lean_object* v_x_1182_, lean_object* v_x_1183_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(v_x_1182_, v_x_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(lean_object* v_upperBound_1185_, lean_object* v_a_1186_, lean_object* v_b_1187_){
_start:
{
uint8_t v___x_1188_; 
v___x_1188_ = lean_nat_dec_lt(v_a_1186_, v_upperBound_1185_);
if (v___x_1188_ == 0)
{
lean_dec(v_a_1186_);
return v_b_1187_;
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
lean_inc(v_a_1186_);
v___x_1189_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1189_, 0, v_a_1186_);
v___x_1190_ = lean_array_push(v_b_1187_, v___x_1189_);
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1192_ = lean_nat_add(v_a_1186_, v___x_1191_);
lean_dec(v_a_1186_);
v_a_1186_ = v___x_1192_;
v_b_1187_ = v___x_1190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg___boxed(lean_object* v_upperBound_1194_, lean_object* v_a_1195_, lean_object* v_b_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_upperBound_1194_, v_a_1195_, v_b_1196_);
lean_dec(v_upperBound_1194_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(lean_object* v_numParams_1198_){
_start:
{
lean_object* v___x_1199_; lean_object* v_values_1200_; lean_object* v___x_1201_; 
v___x_1199_ = lean_unsigned_to_nat(0u);
v_values_1200_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0));
v___x_1201_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_numParams_1198_, v___x_1199_, v_values_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FixedParams_mkInitialValues___boxed(lean_object* v_numParams_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(v_numParams_1202_);
lean_dec(v_numParams_1202_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0(lean_object* v_upperBound_1204_, lean_object* v_inst_1205_, lean_object* v_R_1206_, lean_object* v_a_1207_, lean_object* v_b_1208_, lean_object* v_c_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_upperBound_1204_, v_a_1207_, v_b_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___boxed(lean_object* v_upperBound_1211_, lean_object* v_inst_1212_, lean_object* v_R_1213_, lean_object* v_a_1214_, lean_object* v_b_1215_, lean_object* v_c_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0(v_upperBound_1211_, v_inst_1212_, v_R_1213_, v_a_1214_, v_b_1215_, v_c_1216_);
lean_dec(v_upperBound_1211_);
return v_res_1217_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = lean_box(0);
v___x_1219_ = lean_unsigned_to_nat(16u);
v___x_1220_ = lean_mk_array(v___x_1219_, v___x_1218_);
return v___x_1220_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0);
v___x_1222_ = lean_unsigned_to_nat(0u);
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
lean_ctor_set(v___x_1223_, 1, v___x_1221_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(lean_object* v_decls_1224_, lean_object* v_as_1225_, size_t v_sz_1226_, size_t v_i_1227_, lean_object* v_b_1228_){
_start:
{
lean_object* v_a_1230_; uint8_t v___x_1234_; 
v___x_1234_ = lean_usize_dec_lt(v_i_1227_, v_sz_1226_);
if (v___x_1234_ == 0)
{
lean_dec_ref(v_decls_1224_);
return v_b_1228_;
}
else
{
lean_object* v_a_1235_; lean_object* v_toSignature_1236_; lean_object* v_value_1237_; lean_object* v_name_1238_; lean_object* v_params_1239_; lean_object* v_s_1241_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v_a_1235_ = lean_array_uget_borrowed(v_as_1225_, v_i_1227_);
v_toSignature_1236_ = lean_ctor_get(v_a_1235_, 0);
v_value_1237_ = lean_ctor_get(v_a_1235_, 1);
v_name_1238_ = lean_ctor_get(v_toSignature_1236_, 0);
v_params_1239_ = lean_ctor_get(v_toSignature_1236_, 3);
v___x_1244_ = lean_array_get_size(v_params_1239_);
v___x_1245_ = l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(v___x_1244_);
v___x_1246_ = lean_box(v___x_1234_);
v___x_1247_ = lean_mk_array(v___x_1244_, v___x_1246_);
if (lean_obj_tag(v_value_1237_) == 0)
{
lean_object* v_code_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_a_1254_; 
v_code_1248_ = lean_ctor_get(v_value_1237_, 0);
v___x_1249_ = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(v_a_1235_, v___x_1245_);
lean_inc(v_a_1235_);
lean_inc_ref(v_decls_1224_);
v___x_1250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1250_, 0, v_decls_1224_);
lean_ctor_set(v___x_1250_, 1, v_a_1235_);
lean_ctor_set(v___x_1250_, 2, v___x_1249_);
v___x_1251_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1);
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v___x_1247_);
lean_inc_ref(v_code_1248_);
v___x_1253_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_code_1248_, v___x_1250_, v___x_1252_);
v_a_1254_ = lean_ctor_get(v___x_1253_, 1);
lean_inc(v_a_1254_);
lean_dec_ref(v___x_1253_);
v_s_1241_ = v_a_1254_;
goto v___jp_1240_;
}
else
{
lean_object* v___x_1255_; 
lean_dec_ref(v___x_1245_);
lean_inc(v_name_1238_);
v___x_1255_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1238_, v___x_1247_, v_b_1228_);
v_a_1230_ = v___x_1255_;
goto v___jp_1229_;
}
v___jp_1240_:
{
lean_object* v_fixed_1242_; lean_object* v___x_1243_; 
v_fixed_1242_ = lean_ctor_get(v_s_1241_, 1);
lean_inc_ref(v_fixed_1242_);
lean_dec_ref(v_s_1241_);
lean_inc(v_name_1238_);
v___x_1243_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1238_, v_fixed_1242_, v_b_1228_);
v_a_1230_ = v___x_1243_;
goto v___jp_1229_;
}
}
v___jp_1229_:
{
size_t v___x_1231_; size_t v___x_1232_; 
v___x_1231_ = ((size_t)1ULL);
v___x_1232_ = lean_usize_add(v_i_1227_, v___x_1231_);
v_i_1227_ = v___x_1232_;
v_b_1228_ = v_a_1230_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___boxed(lean_object* v_decls_1256_, lean_object* v_as_1257_, lean_object* v_sz_1258_, lean_object* v_i_1259_, lean_object* v_b_1260_){
_start:
{
size_t v_sz_boxed_1261_; size_t v_i_boxed_1262_; lean_object* v_res_1263_; 
v_sz_boxed_1261_ = lean_unbox_usize(v_sz_1258_);
lean_dec(v_sz_1258_);
v_i_boxed_1262_ = lean_unbox_usize(v_i_1259_);
lean_dec(v_i_1259_);
v_res_1263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(v_decls_1256_, v_as_1257_, v_sz_boxed_1261_, v_i_boxed_1262_, v_b_1260_);
lean_dec_ref(v_as_1257_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFixedParamsMap(lean_object* v_decls_1264_){
_start:
{
lean_object* v_result_1265_; size_t v_sz_1266_; size_t v___x_1267_; lean_object* v___x_1268_; 
v_result_1265_ = lean_box(1);
v_sz_1266_ = lean_array_size(v_decls_1264_);
v___x_1267_ = ((size_t)0ULL);
lean_inc_ref(v_decls_1264_);
v___x_1268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(v_decls_1264_, v_decls_1264_, v_sz_1266_, v___x_1267_, v_result_1265_);
lean_dec_ref(v_decls_1264_);
return v___x_1268_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_FixedParams(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
