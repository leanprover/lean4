// Lean compiler output
// Module: Lean.Compiler.IR.ToIR
// Imports: public import Lean.Compiler.IR.CompilerM public import Lean.Compiler.IR.ToIRType
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
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__0;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__1;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__2;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3;
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedArg_default;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__0;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__1;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__2;
extern lean_object* l_Lean_IR_declMapExt;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_toIRType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCtorInfo(lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody_default__1;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_ToIR_lowerCode___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 38, .m_data = "all local functions should be λ-lifted"};
static const lean_object* l_Lean_IR_ToIR_lowerCode___closed__2 = (const lean_object*)&l_Lean_IR_ToIR_lowerCode___closed__2_value;
static const lean_string_object l_Lean_IR_ToIR_lowerCode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.IR.ToIR.lowerCode"};
static const lean_object* l_Lean_IR_ToIR_lowerCode___closed__1 = (const lean_object*)&l_Lean_IR_ToIR_lowerCode___closed__1_value;
static const lean_string_object l_Lean_IR_ToIR_lowerCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Compiler.IR.ToIR"};
static const lean_object* l_Lean_IR_ToIR_lowerCode___closed__0 = (const lean_object*)&l_Lean_IR_ToIR_lowerCode___closed__0_value;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_ToIR_lowerCode___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_IR_ToIR_lowerCode___closed__4 = (const lean_object*)&l_Lean_IR_ToIR_lowerCode___closed__4_value;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__5;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__6;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__7;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__8;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__9;
lean_object* l_Lean_IR_nameToIRType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_IR_mkDummyExternDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_IR_toIR___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_M_run___redArg___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_IR_ToIR_M_run___redArg___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_IR_ToIR_M_run___redArg___closed__2;
x_6 = lean_st_mk_ref(x_5);
lean_inc(x_6);
x_7 = lean_apply_4(x_1, x_6, x_2, x_3, lean_box(0));
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_st_ref_get(x_6);
lean_dec(x_6);
lean_dec(x_9);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_st_ref_get(x_6);
lean_dec(x_6);
lean_dec(x_11);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
}
else
{
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_M_run___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_M_run___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_M_run(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2));
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(163u);
x_4 = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1));
x_5 = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3;
x_5 = lean_panic_fn(x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = l_Lean_instBEqFVarId_beq(x_6, x_2);
if (x_9 == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
lean_inc(x_7);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_array_get_size(x_4);
x_6 = l_Lean_instHashableFVarId_hash(x_3);
x_7 = 32;
x_8 = lean_uint64_shift_right(x_6, x_7);
x_9 = lean_uint64_xor(x_6, x_8);
x_10 = 16;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = lean_uint64_to_usize(x_12);
x_14 = lean_usize_of_nat(x_5);
x_15 = 1;
x_16 = lean_usize_sub(x_14, x_15);
x_17 = lean_usize_land(x_13, x_16);
x_18 = lean_array_uget(x_4, x_17);
x_19 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(x_1, x_3, x_18);
lean_dec(x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Lean_IR_instInhabitedArg_default;
x_7 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_6, x_5, x_1);
lean_dec_ref(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_getFVarValue___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_getFVarValue___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_getFVarValue(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_panic_fn(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_panic_fn(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_6, x_5, x_1);
lean_dec_ref(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_getJoinPointValue___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_getJoinPointValue___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_getJoinPointValue(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_instBEqFVarId_beq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_instHashableFVarId_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_instHashableFVarId_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_instHashableFVarId_hash(x_2);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(x_2, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_19);
x_27 = lean_array_uset(x_5, x_18, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_25, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(x_27);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_1);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_4, x_35);
lean_dec(x_4);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_37, 2, x_19);
x_38 = lean_array_uset(x_5, x_18, x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_mul(x_36, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(x_38);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(x_6, x_1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_7, x_10);
lean_ctor_set(x_4, 2, x_11);
lean_ctor_set(x_4, 0, x_9);
x_12 = lean_st_ref_set(x_2, x_4);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_4, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
lean_inc(x_16);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(x_14, x_1, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_16, x_19);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_st_ref_set(x_2, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_16);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_bindVar___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindVar___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindVar(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(x_6, x_1, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_7, x_9);
lean_ctor_set(x_4, 2, x_10);
lean_ctor_set(x_4, 1, x_8);
x_11 = lean_st_ref_set(x_2, x_4);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
lean_inc(x_15);
x_16 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(x_14, x_1, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_15, x_17);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_st_ref_set(x_2, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_15);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_bindJoinPoint___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindJoinPoint___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindJoinPoint(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_box(1);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(x_6, x_1, x_7);
lean_ctor_set(x_4, 0, x_8);
x_9 = lean_st_ref_set(x_2, x_4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_4, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_15 = lean_box(1);
x_16 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(x_12, x_1, x_15);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_14);
x_18 = lean_st_ref_set(x_2, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_bindErased___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindErased___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindErased(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_addDecl___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_addDecl___redArg___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 5);
lean_dec(x_7);
x_8 = l_Lean_IR_declMapExt;
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_box(0);
x_12 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_8, x_6, x_1, x_10, x_11);
lean_dec(x_10);
x_13 = l_Lean_IR_ToIR_addDecl___redArg___closed__2;
lean_ctor_set(x_4, 5, x_13);
lean_ctor_set(x_4, 0, x_12);
x_14 = lean_st_ref_set(x_2, x_4);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_ctor_get(x_4, 3);
x_21 = lean_ctor_get(x_4, 4);
x_22 = lean_ctor_get(x_4, 6);
x_23 = lean_ctor_get(x_4, 7);
x_24 = lean_ctor_get(x_4, 8);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_25 = l_Lean_IR_declMapExt;
x_26 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_box(0);
x_29 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_25, x_17, x_1, x_27, x_28);
lean_dec(x_27);
x_30 = l_Lean_IR_ToIR_addDecl___redArg___closed__2;
x_31 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_31, 2, x_19);
lean_ctor_set(x_31, 3, x_20);
lean_ctor_set(x_31, 4, x_21);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_22);
lean_ctor_set(x_31, 7, x_23);
lean_ctor_set(x_31, 8, x_24);
x_32 = lean_st_ref_set(x_2, x_31);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_addDecl___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_addDecl___redArg(x_1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_addDecl(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_8; uint8_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_3 = x_1;
} else {
 lean_dec_ref(x_1);
 x_3 = lean_box(0);
}
x_8 = lean_cstr_to_nat("4294967296");
x_9 = lean_nat_dec_lt(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_box(8);
x_4 = x_10;
goto block_7;
}
else
{
lean_object* x_11; 
x_11 = lean_box(12);
x_4 = x_11;
goto block_7;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
if (lean_is_scalar(x_3)) {
 x_5 = lean_alloc_ctor(0, 1, 0);
} else {
 x_5 = x_3;
}
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
case 1:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_box(7);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
case 2:
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get_uint8(x_1, 0);
lean_dec_ref(x_1);
x_20 = lean_uint8_to_nat(x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
case 3:
{
uint16_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get_uint16(x_1, 0);
lean_dec_ref(x_1);
x_25 = lean_uint16_to_nat(x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_box(2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
case 4:
{
uint32_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get_uint32(x_1, 0);
lean_dec_ref(x_1);
x_30 = lean_uint32_to_nat(x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_box(3);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
case 5:
{
uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get_uint64(x_1, 0);
lean_dec_ref(x_1);
x_35 = lean_uint64_to_nat(x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_box(4);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
default: 
{
uint64_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get_uint64(x_1, 0);
lean_dec_ref(x_1);
x_40 = lean_uint64_to_nat(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_box(5);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = l_Lean_IR_ToIR_getFVarValue___redArg(x_6, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_lowerArg___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerArg___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec_ref(x_1);
x_7 = l_Lean_IR_ToIR_bindVar___redArg(x_4, x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_IR_toIRType(x_5);
lean_dec_ref(x_5);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_6);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = l_Lean_IR_toIRType(x_5);
lean_dec_ref(x_5);
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_6);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_lowerParam___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerParam___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerParam(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCtorInfo(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_7);
return x_8;
}
}
}
static lean_object* _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0;
x_7 = l_ReaderT_instMonad___redArg(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
x_16 = lean_ctor_get(x_9, 1);
lean_dec(x_16);
x_17 = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1));
x_18 = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2));
lean_inc_ref(x_12);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_19, 0, x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_24, 0, x_13);
lean_ctor_set(x_9, 4, x_22);
lean_ctor_set(x_9, 3, x_23);
lean_ctor_set(x_9, 2, x_24);
lean_ctor_set(x_9, 1, x_17);
lean_ctor_set(x_9, 0, x_21);
lean_ctor_set(x_7, 1, x_18);
x_25 = l_ReaderT_instMonad___redArg(x_7);
x_26 = l_Lean_IR_instInhabitedFnBody_default__1;
x_27 = l_instInhabitedOfMonad___redArg(x_25, x_26);
x_28 = lean_panic_fn(x_27, x_1);
x_29 = lean_apply_4(x_28, x_2, x_3, x_4, lean_box(0));
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 2);
x_32 = lean_ctor_get(x_9, 3);
x_33 = lean_ctor_get(x_9, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_34 = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1));
x_35 = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2));
lean_inc_ref(x_30);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_36, 0, x_30);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_32);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_41, 0, x_31);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_40);
lean_ctor_set(x_42, 4, x_39);
lean_ctor_set(x_7, 1, x_35);
lean_ctor_set(x_7, 0, x_42);
x_43 = l_ReaderT_instMonad___redArg(x_7);
x_44 = l_Lean_IR_instInhabitedFnBody_default__1;
x_45 = l_instInhabitedOfMonad___redArg(x_43, x_44);
x_46 = lean_panic_fn(x_45, x_1);
x_47 = lean_apply_4(x_46, x_2, x_3, x_4, lean_box(0));
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_48 = lean_ctor_get(x_7, 0);
lean_inc(x_48);
lean_dec(x_7);
x_49 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_48, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 4);
lean_inc(x_52);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 lean_ctor_release(x_48, 4);
 x_53 = x_48;
} else {
 lean_dec_ref(x_48);
 x_53 = lean_box(0);
}
x_54 = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1));
x_55 = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2));
lean_inc_ref(x_49);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_56, 0, x_49);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_57, 0, x_49);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_52);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_60, 0, x_51);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_61, 0, x_50);
if (lean_is_scalar(x_53)) {
 x_62 = lean_alloc_ctor(0, 5, 0);
} else {
 x_62 = x_53;
}
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_60);
lean_ctor_set(x_62, 4, x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_55);
x_64 = l_ReaderT_instMonad___redArg(x_63);
x_65 = l_Lean_IR_instInhabitedFnBody_default__1;
x_66 = l_instInhabitedOfMonad___redArg(x_64, x_65);
x_67 = lean_panic_fn(x_66, x_1);
x_68 = lean_apply_4(x_67, x_2, x_3, x_4, lean_box(0));
return x_68;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = l_Lean_IR_ToIR_lowerArg___redArg(x_8, x_4);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_3, x_2, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_12, x_2, x_10);
x_2 = x_14;
x_3 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec_ref(x_3);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(x_6, x_7, x_3, x_4);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = l_Lean_IR_ToIR_lowerParam___redArg(x_8, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_3, x_2, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_12, x_2, x_10);
x_2 = x_14;
x_3 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec_ref(x_3);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(x_6, x_7, x_3, x_4);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
x_9 = lean_apply_5(x_2, x_8, x_4, x_5, x_6, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_ToIR_lowerLet___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
x_9 = lean_apply_5(x_2, x_8, x_4, x_5, x_6, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_ToIR_lowerLet___lam__3(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
x_9 = lean_apply_5(x_2, x_8, x_4, x_5, x_6, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_ToIR_lowerLet___lam__5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_4);
x_10 = lean_apply_5(x_3, x_9, x_5, x_6, x_7, lean_box(0));
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_ToIR_lowerLet___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_IR_toIRType(x_1);
x_9 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_apply_5(x_2, x_9, x_4, x_5, x_6, lean_box(0));
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_ToIR_lowerLet___lam__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_array_size(x_1);
x_11 = 0;
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(x_10, x_11, x_1, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_3);
x_16 = lean_apply_5(x_4, x_15, x_6, x_7, x_8, lean_box(0));
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_2, 3);
x_21 = lean_ctor_get(x_2, 4);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
lean_ctor_set(x_22, 4, x_21);
x_23 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_13);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_3);
x_24 = lean_apply_5(x_4, x_23, x_6, x_7, x_8, lean_box(0));
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_12, 0);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_IR_ToIR_lowerLet___lam__6(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = lean_apply_5(x_1, x_7, x_3, x_4, x_5, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_lowerLet___lam__8(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_array_size(x_1);
x_9 = 0;
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(x_8, x_9, x_1, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_apply_5(x_2, x_12, x_4, x_5, x_6, lean_box(0));
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_ToIR_lowerLet___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_ToIR_bindVar___redArg(x_1, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_4);
lean_ctor_set(x_16, 3, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_11;
}
}
else
{
uint8_t x_18; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_ToIR_lowerLet___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_ToIR_getFVarValue___redArg(x_3, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_apply_5(x_4, x_11, x_5, x_6, x_7, lean_box(0));
return x_12;
}
else
{
lean_object* x_13; 
lean_dec_ref(x_4);
x_13 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_5, x_6, x_7);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = l_Lean_IR_toIRType(x_8);
lean_inc(x_10);
lean_inc_ref(x_2);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 8, 3);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_10);
switch (lean_obj_tag(x_9)) {
case 0:
{
uint8_t x_12; 
lean_dec_ref(x_11);
lean_inc(x_7);
lean_dec_ref(x_1);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = l_Lean_IR_ToIR_lowerLitValue(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_ctor_set_tag(x_9, 11);
lean_ctor_set(x_9, 0, x_15);
x_16 = l_Lean_IR_ToIR_lowerLet___lam__0(x_7, x_2, x_10, x_9, x_3, x_4, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = l_Lean_IR_ToIR_lowerLitValue(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_IR_ToIR_lowerLet___lam__0(x_7, x_2, x_10, x_20, x_3, x_4, x_5);
return x_21;
}
}
case 1:
{
lean_object* x_22; 
lean_dec_ref(x_11);
lean_dec(x_10);
x_22 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5);
return x_22;
}
case 4:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
x_23 = lean_ctor_get(x_9, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_24);
lean_dec_ref(x_9);
x_25 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__1___boxed), 7, 2);
lean_closure_set(x_25, 0, x_24);
lean_closure_set(x_25, 1, x_11);
x_26 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(x_1, x_2, x_23, x_25, x_3, x_4, x_5);
lean_dec(x_23);
return x_26;
}
case 5:
{
uint8_t x_27; 
lean_dec_ref(x_11);
lean_inc(x_7);
lean_dec_ref(x_1);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
x_30 = lean_array_size(x_29);
x_31 = 0;
x_32 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(x_30, x_31, x_29, x_3);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
lean_object* x_35; 
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 1, x_33);
x_35 = l_Lean_IR_ToIR_lowerLet___lam__0(x_7, x_2, x_10, x_9, x_3, x_4, x_5);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_28, 0);
x_37 = lean_ctor_get(x_28, 1);
x_38 = lean_ctor_get(x_28, 2);
x_39 = lean_ctor_get(x_28, 3);
x_40 = lean_ctor_get(x_28, 4);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_28);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_38);
lean_ctor_set(x_41, 3, x_39);
lean_ctor_set(x_41, 4, x_40);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 1, x_33);
lean_ctor_set(x_9, 0, x_41);
x_42 = l_Lean_IR_ToIR_lowerLet___lam__0(x_7, x_2, x_10, x_9, x_3, x_4, x_5);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_free_object(x_9);
lean_dec_ref(x_28);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_43 = !lean_is_exclusive(x_32);
if (x_43 == 0)
{
return x_32;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_32, 0);
lean_inc(x_44);
lean_dec(x_32);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_9, 0);
x_47 = lean_ctor_get(x_9, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_9);
x_48 = lean_array_size(x_47);
x_49 = 0;
x_50 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(x_48, x_49, x_47, x_3);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_ctor_get(x_46, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_46, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_46, 3);
lean_inc(x_55);
x_56 = lean_ctor_get(x_46, 4);
lean_inc(x_56);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 lean_ctor_release(x_46, 4);
 x_57 = x_46;
} else {
 lean_dec_ref(x_46);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 5, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_53);
lean_ctor_set(x_58, 2, x_54);
lean_ctor_set(x_58, 3, x_55);
lean_ctor_set(x_58, 4, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_51);
x_60 = l_Lean_IR_ToIR_lowerLet___lam__0(x_7, x_2, x_10, x_59, x_3, x_4, x_5);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_46);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_61 = lean_ctor_get(x_50, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_62 = x_50;
} else {
 lean_dec_ref(x_50);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_61);
return x_63;
}
}
}
case 6:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_10);
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_9, 1);
lean_inc(x_65);
lean_dec_ref(x_9);
x_66 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__2___boxed), 7, 2);
lean_closure_set(x_66, 0, x_64);
lean_closure_set(x_66, 1, x_11);
x_67 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(x_1, x_2, x_65, x_66, x_3, x_4, x_5);
lean_dec(x_65);
return x_67;
}
case 7:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_10);
x_68 = lean_ctor_get(x_9, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_9, 1);
lean_inc(x_69);
lean_dec_ref(x_9);
x_70 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__3___boxed), 7, 2);
lean_closure_set(x_70, 0, x_68);
lean_closure_set(x_70, 1, x_11);
x_71 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(x_1, x_2, x_69, x_70, x_3, x_4, x_5);
lean_dec(x_69);
return x_71;
}
case 8:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_10);
x_72 = lean_ctor_get(x_9, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_9, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_9, 2);
lean_inc(x_74);
lean_dec_ref(x_9);
x_75 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__4___boxed), 8, 3);
lean_closure_set(x_75, 0, x_72);
lean_closure_set(x_75, 1, x_73);
lean_closure_set(x_75, 2, x_11);
x_76 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(x_1, x_2, x_74, x_75, x_3, x_4, x_5);
lean_dec(x_74);
return x_76;
}
case 9:
{
uint8_t x_77; 
lean_dec_ref(x_11);
lean_inc(x_7);
lean_dec_ref(x_1);
x_77 = !lean_is_exclusive(x_9);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; size_t x_80; size_t x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_9, 0);
x_79 = lean_ctor_get(x_9, 1);
x_80 = lean_array_size(x_79);
x_81 = 0;
x_82 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(x_80, x_81, x_79, x_3);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
lean_ctor_set_tag(x_9, 6);
lean_ctor_set(x_9, 1, x_83);
x_84 = l_Lean_IR_ToIR_lowerLet___lam__0(x_7, x_2, x_10, x_9, x_3, x_4, x_5);
return x_84;
}
else
{
uint8_t x_85; 
lean_free_object(x_9);
lean_dec(x_78);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_85 = !lean_is_exclusive(x_82);
if (x_85 == 0)
{
return x_82;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; size_t x_90; size_t x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_9, 0);
x_89 = lean_ctor_get(x_9, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_9);
x_90 = lean_array_size(x_89);
x_91 = 0;
x_92 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(x_90, x_91, x_89, x_3);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
x_94 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_IR_ToIR_lowerLet___lam__0(x_7, x_2, x_10, x_94, x_3, x_4, x_5);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_88);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_96 = lean_ctor_get(x_92, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_97 = x_92;
} else {
 lean_dec_ref(x_92);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_96);
return x_98;
}
}
}
case 10:
{
uint8_t x_99; 
lean_dec_ref(x_11);
lean_inc(x_7);
lean_dec_ref(x_1);
x_99 = !lean_is_exclusive(x_9);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; size_t x_102; size_t x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_9, 0);
x_101 = lean_ctor_get(x_9, 1);
x_102 = lean_array_size(x_101);
x_103 = 0;
x_104 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(x_102, x_103, x_101, x_3);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_105);
x_106 = l_Lean_IR_ToIR_lowerLet___lam__0(x_7, x_2, x_10, x_9, x_3, x_4, x_5);
return x_106;
}
else
{
uint8_t x_107; 
lean_free_object(x_9);
lean_dec(x_100);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_107 = !lean_is_exclusive(x_104);
if (x_107 == 0)
{
return x_104;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
lean_dec(x_104);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; size_t x_112; size_t x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_9, 0);
x_111 = lean_ctor_get(x_9, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_9);
x_112 = lean_array_size(x_111);
x_113 = 0;
x_114 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(x_112, x_113, x_111, x_3);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec_ref(x_114);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_110);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_IR_ToIR_lowerLet___lam__0(x_7, x_2, x_10, x_116, x_3, x_4, x_5);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_110);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_118 = lean_ctor_get(x_114, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_119 = x_114;
} else {
 lean_dec_ref(x_114);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 1, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_118);
return x_120;
}
}
}
case 11:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_10);
x_121 = lean_ctor_get(x_9, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_9, 1);
lean_inc(x_122);
lean_dec_ref(x_9);
x_123 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__5___boxed), 7, 2);
lean_closure_set(x_123, 0, x_121);
lean_closure_set(x_123, 1, x_11);
x_124 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(x_1, x_2, x_122, x_123, x_3, x_4, x_5);
lean_dec(x_122);
return x_124;
}
case 12:
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_10);
x_125 = lean_ctor_get(x_9, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_126);
x_127 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_128 = lean_ctor_get(x_9, 2);
lean_inc_ref(x_128);
lean_dec_ref(x_9);
x_129 = lean_box(x_127);
x_130 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 9, 4);
lean_closure_set(x_130, 0, x_128);
lean_closure_set(x_130, 1, x_126);
lean_closure_set(x_130, 2, x_129);
lean_closure_set(x_130, 3, x_11);
x_131 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(x_1, x_2, x_125, x_130, x_3, x_4, x_5);
lean_dec(x_125);
return x_131;
}
case 13:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_10);
x_132 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_132);
x_133 = lean_ctor_get(x_9, 1);
lean_inc(x_133);
lean_dec_ref(x_9);
x_134 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__7___boxed), 7, 2);
lean_closure_set(x_134, 0, x_132);
lean_closure_set(x_134, 1, x_11);
x_135 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(x_1, x_2, x_133, x_134, x_3, x_4, x_5);
lean_dec(x_133);
return x_135;
}
default: 
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_10);
x_136 = lean_ctor_get(x_9, 0);
lean_inc(x_136);
lean_dec_ref(x_9);
x_137 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__8___boxed), 6, 1);
lean_closure_set(x_137, 0, x_11);
x_138 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(x_1, x_2, x_136, x_137, x_3, x_4, x_5);
lean_dec(x_136);
return x_138;
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__2));
x_2 = lean_unsigned_to_nat(15u);
x_3 = lean_unsigned_to_nat(112u);
x_4 = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
x_5 = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_Lean_IR_ToIR_lowerCode(x_8, x_2, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_17);
lean_ctor_set(x_19, 4, x_18);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_19);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_7, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_7, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_7, 4);
lean_inc(x_25);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 x_26 = x_7;
} else {
 lean_dec_ref(x_7);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(0, 5, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_24);
lean_ctor_set(x_27, 4, x_25);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_1, 0, x_27);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_1);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_free_object(x_1);
lean_dec_ref(x_7);
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
return x_9;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_9, 0);
lean_inc(x_30);
lean_dec(x_9);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
x_34 = l_Lean_IR_ToIR_lowerCode(x_33, x_2, x_3, x_4);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_32, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_32, 4);
lean_inc(x_41);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 x_42 = x_32;
} else {
 lean_dec_ref(x_32);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 5, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set(x_43, 2, x_39);
lean_ctor_set(x_43, 3, x_40);
lean_ctor_set(x_43, 4, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_35);
if (lean_is_scalar(x_36)) {
 x_45 = lean_alloc_ctor(0, 1, 0);
} else {
 x_45 = x_36;
}
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_32);
x_46 = lean_ctor_get(x_34, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_47 = x_34;
} else {
 lean_dec_ref(x_34);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_46);
return x_48;
}
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_1);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_1, 0);
x_51 = l_Lean_IR_ToIR_lowerCode(x_50, x_2, x_3, x_4);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_53);
lean_ctor_set(x_51, 0, x_1);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec(x_51);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_54);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_1);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_free_object(x_1);
x_56 = !lean_is_exclusive(x_51);
if (x_56 == 0)
{
return x_51;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
lean_dec(x_51);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
lean_dec(x_1);
x_60 = l_Lean_IR_ToIR_lowerCode(x_59, x_2, x_3, x_4);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_61);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 1, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_66 = x_60;
} else {
 lean_dec_ref(x_60);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_3, x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_11 = l_Lean_IR_ToIR_lowerAlt(x_10, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_14, x_2, x_12);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
x_2 = lean_unsigned_to_nat(53u);
x_3 = lean_unsigned_to_nat(95u);
x_4 = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
x_5 = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
x_2 = lean_unsigned_to_nat(38u);
x_3 = lean_unsigned_to_nat(110u);
x_4 = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
x_5 = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_unsigned_to_nat(109u);
x_4 = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
x_5 = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
x_2 = lean_unsigned_to_nat(38u);
x_3 = lean_unsigned_to_nat(106u);
x_4 = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
x_5 = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_unsigned_to_nat(105u);
x_4 = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
x_5 = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = l_Lean_IR_ToIR_lowerLet(x_6, x_7, x_2, x_3, x_4);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_1);
x_9 = l_Lean_IR_ToIR_lowerCode___closed__3;
x_10 = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(x_9, x_2, x_3, x_4);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 2);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_11, 4);
lean_inc_ref(x_15);
lean_dec_ref(x_11);
x_16 = l_Lean_IR_ToIR_bindJoinPoint___redArg(x_13, x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_array_size(x_14);
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(x_18, x_19, x_14, x_2);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_22 = l_Lean_IR_ToIR_lowerCode(x_15, x_2, x_3, x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_Lean_IR_ToIR_lowerCode(x_12, x_2, x_3, x_4);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_23);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_17);
return x_24;
}
}
else
{
lean_dec(x_21);
lean_dec(x_17);
lean_dec_ref(x_12);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_22;
}
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_12);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_16, 0);
lean_inc(x_35);
lean_dec(x_16);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
case 3:
{
uint8_t x_37; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_37 = !lean_is_exclusive(x_1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
x_40 = l_Lean_IR_ToIR_getJoinPointValue___redArg(x_38, x_2);
lean_dec(x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_array_size(x_39);
x_43 = 0;
x_44 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(x_42, x_43, x_39, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_ctor_set_tag(x_1, 11);
lean_ctor_set(x_1, 1, x_46);
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set(x_44, 0, x_1);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
lean_dec(x_44);
lean_ctor_set_tag(x_1, 11);
lean_ctor_set(x_1, 1, x_47);
lean_ctor_set(x_1, 0, x_41);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_1);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_41);
lean_free_object(x_1);
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_free_object(x_1);
lean_dec_ref(x_39);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_40);
if (x_52 == 0)
{
return x_40;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_40, 0);
lean_inc(x_53);
lean_dec(x_40);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_1, 0);
x_56 = lean_ctor_get(x_1, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_1);
x_57 = l_Lean_IR_ToIR_getJoinPointValue___redArg(x_55, x_2);
lean_dec(x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; size_t x_59; size_t x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = lean_array_size(x_56);
x_60 = 0;
x_61 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(x_59, x_60, x_56, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_62);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 1, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_58);
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_67 = x_61;
} else {
 lean_dec_ref(x_61);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec_ref(x_56);
lean_dec(x_2);
x_69 = lean_ctor_get(x_57, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_70 = x_57;
} else {
 lean_dec_ref(x_57);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
return x_71;
}
}
}
case 4:
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_72);
lean_dec_ref(x_1);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_ctor_get(x_72, 2);
x_76 = lean_ctor_get(x_72, 3);
x_77 = lean_ctor_get(x_72, 1);
lean_dec(x_77);
x_78 = l_Lean_IR_ToIR_getFVarValue___redArg(x_75, x_2);
lean_dec(x_75);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; size_t x_81; size_t x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = lean_array_size(x_76);
x_82 = 0;
x_83 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(x_81, x_82, x_76, x_2, x_3, x_4);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = l_Lean_IR_nameToIRType(x_74);
lean_ctor_set_tag(x_72, 9);
lean_ctor_set(x_72, 3, x_85);
lean_ctor_set(x_72, 2, x_86);
lean_ctor_set(x_72, 1, x_80);
lean_ctor_set(x_83, 0, x_72);
return x_83;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
lean_dec(x_83);
x_88 = l_Lean_IR_nameToIRType(x_74);
lean_ctor_set_tag(x_72, 9);
lean_ctor_set(x_72, 3, x_87);
lean_ctor_set(x_72, 2, x_88);
lean_ctor_set(x_72, 1, x_80);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_72);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_80);
lean_free_object(x_72);
lean_dec(x_74);
x_90 = !lean_is_exclusive(x_83);
if (x_90 == 0)
{
return x_83;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_83, 0);
lean_inc(x_91);
lean_dec(x_83);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_79);
lean_free_object(x_72);
lean_dec_ref(x_76);
lean_dec(x_74);
x_93 = l_Lean_IR_ToIR_lowerCode___closed__5;
x_94 = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(x_93, x_2, x_3, x_4);
return x_94;
}
}
else
{
uint8_t x_95; 
lean_free_object(x_72);
lean_dec_ref(x_76);
lean_dec(x_74);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_78);
if (x_95 == 0)
{
return x_78;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_78, 0);
lean_inc(x_96);
lean_dec(x_78);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_72, 0);
x_99 = lean_ctor_get(x_72, 2);
x_100 = lean_ctor_get(x_72, 3);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_72);
x_101 = l_Lean_IR_ToIR_getFVarValue___redArg(x_99, x_2);
lean_dec(x_99);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; size_t x_104; size_t x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec_ref(x_102);
x_104 = lean_array_size(x_100);
x_105 = 0;
x_106 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(x_104, x_105, x_100, x_2, x_3, x_4);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_109 = l_Lean_IR_nameToIRType(x_98);
x_110 = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(x_110, 0, x_98);
lean_ctor_set(x_110, 1, x_103);
lean_ctor_set(x_110, 2, x_109);
lean_ctor_set(x_110, 3, x_107);
if (lean_is_scalar(x_108)) {
 x_111 = lean_alloc_ctor(0, 1, 0);
} else {
 x_111 = x_108;
}
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_103);
lean_dec(x_98);
x_112 = lean_ctor_get(x_106, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 x_113 = x_106;
} else {
 lean_dec_ref(x_106);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 1, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_112);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_102);
lean_dec_ref(x_100);
lean_dec(x_98);
x_115 = l_Lean_IR_ToIR_lowerCode___closed__5;
x_116 = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(x_115, x_2, x_3, x_4);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec_ref(x_100);
lean_dec(x_98);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_117 = lean_ctor_get(x_101, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 x_118 = x_101;
} else {
 lean_dec_ref(x_101);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 1, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_117);
return x_119;
}
}
}
case 5:
{
uint8_t x_120; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_120 = !lean_is_exclusive(x_1);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_1, 0);
x_122 = l_Lean_IR_ToIR_getFVarValue___redArg(x_121, x_2);
lean_dec(x_2);
lean_dec(x_121);
if (lean_obj_tag(x_122) == 0)
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_122, 0);
lean_ctor_set_tag(x_1, 10);
lean_ctor_set(x_1, 0, x_124);
lean_ctor_set(x_122, 0, x_1);
return x_122;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_122, 0);
lean_inc(x_125);
lean_dec(x_122);
lean_ctor_set_tag(x_1, 10);
lean_ctor_set(x_1, 0, x_125);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_1);
return x_126;
}
}
else
{
uint8_t x_127; 
lean_free_object(x_1);
x_127 = !lean_is_exclusive(x_122);
if (x_127 == 0)
{
return x_122;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_122, 0);
lean_inc(x_128);
lean_dec(x_122);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_1, 0);
lean_inc(x_130);
lean_dec(x_1);
x_131 = l_Lean_IR_ToIR_getFVarValue___redArg(x_130, x_2);
lean_dec(x_2);
lean_dec(x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_133 = x_131;
} else {
 lean_dec_ref(x_131);
 x_133 = lean_box(0);
}
x_134 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_134, 0, x_132);
if (lean_is_scalar(x_133)) {
 x_135 = lean_alloc_ctor(0, 1, 0);
} else {
 x_135 = x_133;
}
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_131, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_137 = x_131;
} else {
 lean_dec_ref(x_131);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 1, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_136);
return x_138;
}
}
}
case 6:
{
uint8_t x_139; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_139 = !lean_is_exclusive(x_1);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_1, 0);
lean_dec(x_140);
x_141 = lean_box(12);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_141);
return x_1;
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_1);
x_142 = lean_box(12);
x_143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_143, 0, x_142);
return x_143;
}
}
case 7:
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_1);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_1, 0);
x_146 = lean_ctor_get(x_1, 1);
x_147 = lean_ctor_get(x_1, 2);
x_148 = lean_ctor_get(x_1, 3);
x_149 = l_Lean_IR_ToIR_getFVarValue___redArg(x_147, x_2);
lean_dec(x_147);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec_ref(x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec_ref(x_150);
x_152 = l_Lean_IR_ToIR_getFVarValue___redArg(x_145, x_2);
lean_dec(x_145);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec_ref(x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec_ref(x_153);
x_155 = l_Lean_IR_ToIR_lowerCode(x_148, x_2, x_3, x_4);
if (lean_obj_tag(x_155) == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_155, 0);
lean_ctor_set_tag(x_1, 4);
lean_ctor_set(x_1, 3, x_157);
lean_ctor_set(x_1, 2, x_151);
lean_ctor_set(x_1, 0, x_154);
lean_ctor_set(x_155, 0, x_1);
return x_155;
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_155, 0);
lean_inc(x_158);
lean_dec(x_155);
lean_ctor_set_tag(x_1, 4);
lean_ctor_set(x_1, 3, x_158);
lean_ctor_set(x_1, 2, x_151);
lean_ctor_set(x_1, 0, x_154);
x_159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_159, 0, x_1);
return x_159;
}
}
else
{
lean_dec(x_154);
lean_dec(x_151);
lean_free_object(x_1);
lean_dec(x_146);
return x_155;
}
}
else
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_153);
lean_dec(x_151);
lean_free_object(x_1);
lean_dec_ref(x_148);
lean_dec(x_146);
x_160 = l_Lean_IR_ToIR_lowerCode___closed__6;
x_161 = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(x_160, x_2, x_3, x_4);
return x_161;
}
}
else
{
uint8_t x_162; 
lean_dec(x_151);
lean_free_object(x_1);
lean_dec_ref(x_148);
lean_dec(x_146);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_162 = !lean_is_exclusive(x_152);
if (x_162 == 0)
{
return x_152;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_152, 0);
lean_inc(x_163);
lean_dec(x_152);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
return x_164;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_150);
lean_free_object(x_1);
lean_dec_ref(x_148);
lean_dec(x_146);
lean_dec(x_145);
x_165 = l_Lean_IR_ToIR_lowerCode___closed__7;
x_166 = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(x_165, x_2, x_3, x_4);
return x_166;
}
}
else
{
uint8_t x_167; 
lean_free_object(x_1);
lean_dec_ref(x_148);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_167 = !lean_is_exclusive(x_149);
if (x_167 == 0)
{
return x_149;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_149, 0);
lean_inc(x_168);
lean_dec(x_149);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = lean_ctor_get(x_1, 0);
x_171 = lean_ctor_get(x_1, 1);
x_172 = lean_ctor_get(x_1, 2);
x_173 = lean_ctor_get(x_1, 3);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_1);
x_174 = l_Lean_IR_ToIR_getFVarValue___redArg(x_172, x_2);
lean_dec(x_172);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
lean_dec_ref(x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
x_177 = l_Lean_IR_ToIR_getFVarValue___redArg(x_170, x_2);
lean_dec(x_170);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec_ref(x_177);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
lean_dec_ref(x_178);
x_180 = l_Lean_IR_ToIR_lowerCode(x_173, x_2, x_3, x_4);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 x_182 = x_180;
} else {
 lean_dec_ref(x_180);
 x_182 = lean_box(0);
}
x_183 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_183, 0, x_179);
lean_ctor_set(x_183, 1, x_171);
lean_ctor_set(x_183, 2, x_176);
lean_ctor_set(x_183, 3, x_181);
if (lean_is_scalar(x_182)) {
 x_184 = lean_alloc_ctor(0, 1, 0);
} else {
 x_184 = x_182;
}
lean_ctor_set(x_184, 0, x_183);
return x_184;
}
else
{
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_171);
return x_180;
}
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_dec(x_178);
lean_dec(x_176);
lean_dec_ref(x_173);
lean_dec(x_171);
x_185 = l_Lean_IR_ToIR_lowerCode___closed__6;
x_186 = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(x_185, x_2, x_3, x_4);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_176);
lean_dec_ref(x_173);
lean_dec(x_171);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_187 = lean_ctor_get(x_177, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 x_188 = x_177;
} else {
 lean_dec_ref(x_177);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 1, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_187);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_175);
lean_dec_ref(x_173);
lean_dec(x_171);
lean_dec(x_170);
x_190 = l_Lean_IR_ToIR_lowerCode___closed__7;
x_191 = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(x_190, x_2, x_3, x_4);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec_ref(x_173);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_192 = lean_ctor_get(x_174, 0);
lean_inc(x_192);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_193 = x_174;
} else {
 lean_dec_ref(x_174);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_192);
return x_194;
}
}
}
default: 
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_1);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_196 = lean_ctor_get(x_1, 0);
x_197 = lean_ctor_get(x_1, 1);
x_198 = lean_ctor_get(x_1, 2);
x_199 = lean_ctor_get(x_1, 3);
x_200 = lean_ctor_get(x_1, 4);
x_201 = lean_ctor_get(x_1, 5);
x_202 = l_Lean_IR_ToIR_getFVarValue___redArg(x_199, x_2);
lean_dec(x_199);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
lean_dec_ref(x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec_ref(x_203);
x_205 = l_Lean_IR_ToIR_getFVarValue___redArg(x_196, x_2);
lean_dec(x_196);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
lean_dec_ref(x_205);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
lean_dec_ref(x_206);
x_208 = l_Lean_IR_ToIR_lowerCode(x_201, x_2, x_3, x_4);
if (lean_obj_tag(x_208) == 0)
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_208);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_208, 0);
x_211 = l_Lean_IR_toIRType(x_200);
lean_dec_ref(x_200);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 5, x_210);
lean_ctor_set(x_1, 4, x_211);
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 0, x_207);
lean_ctor_set(x_208, 0, x_1);
return x_208;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_208, 0);
lean_inc(x_212);
lean_dec(x_208);
x_213 = l_Lean_IR_toIRType(x_200);
lean_dec_ref(x_200);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 5, x_212);
lean_ctor_set(x_1, 4, x_213);
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 0, x_207);
x_214 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_214, 0, x_1);
return x_214;
}
}
else
{
lean_dec(x_207);
lean_dec(x_204);
lean_free_object(x_1);
lean_dec_ref(x_200);
lean_dec(x_198);
lean_dec(x_197);
return x_208;
}
}
else
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_206);
lean_dec(x_204);
lean_free_object(x_1);
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_198);
lean_dec(x_197);
x_215 = l_Lean_IR_ToIR_lowerCode___closed__8;
x_216 = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(x_215, x_2, x_3, x_4);
return x_216;
}
}
else
{
uint8_t x_217; 
lean_dec(x_204);
lean_free_object(x_1);
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_217 = !lean_is_exclusive(x_205);
if (x_217 == 0)
{
return x_205;
}
else
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_205, 0);
lean_inc(x_218);
lean_dec(x_205);
x_219 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_219, 0, x_218);
return x_219;
}
}
}
else
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_203);
lean_free_object(x_1);
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
x_220 = l_Lean_IR_ToIR_lowerCode___closed__9;
x_221 = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(x_220, x_2, x_3, x_4);
return x_221;
}
}
else
{
uint8_t x_222; 
lean_free_object(x_1);
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_222 = !lean_is_exclusive(x_202);
if (x_222 == 0)
{
return x_202;
}
else
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_202, 0);
lean_inc(x_223);
lean_dec(x_202);
x_224 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_224, 0, x_223);
return x_224;
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_225 = lean_ctor_get(x_1, 0);
x_226 = lean_ctor_get(x_1, 1);
x_227 = lean_ctor_get(x_1, 2);
x_228 = lean_ctor_get(x_1, 3);
x_229 = lean_ctor_get(x_1, 4);
x_230 = lean_ctor_get(x_1, 5);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_1);
x_231 = l_Lean_IR_ToIR_getFVarValue___redArg(x_228, x_2);
lean_dec(x_228);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
lean_dec_ref(x_231);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
lean_dec_ref(x_232);
x_234 = l_Lean_IR_ToIR_getFVarValue___redArg(x_225, x_2);
lean_dec(x_225);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
lean_dec_ref(x_234);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
lean_dec_ref(x_235);
x_237 = l_Lean_IR_ToIR_lowerCode(x_230, x_2, x_3, x_4);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 x_239 = x_237;
} else {
 lean_dec_ref(x_237);
 x_239 = lean_box(0);
}
x_240 = l_Lean_IR_toIRType(x_229);
lean_dec_ref(x_229);
x_241 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_241, 0, x_236);
lean_ctor_set(x_241, 1, x_226);
lean_ctor_set(x_241, 2, x_227);
lean_ctor_set(x_241, 3, x_233);
lean_ctor_set(x_241, 4, x_240);
lean_ctor_set(x_241, 5, x_238);
if (lean_is_scalar(x_239)) {
 x_242 = lean_alloc_ctor(0, 1, 0);
} else {
 x_242 = x_239;
}
lean_ctor_set(x_242, 0, x_241);
return x_242;
}
else
{
lean_dec(x_236);
lean_dec(x_233);
lean_dec_ref(x_229);
lean_dec(x_227);
lean_dec(x_226);
return x_237;
}
}
else
{
lean_object* x_243; lean_object* x_244; 
lean_dec(x_235);
lean_dec(x_233);
lean_dec_ref(x_230);
lean_dec_ref(x_229);
lean_dec(x_227);
lean_dec(x_226);
x_243 = l_Lean_IR_ToIR_lowerCode___closed__8;
x_244 = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(x_243, x_2, x_3, x_4);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_233);
lean_dec_ref(x_230);
lean_dec_ref(x_229);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_245 = lean_ctor_get(x_234, 0);
lean_inc(x_245);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 x_246 = x_234;
} else {
 lean_dec_ref(x_234);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 1, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_245);
return x_247;
}
}
else
{
lean_object* x_248; lean_object* x_249; 
lean_dec(x_232);
lean_dec_ref(x_230);
lean_dec_ref(x_229);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
x_248 = l_Lean_IR_ToIR_lowerCode___closed__9;
x_249 = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(x_248, x_2, x_3, x_4);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec_ref(x_230);
lean_dec_ref(x_229);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_250 = lean_ctor_get(x_231, 0);
lean_inc(x_250);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_251 = x_231;
} else {
 lean_dec_ref(x_231);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 1, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_250);
return x_252;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Lean_IR_ToIR_bindErased___redArg(x_7, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec_ref(x_8);
x_9 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(x_8, x_9, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerAlt(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_lowerLet(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerCode(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(x_8, x_9, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(x_8, x_9, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_10);
lean_dec_ref(x_6);
x_11 = lean_array_size(x_10);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(x_11, x_12, x_10, x_2);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_IR_toIRType(x_9);
lean_dec_ref(x_9);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_17; 
lean_free_object(x_13);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = l_Lean_IR_ToIR_lowerCode(x_18, x_2, x_3, x_4);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_21);
lean_ctor_set(x_23, 4, x_22);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_23);
lean_ctor_set(x_19, 0, x_7);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set(x_26, 2, x_16);
lean_ctor_set(x_26, 3, x_24);
lean_ctor_set(x_26, 4, x_25);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_26);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_7);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_free_object(x_7);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_8);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_19, 0);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_7, 0);
lean_inc(x_31);
lean_dec(x_7);
x_32 = l_Lean_IR_ToIR_lowerCode(x_31, x_2, x_3, x_4);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_8);
lean_ctor_set(x_36, 1, x_15);
lean_ctor_set(x_36, 2, x_16);
lean_ctor_set(x_36, 3, x_33);
lean_ctor_set(x_36, 4, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
if (lean_is_scalar(x_34)) {
 x_38 = lean_alloc_ctor(0, 1, 0);
} else {
 x_38 = x_34;
}
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_8);
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_40 = x_32;
} else {
 lean_dec_ref(x_32);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_7);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_7, 0);
x_44 = l_List_isEmpty___redArg(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_4);
x_45 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_45, 0, x_8);
lean_ctor_set(x_45, 1, x_15);
lean_ctor_set(x_45, 2, x_16);
lean_ctor_set(x_45, 3, x_43);
lean_ctor_set(x_7, 0, x_45);
lean_ctor_set(x_13, 0, x_7);
return x_13;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_free_object(x_7);
lean_dec(x_43);
lean_free_object(x_13);
x_46 = l_Lean_IR_mkDummyExternDecl(x_8, x_15, x_16);
x_47 = l_Lean_IR_ToIR_addDecl___redArg(x_46, x_4);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_47);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_7, 0);
lean_inc(x_53);
lean_dec(x_7);
x_54 = l_List_isEmpty___redArg(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_4);
x_55 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_55, 0, x_8);
lean_ctor_set(x_55, 1, x_15);
lean_ctor_set(x_55, 2, x_16);
lean_ctor_set(x_55, 3, x_53);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_13, 0, x_56);
return x_13;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_53);
lean_free_object(x_13);
x_57 = l_Lean_IR_mkDummyExternDecl(x_8, x_15, x_16);
x_58 = l_Lean_IR_ToIR_addDecl___redArg(x_57, x_4);
lean_dec(x_4);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_59 = x_58;
} else {
 lean_dec_ref(x_58);
 x_59 = lean_box(0);
}
x_60 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 1, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_13, 0);
lean_inc(x_62);
lean_dec(x_13);
x_63 = l_Lean_IR_toIRType(x_9);
lean_dec_ref(x_9);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_64);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_65 = x_7;
} else {
 lean_dec_ref(x_7);
 x_65 = lean_box(0);
}
x_66 = l_Lean_IR_ToIR_lowerCode(x_64, x_2, x_3, x_4);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_8);
lean_ctor_set(x_70, 1, x_62);
lean_ctor_set(x_70, 2, x_63);
lean_ctor_set(x_70, 3, x_67);
lean_ctor_set(x_70, 4, x_69);
if (lean_is_scalar(x_65)) {
 x_71 = lean_alloc_ctor(1, 1, 0);
} else {
 x_71 = x_65;
 lean_ctor_set_tag(x_71, 1);
}
lean_ctor_set(x_71, 0, x_70);
if (lean_is_scalar(x_68)) {
 x_72 = lean_alloc_ctor(0, 1, 0);
} else {
 x_72 = x_68;
}
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_8);
x_73 = lean_ctor_get(x_66, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_74 = x_66;
} else {
 lean_dec_ref(x_66);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_76 = lean_ctor_get(x_7, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_77 = x_7;
} else {
 lean_dec_ref(x_7);
 x_77 = lean_box(0);
}
x_78 = l_List_isEmpty___redArg(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_4);
x_79 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_79, 0, x_8);
lean_ctor_set(x_79, 1, x_62);
lean_ctor_set(x_79, 2, x_63);
lean_ctor_set(x_79, 3, x_76);
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_77;
}
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_77);
lean_dec(x_76);
x_82 = l_Lean_IR_mkDummyExternDecl(x_8, x_62, x_63);
x_83 = l_Lean_IR_ToIR_addDecl___redArg(x_82, x_4);
lean_dec(x_4);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_84 = x_83;
} else {
 lean_dec_ref(x_83);
 x_84 = lean_box(0);
}
x_85 = lean_box(0);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 1, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_13);
if (x_87 == 0)
{
return x_13;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_13, 0);
lean_inc(x_88);
lean_dec(x_13);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerDecl(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_5);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_uget(x_1, x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerDecl___boxed), 5, 1);
lean_closure_set(x_11, 0, x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
x_12 = l_Lean_IR_ToIR_M_run___redArg(x_11, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec_ref(x_13);
x_20 = lean_array_push(x_4, x_19);
x_14 = x_20;
goto block_18;
}
else
{
lean_dec(x_13);
x_14 = x_4;
goto block_18;
}
block_18:
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_4 = x_14;
goto _start;
}
}
else
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(x_1, x_8, x_9, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_IR_toIR___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = l_Lean_IR_toIR___closed__0;
x_6 = lean_array_size(x_1);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(x_1, x_6, x_7, x_5, x_2, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_toIR(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_5;
}
}
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ToIR(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIRType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_ToIR_M_run___redArg___closed__0 = _init_l_Lean_IR_ToIR_M_run___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___redArg___closed__0);
l_Lean_IR_ToIR_M_run___redArg___closed__1 = _init_l_Lean_IR_ToIR_M_run___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___redArg___closed__1);
l_Lean_IR_ToIR_M_run___redArg___closed__2 = _init_l_Lean_IR_ToIR_M_run___redArg___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___redArg___closed__2);
l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3);
l_Lean_IR_ToIR_addDecl___redArg___closed__0 = _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___redArg___closed__0);
l_Lean_IR_ToIR_addDecl___redArg___closed__1 = _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___redArg___closed__1);
l_Lean_IR_ToIR_addDecl___redArg___closed__2 = _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___redArg___closed__2);
l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0 = _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0();
lean_mark_persistent(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0);
l_Lean_IR_ToIR_lowerCode___closed__3 = _init_l_Lean_IR_ToIR_lowerCode___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__3);
l_Lean_IR_ToIR_lowerCode___closed__5 = _init_l_Lean_IR_ToIR_lowerCode___closed__5();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__5);
l_Lean_IR_ToIR_lowerCode___closed__6 = _init_l_Lean_IR_ToIR_lowerCode___closed__6();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__6);
l_Lean_IR_ToIR_lowerCode___closed__7 = _init_l_Lean_IR_ToIR_lowerCode___closed__7();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__7);
l_Lean_IR_ToIR_lowerCode___closed__8 = _init_l_Lean_IR_ToIR_lowerCode___closed__8();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__8);
l_Lean_IR_ToIR_lowerCode___closed__9 = _init_l_Lean_IR_ToIR_lowerCode___closed__9();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__9);
l_Lean_IR_toIR___closed__0 = _init_l_Lean_IR_toIR___closed__0();
lean_mark_persistent(l_Lean_IR_toIR___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
