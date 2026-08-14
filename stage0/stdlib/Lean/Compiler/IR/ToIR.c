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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_IR_toIRType(lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedArg_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_uint64_to_nat(uint64_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody_default__1;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_IR_nameToIRType(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_IR_mkDummyExternDecl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_declMapExt;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_IR_ToIR_M_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__0;
static lean_once_cell_t l_Lean_IR_ToIR_M_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__1;
static lean_once_cell_t l_Lean_IR_ToIR_M_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_IR_ToIR_addDecl___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__0;
static lean_once_cell_t l_Lean_IR_ToIR_addDecl___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__1;
static lean_once_cell_t l_Lean_IR_ToIR_addDecl___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCtorInfo(lean_object*);
static lean_once_cell_t l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_ToIR_lowerCode___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 38, .m_data = "all local functions should be λ-lifted"};
static const lean_object* l_Lean_IR_ToIR_lowerCode___closed__2 = (const lean_object*)&l_Lean_IR_ToIR_lowerCode___closed__2_value;
static const lean_string_object l_Lean_IR_ToIR_lowerCode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.IR.ToIR.lowerCode"};
static const lean_object* l_Lean_IR_ToIR_lowerCode___closed__1 = (const lean_object*)&l_Lean_IR_ToIR_lowerCode___closed__1_value;
static const lean_string_object l_Lean_IR_ToIR_lowerCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Compiler.IR.ToIR"};
static const lean_object* l_Lean_IR_ToIR_lowerCode___closed__0 = (const lean_object*)&l_Lean_IR_ToIR_lowerCode___closed__0_value;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_ToIR_lowerCode___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_IR_ToIR_lowerCode___closed__4 = (const lean_object*)&l_Lean_IR_ToIR_lowerCode___closed__4_value;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__5;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__6;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__7;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__8;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__9;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__10;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__11;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__12;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__13;
static lean_once_cell_t l_Lean_IR_ToIR_lowerCode___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__14;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_IR_toIR___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_IR_toIR___closed__0 = (const lean_object*)&l_Lean_IR_toIR___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_IR_ToIR_M_run___redArg___closed__0, &l_Lean_IR_ToIR_M_run___redArg___closed__0_once, _init_l_Lean_IR_ToIR_M_run___redArg___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_obj_once(&l_Lean_IR_ToIR_M_run___redArg___closed__1, &l_Lean_IR_ToIR_M_run___redArg___closed__1_once, _init_l_Lean_IR_ToIR_M_run___redArg___closed__1);
v___x_9_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v___x_8_);
lean_ctor_set(v___x_9_, 2, v___x_7_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg(lean_object* v_x_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = lean_obj_once(&l_Lean_IR_ToIR_M_run___redArg___closed__2, &l_Lean_IR_ToIR_M_run___redArg___closed__2_once, _init_l_Lean_IR_ToIR_M_run___redArg___closed__2);
v___x_15_ = lean_st_mk_ref(v___x_14_);
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v___x_15_);
v___x_16_ = lean_apply_4(v_x_10_, v___x_15_, v_a_11_, v_a_12_, lean_box(0));
if (lean_obj_tag(v___x_16_) == 0)
{
lean_object* v_a_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_25_; 
v_a_17_ = lean_ctor_get(v___x_16_, 0);
v_isSharedCheck_25_ = !lean_is_exclusive(v___x_16_);
if (v_isSharedCheck_25_ == 0)
{
v___x_19_ = v___x_16_;
v_isShared_20_ = v_isSharedCheck_25_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_a_17_);
lean_dec(v___x_16_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_25_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_21_; lean_object* v___x_23_; 
v___x_21_ = lean_st_ref_get(v___x_15_);
lean_dec(v___x_15_);
lean_dec(v___x_21_);
if (v_isShared_20_ == 0)
{
v___x_23_ = v___x_19_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_a_17_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
else
{
lean_dec(v___x_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg___boxed(lean_object* v_x_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_IR_ToIR_M_run___redArg(v_x_26_, v_a_27_, v_a_28_);
lean_dec(v_a_28_);
lean_dec_ref(v_a_27_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object* v_00_u03b1_31_, lean_object* v_x_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_IR_ToIR_M_run___redArg(v_x_32_, v_a_33_, v_a_34_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___boxed(lean_object* v_00_u03b1_37_, lean_object* v_x_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_IR_ToIR_M_run(v_00_u03b1_37_, v_x_38_, v_a_39_, v_a_40_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1(lean_object* v_msg_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = l_Lean_IR_instInhabitedArg_default;
v___x_45_ = lean_panic_fn_borrowed(v___x_44_, v_msg_43_);
return v___x_45_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_49_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__2));
v___x_50_ = lean_unsigned_to_nat(11u);
v___x_51_ = lean_unsigned_to_nat(163u);
v___x_52_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__1));
v___x_53_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__0));
v___x_54_ = l_mkPanicMessageWithDecl(v___x_53_, v___x_52_, v___x_51_, v___x_50_, v___x_49_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(lean_object* v_a_55_, lean_object* v_x_56_){
_start:
{
if (lean_obj_tag(v_x_56_) == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3);
v___x_58_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1(v___x_57_);
return v___x_58_;
}
else
{
lean_object* v_key_59_; lean_object* v_value_60_; lean_object* v_tail_61_; uint8_t v___x_62_; 
v_key_59_ = lean_ctor_get(v_x_56_, 0);
v_value_60_ = lean_ctor_get(v_x_56_, 1);
v_tail_61_ = lean_ctor_get(v_x_56_, 2);
v___x_62_ = l_Lean_instBEqFVarId_beq(v_key_59_, v_a_55_);
if (v___x_62_ == 0)
{
v_x_56_ = v_tail_61_;
goto _start;
}
else
{
lean_inc(v_value_60_);
return v_value_60_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___boxed(lean_object* v_a_64_, lean_object* v_x_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(v_a_64_, v_x_65_);
lean_dec(v_x_65_);
lean_dec(v_a_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(lean_object* v_m_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_buckets_69_; lean_object* v___x_70_; uint64_t v___x_71_; uint64_t v___x_72_; uint64_t v___x_73_; uint64_t v_fold_74_; uint64_t v___x_75_; uint64_t v___x_76_; uint64_t v___x_77_; size_t v___x_78_; size_t v___x_79_; size_t v___x_80_; size_t v___x_81_; size_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_buckets_69_ = lean_ctor_get(v_m_67_, 1);
v___x_70_ = lean_array_get_size(v_buckets_69_);
v___x_71_ = l_Lean_instHashableFVarId_hash(v_a_68_);
v___x_72_ = 32ULL;
v___x_73_ = lean_uint64_shift_right(v___x_71_, v___x_72_);
v_fold_74_ = lean_uint64_xor(v___x_71_, v___x_73_);
v___x_75_ = 16ULL;
v___x_76_ = lean_uint64_shift_right(v_fold_74_, v___x_75_);
v___x_77_ = lean_uint64_xor(v_fold_74_, v___x_76_);
v___x_78_ = lean_uint64_to_usize(v___x_77_);
v___x_79_ = lean_usize_of_nat(v___x_70_);
v___x_80_ = ((size_t)1ULL);
v___x_81_ = lean_usize_sub(v___x_79_, v___x_80_);
v___x_82_ = lean_usize_land(v___x_78_, v___x_81_);
v___x_83_ = lean_array_uget_borrowed(v_buckets_69_, v___x_82_);
v___x_84_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(v_a_68_, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___boxed(lean_object* v_m_85_, lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(v_m_85_, v_a_86_);
lean_dec(v_a_86_);
lean_dec_ref(v_m_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg(lean_object* v_fvarId_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___x_91_; lean_object* v_vars_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_91_ = lean_st_ref_get(v_a_89_);
v_vars_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc_ref(v_vars_92_);
lean_dec(v___x_91_);
v___x_93_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(v_vars_92_, v_fvarId_88_);
lean_dec_ref(v_vars_92_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___boxed(lean_object* v_fvarId_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_95_, v_a_96_);
lean_dec(v_a_96_);
lean_dec(v_fvarId_95_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue(lean_object* v_fvarId_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_99_, v_a_100_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___boxed(lean_object* v_fvarId_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_IR_ToIR_getFVarValue(v_fvarId_105_, v_a_106_, v_a_107_, v_a_108_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec(v_fvarId_105_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0_spec__1(lean_object* v_msg_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_panic_fn_borrowed(v___x_112_, v_msg_111_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0(lean_object* v_a_114_, lean_object* v_x_115_){
_start:
{
if (lean_obj_tag(v_x_115_) == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3);
v___x_117_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0_spec__1(v___x_116_);
return v___x_117_;
}
else
{
lean_object* v_key_118_; lean_object* v_value_119_; lean_object* v_tail_120_; uint8_t v___x_121_; 
v_key_118_ = lean_ctor_get(v_x_115_, 0);
v_value_119_ = lean_ctor_get(v_x_115_, 1);
v_tail_120_ = lean_ctor_get(v_x_115_, 2);
v___x_121_ = l_Lean_instBEqFVarId_beq(v_key_118_, v_a_114_);
if (v___x_121_ == 0)
{
v_x_115_ = v_tail_120_;
goto _start;
}
else
{
lean_inc(v_value_119_);
return v_value_119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0___boxed(lean_object* v_a_123_, lean_object* v_x_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0(v_a_123_, v_x_124_);
lean_dec(v_x_124_);
lean_dec(v_a_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0(lean_object* v_m_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_buckets_128_; lean_object* v___x_129_; uint64_t v___x_130_; uint64_t v___x_131_; uint64_t v___x_132_; uint64_t v_fold_133_; uint64_t v___x_134_; uint64_t v___x_135_; uint64_t v___x_136_; size_t v___x_137_; size_t v___x_138_; size_t v___x_139_; size_t v___x_140_; size_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v_buckets_128_ = lean_ctor_get(v_m_126_, 1);
v___x_129_ = lean_array_get_size(v_buckets_128_);
v___x_130_ = l_Lean_instHashableFVarId_hash(v_a_127_);
v___x_131_ = 32ULL;
v___x_132_ = lean_uint64_shift_right(v___x_130_, v___x_131_);
v_fold_133_ = lean_uint64_xor(v___x_130_, v___x_132_);
v___x_134_ = 16ULL;
v___x_135_ = lean_uint64_shift_right(v_fold_133_, v___x_134_);
v___x_136_ = lean_uint64_xor(v_fold_133_, v___x_135_);
v___x_137_ = lean_uint64_to_usize(v___x_136_);
v___x_138_ = lean_usize_of_nat(v___x_129_);
v___x_139_ = ((size_t)1ULL);
v___x_140_ = lean_usize_sub(v___x_138_, v___x_139_);
v___x_141_ = lean_usize_land(v___x_137_, v___x_140_);
v___x_142_ = lean_array_uget_borrowed(v_buckets_128_, v___x_141_);
v___x_143_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0(v_a_127_, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0___boxed(lean_object* v_m_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0(v_m_144_, v_a_145_);
lean_dec(v_a_145_);
lean_dec_ref(v_m_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg(lean_object* v_fvarId_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___x_150_; lean_object* v_joinPoints_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_150_ = lean_st_ref_get(v_a_148_);
v_joinPoints_151_ = lean_ctor_get(v___x_150_, 1);
lean_inc_ref(v_joinPoints_151_);
lean_dec(v___x_150_);
v___x_152_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0(v_joinPoints_151_, v_fvarId_147_);
lean_dec_ref(v_joinPoints_151_);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg___boxed(lean_object* v_fvarId_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_154_, v_a_155_);
lean_dec(v_a_155_);
lean_dec(v_fvarId_154_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue(lean_object* v_fvarId_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_158_, v_a_159_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___boxed(lean_object* v_fvarId_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_IR_ToIR_getJoinPointValue(v_fvarId_164_, v_a_165_, v_a_166_, v_a_167_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec(v_fvarId_164_);
return v_res_169_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(lean_object* v_a_170_, lean_object* v_x_171_){
_start:
{
if (lean_obj_tag(v_x_171_) == 0)
{
uint8_t v___x_172_; 
v___x_172_ = 0;
return v___x_172_;
}
else
{
lean_object* v_key_173_; lean_object* v_tail_174_; uint8_t v___x_175_; 
v_key_173_ = lean_ctor_get(v_x_171_, 0);
v_tail_174_ = lean_ctor_get(v_x_171_, 2);
v___x_175_ = l_Lean_instBEqFVarId_beq(v_key_173_, v_a_170_);
if (v___x_175_ == 0)
{
v_x_171_ = v_tail_174_;
goto _start;
}
else
{
return v___x_175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_177_, lean_object* v_x_178_){
_start:
{
uint8_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_a_177_, v_x_178_);
lean_dec(v_x_178_);
lean_dec(v_a_177_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_181_, lean_object* v_x_182_){
_start:
{
if (lean_obj_tag(v_x_182_) == 0)
{
return v_x_181_;
}
else
{
lean_object* v_key_183_; lean_object* v_value_184_; lean_object* v_tail_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_208_; 
v_key_183_ = lean_ctor_get(v_x_182_, 0);
v_value_184_ = lean_ctor_get(v_x_182_, 1);
v_tail_185_ = lean_ctor_get(v_x_182_, 2);
v_isSharedCheck_208_ = !lean_is_exclusive(v_x_182_);
if (v_isSharedCheck_208_ == 0)
{
v___x_187_ = v_x_182_;
v_isShared_188_ = v_isSharedCheck_208_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_tail_185_);
lean_inc(v_value_184_);
lean_inc(v_key_183_);
lean_dec(v_x_182_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_208_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; uint64_t v___x_190_; uint64_t v___x_191_; uint64_t v___x_192_; uint64_t v_fold_193_; uint64_t v___x_194_; uint64_t v___x_195_; uint64_t v___x_196_; size_t v___x_197_; size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; size_t v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_189_ = lean_array_get_size(v_x_181_);
v___x_190_ = l_Lean_instHashableFVarId_hash(v_key_183_);
v___x_191_ = 32ULL;
v___x_192_ = lean_uint64_shift_right(v___x_190_, v___x_191_);
v_fold_193_ = lean_uint64_xor(v___x_190_, v___x_192_);
v___x_194_ = 16ULL;
v___x_195_ = lean_uint64_shift_right(v_fold_193_, v___x_194_);
v___x_196_ = lean_uint64_xor(v_fold_193_, v___x_195_);
v___x_197_ = lean_uint64_to_usize(v___x_196_);
v___x_198_ = lean_usize_of_nat(v___x_189_);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_sub(v___x_198_, v___x_199_);
v___x_201_ = lean_usize_land(v___x_197_, v___x_200_);
v___x_202_ = lean_array_uget_borrowed(v_x_181_, v___x_201_);
lean_inc(v___x_202_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 2, v___x_202_);
v___x_204_ = v___x_187_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_key_183_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_value_184_);
lean_ctor_set(v_reuseFailAlloc_207_, 2, v___x_202_);
v___x_204_ = v_reuseFailAlloc_207_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; 
v___x_205_ = lean_array_uset(v_x_181_, v___x_201_, v___x_204_);
v_x_181_ = v___x_205_;
v_x_182_ = v_tail_185_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(lean_object* v_i_209_, lean_object* v_source_210_, lean_object* v_target_211_){
_start:
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = lean_array_get_size(v_source_210_);
v___x_213_ = lean_nat_dec_lt(v_i_209_, v___x_212_);
if (v___x_213_ == 0)
{
lean_dec_ref(v_source_210_);
lean_dec(v_i_209_);
return v_target_211_;
}
else
{
lean_object* v_es_214_; lean_object* v___x_215_; lean_object* v_source_216_; lean_object* v_target_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_es_214_ = lean_array_fget(v_source_210_, v_i_209_);
v___x_215_ = lean_box(0);
v_source_216_ = lean_array_fset(v_source_210_, v_i_209_, v___x_215_);
v_target_217_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_211_, v_es_214_);
v___x_218_ = lean_unsigned_to_nat(1u);
v___x_219_ = lean_nat_add(v_i_209_, v___x_218_);
lean_dec(v_i_209_);
v_i_209_ = v___x_219_;
v_source_210_ = v_source_216_;
v_target_211_ = v_target_217_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(lean_object* v_data_221_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v_nbuckets_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_222_ = lean_array_get_size(v_data_221_);
v___x_223_ = lean_unsigned_to_nat(2u);
v_nbuckets_224_ = lean_nat_mul(v___x_222_, v___x_223_);
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_box(0);
v___x_227_ = lean_mk_array(v_nbuckets_224_, v___x_226_);
v___x_228_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(v___x_225_, v_data_221_, v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(lean_object* v_m_229_, lean_object* v_a_230_, lean_object* v_b_231_){
_start:
{
lean_object* v_size_232_; lean_object* v_buckets_233_; lean_object* v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v_fold_238_; uint64_t v___x_239_; uint64_t v___x_240_; uint64_t v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; lean_object* v_bkt_247_; uint8_t v___x_248_; 
v_size_232_ = lean_ctor_get(v_m_229_, 0);
v_buckets_233_ = lean_ctor_get(v_m_229_, 1);
v___x_234_ = lean_array_get_size(v_buckets_233_);
v___x_235_ = l_Lean_instHashableFVarId_hash(v_a_230_);
v___x_236_ = 32ULL;
v___x_237_ = lean_uint64_shift_right(v___x_235_, v___x_236_);
v_fold_238_ = lean_uint64_xor(v___x_235_, v___x_237_);
v___x_239_ = 16ULL;
v___x_240_ = lean_uint64_shift_right(v_fold_238_, v___x_239_);
v___x_241_ = lean_uint64_xor(v_fold_238_, v___x_240_);
v___x_242_ = lean_uint64_to_usize(v___x_241_);
v___x_243_ = lean_usize_of_nat(v___x_234_);
v___x_244_ = ((size_t)1ULL);
v___x_245_ = lean_usize_sub(v___x_243_, v___x_244_);
v___x_246_ = lean_usize_land(v___x_242_, v___x_245_);
v_bkt_247_ = lean_array_uget_borrowed(v_buckets_233_, v___x_246_);
v___x_248_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_a_230_, v_bkt_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_269_; 
lean_inc_ref(v_buckets_233_);
lean_inc(v_size_232_);
v_isSharedCheck_269_ = !lean_is_exclusive(v_m_229_);
if (v_isSharedCheck_269_ == 0)
{
lean_object* v_unused_270_; lean_object* v_unused_271_; 
v_unused_270_ = lean_ctor_get(v_m_229_, 1);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v_m_229_, 0);
lean_dec(v_unused_271_);
v___x_250_ = v_m_229_;
v_isShared_251_ = v_isSharedCheck_269_;
goto v_resetjp_249_;
}
else
{
lean_dec(v_m_229_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_269_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v_size_x27_253_; lean_object* v___x_254_; lean_object* v_buckets_x27_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_252_ = lean_unsigned_to_nat(1u);
v_size_x27_253_ = lean_nat_add(v_size_232_, v___x_252_);
lean_dec(v_size_232_);
lean_inc(v_bkt_247_);
v___x_254_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_254_, 0, v_a_230_);
lean_ctor_set(v___x_254_, 1, v_b_231_);
lean_ctor_set(v___x_254_, 2, v_bkt_247_);
v_buckets_x27_255_ = lean_array_uset(v_buckets_233_, v___x_246_, v___x_254_);
v___x_256_ = lean_unsigned_to_nat(4u);
v___x_257_ = lean_nat_mul(v_size_x27_253_, v___x_256_);
v___x_258_ = lean_unsigned_to_nat(3u);
v___x_259_ = lean_nat_div(v___x_257_, v___x_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_array_get_size(v_buckets_x27_255_);
v___x_261_ = lean_nat_dec_le(v___x_259_, v___x_260_);
lean_dec(v___x_259_);
if (v___x_261_ == 0)
{
lean_object* v_val_262_; lean_object* v___x_264_; 
v_val_262_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(v_buckets_x27_255_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 1, v_val_262_);
lean_ctor_set(v___x_250_, 0, v_size_x27_253_);
v___x_264_ = v___x_250_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_size_x27_253_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_val_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
else
{
lean_object* v___x_267_; 
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 1, v_buckets_x27_255_);
lean_ctor_set(v___x_250_, 0, v_size_x27_253_);
v___x_267_ = v___x_250_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_size_x27_253_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_buckets_x27_255_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
else
{
lean_dec(v_b_231_);
lean_dec(v_a_230_);
return v_m_229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object* v_fvarId_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_275_; lean_object* v_vars_276_; lean_object* v_joinPoints_277_; lean_object* v_nextId_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_291_; 
v___x_275_ = lean_st_ref_take(v_a_273_);
v_vars_276_ = lean_ctor_get(v___x_275_, 0);
v_joinPoints_277_ = lean_ctor_get(v___x_275_, 1);
v_nextId_278_ = lean_ctor_get(v___x_275_, 2);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_291_ == 0)
{
v___x_280_ = v___x_275_;
v_isShared_281_ = v_isSharedCheck_291_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_nextId_278_);
lean_inc(v_joinPoints_277_);
lean_inc(v_vars_276_);
lean_dec(v___x_275_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_291_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
lean_inc(v_nextId_278_);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v_nextId_278_);
v___x_283_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_276_, v_fvarId_272_, v___x_282_);
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = lean_nat_add(v_nextId_278_, v___x_284_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 2, v___x_285_);
lean_ctor_set(v___x_280_, 0, v___x_283_);
v___x_287_ = v___x_280_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_joinPoints_277_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v___x_285_);
v___x_287_ = v_reuseFailAlloc_290_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_st_ref_put(v_a_273_, v___x_287_);
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v_nextId_278_);
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg___boxed(lean_object* v_fvarId_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_292_, v_a_293_);
lean_dec(v_a_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object* v_fvarId_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_296_, v_a_297_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object* v_fvarId_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_IR_ToIR_bindVar(v_fvarId_302_, v_a_303_, v_a_304_, v_a_305_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0(lean_object* v_00_u03b2_308_, lean_object* v_m_309_, lean_object* v_a_310_, lean_object* v_b_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_m_309_, v_a_310_, v_b_311_);
return v___x_312_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(lean_object* v_00_u03b2_313_, lean_object* v_a_314_, lean_object* v_x_315_){
_start:
{
uint8_t v___x_316_; 
v___x_316_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_a_314_, v_x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_317_, lean_object* v_a_318_, lean_object* v_x_319_){
_start:
{
uint8_t v_res_320_; lean_object* v_r_321_; 
v_res_320_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(v_00_u03b2_317_, v_a_318_, v_x_319_);
lean_dec(v_x_319_);
lean_dec(v_a_318_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1(lean_object* v_00_u03b2_322_, lean_object* v_data_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(v_data_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_325_, lean_object* v_i_326_, lean_object* v_source_327_, lean_object* v_target_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(v_i_326_, v_source_327_, v_target_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_330_, lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_331_, v_x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object* v_fvarId_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_337_; lean_object* v_vars_338_; lean_object* v_joinPoints_339_; lean_object* v_nextId_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_352_; 
v___x_337_ = lean_st_ref_take(v_a_335_);
v_vars_338_ = lean_ctor_get(v___x_337_, 0);
v_joinPoints_339_ = lean_ctor_get(v___x_337_, 1);
v_nextId_340_ = lean_ctor_get(v___x_337_, 2);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_352_ == 0)
{
v___x_342_ = v___x_337_;
v_isShared_343_ = v_isSharedCheck_352_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_nextId_340_);
lean_inc(v_joinPoints_339_);
lean_inc(v_vars_338_);
lean_dec(v___x_337_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_352_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
lean_inc(v_nextId_340_);
v___x_344_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_joinPoints_339_, v_fvarId_334_, v_nextId_340_);
v___x_345_ = lean_unsigned_to_nat(1u);
v___x_346_ = lean_nat_add(v_nextId_340_, v___x_345_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 2, v___x_346_);
lean_ctor_set(v___x_342_, 1, v___x_344_);
v___x_348_ = v___x_342_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_vars_338_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v___x_346_);
v___x_348_ = v_reuseFailAlloc_351_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_st_ref_put(v_a_335_, v___x_348_);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v_nextId_340_);
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object* v_fvarId_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_353_, v_a_354_);
lean_dec(v_a_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object* v_fvarId_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_357_, v_a_358_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object* v_fvarId_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_IR_ToIR_bindJoinPoint(v_fvarId_363_, v_a_364_, v_a_365_, v_a_366_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object* v_fvarId_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_372_; lean_object* v_vars_373_; lean_object* v_joinPoints_374_; lean_object* v_nextId_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_387_; 
v___x_372_ = lean_st_ref_take(v_a_370_);
v_vars_373_ = lean_ctor_get(v___x_372_, 0);
v_joinPoints_374_ = lean_ctor_get(v___x_372_, 1);
v_nextId_375_ = lean_ctor_get(v___x_372_, 2);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_387_ == 0)
{
v___x_377_ = v___x_372_;
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_nextId_375_);
lean_inc(v_joinPoints_374_);
lean_inc(v_vars_373_);
lean_dec(v___x_372_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_379_ = lean_box(1);
v___x_380_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_373_, v_fvarId_369_, v___x_379_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_380_);
v___x_382_ = v___x_377_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_joinPoints_374_);
lean_ctor_set(v_reuseFailAlloc_386_, 2, v_nextId_375_);
v___x_382_ = v_reuseFailAlloc_386_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_383_ = lean_st_ref_put(v_a_370_, v___x_382_);
v___x_384_ = lean_box(0);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg___boxed(lean_object* v_fvarId_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_388_, v_a_389_);
lean_dec(v_a_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object* v_fvarId_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_392_, v_a_393_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object* v_fvarId_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_IR_ToIR_bindErased(v_fvarId_398_, v_a_399_, v_a_400_, v_a_401_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
return v_res_403_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_404_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__0, &l_Lean_IR_ToIR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__1, &l_Lean_IR_ToIR_addDecl___redArg___closed__1_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object* v_d_409_, lean_object* v_a_410_){
_start:
{
lean_object* v___x_412_; lean_object* v_env_413_; lean_object* v_nextMacroScope_414_; lean_object* v_ngen_415_; lean_object* v_auxDeclNGen_416_; lean_object* v_traceState_417_; lean_object* v_messages_418_; lean_object* v_infoState_419_; lean_object* v_snapshotTasks_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_436_; 
v___x_412_ = lean_st_ref_take(v_a_410_);
v_env_413_ = lean_ctor_get(v___x_412_, 0);
v_nextMacroScope_414_ = lean_ctor_get(v___x_412_, 1);
v_ngen_415_ = lean_ctor_get(v___x_412_, 2);
v_auxDeclNGen_416_ = lean_ctor_get(v___x_412_, 3);
v_traceState_417_ = lean_ctor_get(v___x_412_, 4);
v_messages_418_ = lean_ctor_get(v___x_412_, 6);
v_infoState_419_ = lean_ctor_get(v___x_412_, 7);
v_snapshotTasks_420_ = lean_ctor_get(v___x_412_, 8);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_436_ == 0)
{
lean_object* v_unused_437_; 
v_unused_437_ = lean_ctor_get(v___x_412_, 5);
lean_dec(v_unused_437_);
v___x_422_ = v___x_412_;
v_isShared_423_ = v_isSharedCheck_436_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_snapshotTasks_420_);
lean_inc(v_infoState_419_);
lean_inc(v_messages_418_);
lean_inc(v_traceState_417_);
lean_inc(v_auxDeclNGen_416_);
lean_inc(v_ngen_415_);
lean_inc(v_nextMacroScope_414_);
lean_inc(v_env_413_);
lean_dec(v___x_412_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_436_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v_toEnvExtension_425_; lean_object* v_asyncMode_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_424_ = l_Lean_IR_declMapExt;
v_toEnvExtension_425_ = lean_ctor_get(v___x_424_, 0);
v_asyncMode_426_ = lean_ctor_get(v_toEnvExtension_425_, 2);
v___x_427_ = lean_box(0);
v___x_428_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_424_, v_env_413_, v_d_409_, v_asyncMode_426_, v___x_427_);
v___x_429_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__2, &l_Lean_IR_ToIR_addDecl___redArg___closed__2_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 5, v___x_429_);
lean_ctor_set(v___x_422_, 0, v___x_428_);
v___x_431_ = v___x_422_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_nextMacroScope_414_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_ngen_415_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_auxDeclNGen_416_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v_traceState_417_);
lean_ctor_set(v_reuseFailAlloc_435_, 5, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_435_, 6, v_messages_418_);
lean_ctor_set(v_reuseFailAlloc_435_, 7, v_infoState_419_);
lean_ctor_set(v_reuseFailAlloc_435_, 8, v_snapshotTasks_420_);
v___x_431_ = v_reuseFailAlloc_435_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = lean_st_ref_put(v_a_410_, v___x_431_);
v___x_433_ = lean_box(0);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object* v_d_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_438_, v_a_439_);
lean_dec(v_a_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object* v_d_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_442_, v_a_445_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object* v_d_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_IR_ToIR_addDecl(v_d_448_, v_a_449_, v_a_450_, v_a_451_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object* v_v_454_){
_start:
{
switch(lean_obj_tag(v_v_454_))
{
case 0:
{
lean_object* v_val_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_469_; 
v_val_455_ = lean_ctor_get(v_v_454_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v_v_454_);
if (v_isSharedCheck_469_ == 0)
{
v___x_457_ = v_v_454_;
v_isShared_458_ = v_isSharedCheck_469_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_val_455_);
lean_dec(v_v_454_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_469_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___y_460_; lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = lean_cstr_to_nat("4294967296");
v___x_466_ = lean_nat_dec_lt(v_val_455_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
v___x_467_ = lean_box(8);
v___y_460_ = v___x_467_;
goto v___jp_459_;
}
else
{
lean_object* v___x_468_; 
v___x_468_ = lean_box(12);
v___y_460_ = v___x_468_;
goto v___jp_459_;
}
v___jp_459_:
{
lean_object* v___x_462_; 
if (v_isShared_458_ == 0)
{
v___x_462_ = v___x_457_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_val_455_);
v___x_462_ = v_reuseFailAlloc_464_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_463_; 
lean_inc(v___y_460_);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v___y_460_);
return v___x_463_;
}
}
}
}
case 1:
{
lean_object* v_val_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_479_; 
v_val_470_ = lean_ctor_get(v_v_454_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v_v_454_);
if (v_isSharedCheck_479_ == 0)
{
v___x_472_ = v_v_454_;
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_val_470_);
lean_dec(v_v_454_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_val_470_);
v___x_475_ = v_reuseFailAlloc_478_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_box(7);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
return v___x_477_;
}
}
}
case 2:
{
uint8_t v_val_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_val_480_ = lean_ctor_get_uint8(v_v_454_, 0);
lean_dec_ref_known(v_v_454_, 0);
v___x_481_ = lean_uint8_to_nat(v_val_480_);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
v___x_483_ = lean_box(1);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_482_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
return v___x_484_;
}
case 3:
{
uint16_t v_val_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_val_485_ = lean_ctor_get_uint16(v_v_454_, 0);
lean_dec_ref_known(v_v_454_, 0);
v___x_486_ = lean_uint16_to_nat(v_val_485_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
v___x_488_ = lean_box(2);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
return v___x_489_;
}
case 4:
{
uint32_t v_val_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_val_490_ = lean_ctor_get_uint32(v_v_454_, 0);
lean_dec_ref_known(v_v_454_, 0);
v___x_491_ = lean_uint32_to_nat(v_val_490_);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
v___x_493_ = lean_box(3);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
return v___x_494_;
}
case 5:
{
uint64_t v_val_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_val_495_ = lean_ctor_get_uint64(v_v_454_, 0);
lean_dec_ref_known(v_v_454_, 0);
v___x_496_ = lean_uint64_to_nat(v_val_495_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
v___x_498_ = lean_box(4);
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
return v___x_499_;
}
default: 
{
uint64_t v_val_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_val_500_ = lean_ctor_get_uint64(v_v_454_, 0);
lean_dec_ref_known(v_v_454_, 0);
v___x_501_ = lean_uint64_to_nat(v_val_500_);
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
v___x_503_ = lean_box(5);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_502_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
if (lean_obj_tag(v_a_505_) == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_box(1);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
else
{
lean_object* v_fvarId_510_; lean_object* v___x_511_; 
v_fvarId_510_ = lean_ctor_get(v_a_505_, 0);
v___x_511_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_510_, v_a_506_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_512_, v_a_513_);
lean_dec(v_a_513_);
lean_dec(v_a_512_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_516_, v_a_517_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_IR_ToIR_lowerArg(v_a_522_, v_a_523_, v_a_524_, v_a_525_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec(v_a_522_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg(lean_object* v_p_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_fvarId_531_; lean_object* v_type_532_; uint8_t v_borrow_533_; lean_object* v___x_534_; lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_548_; 
v_fvarId_531_ = lean_ctor_get(v_p_528_, 0);
lean_inc(v_fvarId_531_);
v_type_532_ = lean_ctor_get(v_p_528_, 2);
lean_inc_ref(v_type_532_);
v_borrow_533_ = lean_ctor_get_uint8(v_p_528_, sizeof(void*)*3);
lean_dec_ref(v_p_528_);
v___x_534_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_531_, v_a_529_);
v_a_535_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_548_ == 0)
{
v___x_537_ = v___x_534_;
v_isShared_538_ = v_isSharedCheck_548_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_548_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; uint8_t v___y_541_; 
v___x_539_ = l_Lean_IR_toIRType(v_type_532_);
lean_dec_ref(v_type_532_);
if (v_borrow_533_ == 0)
{
v___y_541_ = v_borrow_533_;
goto v___jp_540_;
}
else
{
uint8_t v___x_546_; 
v___x_546_ = l_Lean_IR_IRType_isScalar(v___x_539_);
if (v___x_546_ == 0)
{
v___y_541_ = v_borrow_533_;
goto v___jp_540_;
}
else
{
uint8_t v___x_547_; 
v___x_547_ = 0;
v___y_541_ = v___x_547_;
goto v___jp_540_;
}
}
v___jp_540_:
{
lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_542_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_542_, 0, v_a_535_);
lean_ctor_set(v___x_542_, 1, v___x_539_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*2, v___y_541_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_542_);
v___x_544_ = v___x_537_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg___boxed(lean_object* v_p_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_549_, v_a_550_);
lean_dec(v_a_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object* v_p_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_553_, v_a_554_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object* v_p_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_IR_ToIR_lowerParam(v_p_559_, v_a_560_, v_a_561_, v_a_562_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCtorInfo(lean_object* v_i_565_){
_start:
{
lean_object* v_name_566_; lean_object* v_cidx_567_; lean_object* v_size_568_; lean_object* v_usize_569_; lean_object* v_ssize_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
v_name_566_ = lean_ctor_get(v_i_565_, 0);
v_cidx_567_ = lean_ctor_get(v_i_565_, 1);
v_size_568_ = lean_ctor_get(v_i_565_, 2);
v_usize_569_ = lean_ctor_get(v_i_565_, 3);
v_ssize_570_ = lean_ctor_get(v_i_565_, 4);
v_isSharedCheck_577_ = !lean_is_exclusive(v_i_565_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v_i_565_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_ssize_570_);
lean_inc(v_usize_569_);
lean_inc(v_size_568_);
lean_inc(v_cidx_567_);
lean_inc(v_name_566_);
lean_dec(v_i_565_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_name_566_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_cidx_567_);
lean_ctor_set(v_reuseFailAlloc_576_, 2, v_size_568_);
lean_ctor_set(v_reuseFailAlloc_576_, 3, v_usize_569_);
lean_ctor_set(v_reuseFailAlloc_576_, 4, v_ssize_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0(void){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_instMonadEIO(lean_box(0));
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(lean_object* v_msg_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v_toApplicative_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_620_; 
v___x_586_ = lean_obj_once(&l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0, &l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0_once, _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0);
v___x_587_ = l_StateRefT_x27_instMonad___redArg(v___x_586_);
v_toApplicative_588_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v___x_587_, 1);
lean_dec(v_unused_621_);
v___x_590_ = v___x_587_;
v_isShared_591_ = v_isSharedCheck_620_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_toApplicative_588_);
lean_dec(v___x_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_620_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v_toFunctor_592_; lean_object* v_toSeq_593_; lean_object* v_toSeqLeft_594_; lean_object* v_toSeqRight_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_618_; 
v_toFunctor_592_ = lean_ctor_get(v_toApplicative_588_, 0);
v_toSeq_593_ = lean_ctor_get(v_toApplicative_588_, 2);
v_toSeqLeft_594_ = lean_ctor_get(v_toApplicative_588_, 3);
v_toSeqRight_595_ = lean_ctor_get(v_toApplicative_588_, 4);
v_isSharedCheck_618_ = !lean_is_exclusive(v_toApplicative_588_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; 
v_unused_619_ = lean_ctor_get(v_toApplicative_588_, 1);
lean_dec(v_unused_619_);
v___x_597_ = v_toApplicative_588_;
v_isShared_598_ = v_isSharedCheck_618_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_toSeqRight_595_);
lean_inc(v_toSeqLeft_594_);
lean_inc(v_toSeq_593_);
lean_inc(v_toFunctor_592_);
lean_dec(v_toApplicative_588_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_618_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___f_599_; lean_object* v___f_600_; lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___x_603_; lean_object* v___f_604_; lean_object* v___f_605_; lean_object* v___f_606_; lean_object* v___x_608_; 
v___f_599_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1));
v___f_600_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2));
lean_inc_ref(v_toFunctor_592_);
v___f_601_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_601_, 0, v_toFunctor_592_);
v___f_602_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_602_, 0, v_toFunctor_592_);
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v___f_601_);
lean_ctor_set(v___x_603_, 1, v___f_602_);
v___f_604_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_604_, 0, v_toSeqRight_595_);
v___f_605_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_605_, 0, v_toSeqLeft_594_);
v___f_606_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_606_, 0, v_toSeq_593_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 4, v___f_604_);
lean_ctor_set(v___x_597_, 3, v___f_605_);
lean_ctor_set(v___x_597_, 2, v___f_606_);
lean_ctor_set(v___x_597_, 1, v___f_599_);
lean_ctor_set(v___x_597_, 0, v___x_603_);
v___x_608_ = v___x_597_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v___f_599_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v___f_606_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v___f_605_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v___f_604_);
v___x_608_ = v_reuseFailAlloc_617_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_610_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v___f_600_);
lean_ctor_set(v___x_590_, 0, v___x_608_);
v___x_610_ = v___x_590_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v___f_600_);
v___x_610_ = v_reuseFailAlloc_616_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_8618__overap_614_; lean_object* v___x_615_; 
v___x_611_ = l_StateRefT_x27_instMonad___redArg(v___x_610_);
v___x_612_ = l_Lean_IR_instInhabitedFnBody_default__1;
v___x_613_ = l_instInhabitedOfMonad___redArg(v___x_611_, v___x_612_);
v___x_8618__overap_614_ = lean_panic_fn_borrowed(v___x_613_, v_msg_581_);
lean_dec(v___x_613_);
lean_inc(v___y_584_);
lean_inc_ref(v___y_583_);
lean_inc(v___y_582_);
v___x_615_ = lean_apply_4(v___x_8618__overap_614_, v___y_582_, v___y_583_, v___y_584_, lean_box(0));
return v___x_615_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object* v_msg_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v_msg_622_, v___y_623_, v___y_624_, v___y_625_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(size_t v_sz_628_, size_t v_i_629_, lean_object* v_bs_630_, lean_object* v___y_631_){
_start:
{
uint8_t v___x_633_; 
v___x_633_ = lean_usize_dec_lt(v_i_629_, v_sz_628_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; 
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v_bs_630_);
return v___x_634_;
}
else
{
lean_object* v_v_635_; lean_object* v___x_636_; 
v_v_635_ = lean_array_uget_borrowed(v_bs_630_, v_i_629_);
v___x_636_ = l_Lean_IR_ToIR_lowerArg___redArg(v_v_635_, v___y_631_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_638_; lean_object* v_bs_x27_639_; size_t v___x_640_; size_t v___x_641_; lean_object* v___x_642_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___x_636_, 1);
v___x_638_ = lean_unsigned_to_nat(0u);
v_bs_x27_639_ = lean_array_uset(v_bs_630_, v_i_629_, v___x_638_);
v___x_640_ = ((size_t)1ULL);
v___x_641_ = lean_usize_add(v_i_629_, v___x_640_);
v___x_642_ = lean_array_uset(v_bs_x27_639_, v_i_629_, v_a_637_);
v_i_629_ = v___x_641_;
v_bs_630_ = v___x_642_;
goto _start;
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec_ref(v_bs_630_);
v_a_644_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_636_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_636_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object* v_sz_652_, lean_object* v_i_653_, lean_object* v_bs_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
size_t v_sz_boxed_657_; size_t v_i_boxed_658_; lean_object* v_res_659_; 
v_sz_boxed_657_ = lean_unbox_usize(v_sz_652_);
lean_dec(v_sz_652_);
v_i_boxed_658_ = lean_unbox_usize(v_i_653_);
lean_dec(v_i_653_);
v_res_659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_boxed_657_, v_i_boxed_658_, v_bs_654_, v___y_655_);
lean_dec(v___y_655_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(size_t v_sz_660_, size_t v_i_661_, lean_object* v_bs_662_, lean_object* v___y_663_){
_start:
{
uint8_t v___x_665_; 
v___x_665_ = lean_usize_dec_lt(v_i_661_, v_sz_660_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v_bs_662_);
return v___x_666_;
}
else
{
lean_object* v_v_667_; lean_object* v___x_668_; 
v_v_667_ = lean_array_uget_borrowed(v_bs_662_, v_i_661_);
lean_inc(v_v_667_);
v___x_668_ = l_Lean_IR_ToIR_lowerParam___redArg(v_v_667_, v___y_663_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_670_; lean_object* v_bs_x27_671_; size_t v___x_672_; size_t v___x_673_; lean_object* v___x_674_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v___x_670_ = lean_unsigned_to_nat(0u);
v_bs_x27_671_ = lean_array_uset(v_bs_662_, v_i_661_, v___x_670_);
v___x_672_ = ((size_t)1ULL);
v___x_673_ = lean_usize_add(v_i_661_, v___x_672_);
v___x_674_ = lean_array_uset(v_bs_x27_671_, v_i_661_, v_a_669_);
v_i_661_ = v___x_673_;
v_bs_662_ = v___x_674_;
goto _start;
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec_ref(v_bs_662_);
v_a_676_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_668_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_668_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg___boxed(lean_object* v_sz_684_, lean_object* v_i_685_, lean_object* v_bs_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
size_t v_sz_boxed_689_; size_t v_i_boxed_690_; lean_object* v_res_691_; 
v_sz_boxed_689_ = lean_unbox_usize(v_sz_684_);
lean_dec(v_sz_684_);
v_i_boxed_690_ = lean_unbox_usize(v_i_685_);
lean_dec(v_i_685_);
v_res_691_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_boxed_689_, v_i_boxed_690_, v_bs_686_, v___y_687_);
lean_dec(v___y_687_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2(lean_object* v_i_692_, lean_object* v_continueLet_693_, lean_object* v_var_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_699_, 0, v_i_692_);
lean_ctor_set(v___x_699_, 1, v_var_694_);
lean_inc(v___y_697_);
lean_inc_ref(v___y_696_);
lean_inc(v___y_695_);
v___x_700_ = lean_apply_5(v_continueLet_693_, v___x_699_, v___y_695_, v___y_696_, v___y_697_, lean_box(0));
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2___boxed(lean_object* v_i_701_, lean_object* v_continueLet_702_, lean_object* v_var_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_IR_ToIR_lowerLet___lam__2(v_i_701_, v_continueLet_702_, v_var_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4(lean_object* v_n_709_, lean_object* v_offset_710_, lean_object* v_continueLet_711_, lean_object* v_var_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_717_, 0, v_n_709_);
lean_ctor_set(v___x_717_, 1, v_offset_710_);
lean_ctor_set(v___x_717_, 2, v_var_712_);
lean_inc(v___y_715_);
lean_inc_ref(v___y_714_);
lean_inc(v___y_713_);
v___x_718_ = lean_apply_5(v_continueLet_711_, v___x_717_, v___y_713_, v___y_714_, v___y_715_, lean_box(0));
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4___boxed(lean_object* v_n_719_, lean_object* v_offset_720_, lean_object* v_continueLet_721_, lean_object* v_var_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_IR_ToIR_lowerLet___lam__4(v_n_719_, v_offset_720_, v_continueLet_721_, v_var_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5(lean_object* v_n_728_, lean_object* v_continueLet_729_, lean_object* v_var_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_735_, 0, v_n_728_);
lean_ctor_set(v___x_735_, 1, v_var_730_);
lean_inc(v___y_733_);
lean_inc_ref(v___y_732_);
lean_inc(v___y_731_);
v___x_736_ = lean_apply_5(v_continueLet_729_, v___x_735_, v___y_731_, v___y_732_, v___y_733_, lean_box(0));
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5___boxed(lean_object* v_n_737_, lean_object* v_continueLet_738_, lean_object* v_var_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_IR_ToIR_lowerLet___lam__5(v_n_737_, v_continueLet_738_, v_var_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8(lean_object* v_continueLet_745_, lean_object* v_var_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_751_, 0, v_var_746_);
lean_inc(v___y_749_);
lean_inc_ref(v___y_748_);
lean_inc(v___y_747_);
v___x_752_ = lean_apply_5(v_continueLet_745_, v___x_751_, v___y_747_, v___y_748_, v___y_749_, lean_box(0));
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8___boxed(lean_object* v_continueLet_753_, lean_object* v_var_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_IR_ToIR_lowerLet___lam__8(v_continueLet_753_, v_var_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3(lean_object* v_i_760_, lean_object* v_continueLet_761_, lean_object* v_var_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_767_, 0, v_i_760_);
lean_ctor_set(v___x_767_, 1, v_var_762_);
lean_inc(v___y_765_);
lean_inc_ref(v___y_764_);
lean_inc(v___y_763_);
v___x_768_ = lean_apply_5(v_continueLet_761_, v___x_767_, v___y_763_, v___y_764_, v___y_765_, lean_box(0));
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3___boxed(lean_object* v_i_769_, lean_object* v_continueLet_770_, lean_object* v_var_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_IR_ToIR_lowerLet___lam__3(v_i_769_, v_continueLet_770_, v_var_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7(lean_object* v_ty_777_, lean_object* v_continueLet_778_, lean_object* v_var_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_784_ = l_Lean_IR_toIRType(v_ty_777_);
v___x_785_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set(v___x_785_, 1, v_var_779_);
lean_inc(v___y_782_);
lean_inc_ref(v___y_781_);
lean_inc(v___y_780_);
v___x_786_ = lean_apply_5(v_continueLet_778_, v___x_785_, v___y_780_, v___y_781_, v___y_782_, lean_box(0));
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7___boxed(lean_object* v_ty_787_, lean_object* v_continueLet_788_, lean_object* v_var_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_IR_ToIR_lowerLet___lam__7(v_ty_787_, v_continueLet_788_, v_var_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v_ty_787_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6(lean_object* v_args_795_, lean_object* v_i_796_, uint8_t v_updateHeader_797_, lean_object* v_continueLet_798_, lean_object* v_var_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
size_t v_sz_804_; size_t v___x_805_; lean_object* v___x_806_; 
v_sz_804_ = lean_array_size(v_args_795_);
v___x_805_ = ((size_t)0ULL);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_804_, v___x_805_, v_args_795_, v___y_800_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v_name_808_; lean_object* v_cidx_809_; lean_object* v_size_810_; lean_object* v_usize_811_; lean_object* v_ssize_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_821_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref_known(v___x_806_, 1);
v_name_808_ = lean_ctor_get(v_i_796_, 0);
v_cidx_809_ = lean_ctor_get(v_i_796_, 1);
v_size_810_ = lean_ctor_get(v_i_796_, 2);
v_usize_811_ = lean_ctor_get(v_i_796_, 3);
v_ssize_812_ = lean_ctor_get(v_i_796_, 4);
v_isSharedCheck_821_ = !lean_is_exclusive(v_i_796_);
if (v_isSharedCheck_821_ == 0)
{
v___x_814_ = v_i_796_;
v_isShared_815_ = v_isSharedCheck_821_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_ssize_812_);
lean_inc(v_usize_811_);
lean_inc(v_size_810_);
lean_inc(v_cidx_809_);
lean_inc(v_name_808_);
lean_dec(v_i_796_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_821_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_name_808_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_cidx_809_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v_size_810_);
lean_ctor_set(v_reuseFailAlloc_820_, 3, v_usize_811_);
lean_ctor_set(v_reuseFailAlloc_820_, 4, v_ssize_812_);
v___x_817_ = v_reuseFailAlloc_820_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v___x_818_, 0, v_var_799_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
lean_ctor_set(v___x_818_, 2, v_a_807_);
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*3, v_updateHeader_797_);
lean_inc(v___y_802_);
lean_inc_ref(v___y_801_);
lean_inc(v___y_800_);
v___x_819_ = lean_apply_5(v_continueLet_798_, v___x_818_, v___y_800_, v___y_801_, v___y_802_, lean_box(0));
return v___x_819_;
}
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec(v_var_799_);
lean_dec_ref(v_continueLet_798_);
lean_dec_ref(v_i_796_);
v_a_822_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_806_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_806_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6___boxed(lean_object* v_args_830_, lean_object* v_i_831_, lean_object* v_updateHeader_832_, lean_object* v_continueLet_833_, lean_object* v_var_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
uint8_t v_updateHeader_9660__boxed_839_; lean_object* v_res_840_; 
v_updateHeader_9660__boxed_839_ = lean_unbox(v_updateHeader_832_);
v_res_840_ = l_Lean_IR_ToIR_lowerLet___lam__6(v_args_830_, v_i_831_, v_updateHeader_9660__boxed_839_, v_continueLet_833_, v_var_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9(lean_object* v_continueLet_841_, lean_object* v_var_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_847_, 0, v_var_842_);
lean_inc(v___y_845_);
lean_inc_ref(v___y_844_);
lean_inc(v___y_843_);
v___x_848_ = lean_apply_5(v_continueLet_841_, v___x_847_, v___y_843_, v___y_844_, v___y_845_, lean_box(0));
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9___boxed(lean_object* v_continueLet_849_, lean_object* v_var_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_IR_ToIR_lowerLet___lam__9(v_continueLet_849_, v_var_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1(lean_object* v_args_856_, lean_object* v_continueLet_857_, lean_object* v_id_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
size_t v_sz_863_; size_t v___x_864_; lean_object* v___x_865_; 
v_sz_863_ = lean_array_size(v_args_856_);
v___x_864_ = ((size_t)0ULL);
v___x_865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_863_, v___x_864_, v_args_856_, v___y_859_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref_known(v___x_865_, 1);
v___x_867_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_867_, 0, v_id_858_);
lean_ctor_set(v___x_867_, 1, v_a_866_);
lean_inc(v___y_861_);
lean_inc_ref(v___y_860_);
lean_inc(v___y_859_);
v___x_868_ = lean_apply_5(v_continueLet_857_, v___x_867_, v___y_859_, v___y_860_, v___y_861_, lean_box(0));
return v___x_868_;
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec(v_id_858_);
lean_dec_ref(v_continueLet_857_);
v_a_869_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_865_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_865_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1___boxed(lean_object* v_args_877_, lean_object* v_continueLet_878_, lean_object* v_id_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_IR_ToIR_lowerLet___lam__1(v_args_877_, v_continueLet_878_, v_id_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0(lean_object* v_fvarId_885_, lean_object* v_k_886_, lean_object* v_type_887_, lean_object* v_e_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_885_, v___y_889_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_895_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
lean_dec_ref_known(v___x_893_, 1);
v___x_895_ = l_Lean_IR_ToIR_lowerCode(v_k_886_, v___y_889_, v___y_890_, v___y_891_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_904_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_904_ == 0)
{
v___x_898_ = v___x_895_;
v_isShared_899_ = v_isSharedCheck_904_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_895_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_904_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_900_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_900_, 0, v_a_894_);
lean_ctor_set(v___x_900_, 1, v_type_887_);
lean_ctor_set(v___x_900_, 2, v_e_888_);
lean_ctor_set(v___x_900_, 3, v_a_896_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_900_);
v___x_902_ = v___x_898_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
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
lean_dec(v_a_894_);
lean_dec_ref(v_e_888_);
lean_dec(v_type_887_);
return v___x_895_;
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec_ref(v_e_888_);
lean_dec(v_type_887_);
lean_dec_ref(v_k_886_);
v_a_905_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_893_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_893_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object* v_fvarId_913_, lean_object* v_k_914_, lean_object* v_type_915_, lean_object* v_e_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_913_, v_k_914_, v_type_915_, v_e_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(lean_object* v_decl_922_, lean_object* v_k_923_, lean_object* v_fvarId_924_, lean_object* v_f_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_924_, v_a_926_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
lean_dec_ref_known(v___x_930_, 1);
if (lean_obj_tag(v_a_931_) == 0)
{
lean_object* v_id_932_; lean_object* v___x_933_; 
lean_dec_ref(v_k_923_);
lean_dec_ref(v_decl_922_);
v_id_932_ = lean_ctor_get(v_a_931_, 0);
lean_inc(v_id_932_);
lean_dec_ref_known(v_a_931_, 1);
lean_inc(v_a_928_);
lean_inc_ref(v_a_927_);
lean_inc(v_a_926_);
v___x_933_ = lean_apply_5(v_f_925_, v_id_932_, v_a_926_, v_a_927_, v_a_928_, lean_box(0));
return v___x_933_;
}
else
{
lean_object* v___x_934_; 
lean_dec_ref(v_f_925_);
v___x_934_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_922_, v_k_923_, v_a_926_, v_a_927_, v_a_928_);
return v___x_934_;
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec_ref(v_f_925_);
lean_dec_ref(v_k_923_);
lean_dec_ref(v_decl_922_);
v_a_935_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_930_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_930_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object* v_decl_943_, lean_object* v_k_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_fvarId_949_; lean_object* v_type_950_; lean_object* v_value_951_; lean_object* v_type_952_; lean_object* v_continueLet_953_; 
v_fvarId_949_ = lean_ctor_get(v_decl_943_, 0);
v_type_950_ = lean_ctor_get(v_decl_943_, 2);
v_value_951_ = lean_ctor_get(v_decl_943_, 3);
lean_inc(v_value_951_);
v_type_952_ = l_Lean_IR_toIRType(v_type_950_);
lean_inc(v_type_952_);
lean_inc_ref(v_k_944_);
lean_inc(v_fvarId_949_);
v_continueLet_953_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 8, 3);
lean_closure_set(v_continueLet_953_, 0, v_fvarId_949_);
lean_closure_set(v_continueLet_953_, 1, v_k_944_);
lean_closure_set(v_continueLet_953_, 2, v_type_952_);
switch(lean_obj_tag(v_value_951_))
{
case 0:
{
lean_object* v_value_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_964_; 
lean_inc(v_fvarId_949_);
lean_dec_ref(v_continueLet_953_);
lean_dec_ref(v_decl_943_);
v_value_954_ = lean_ctor_get(v_value_951_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v_value_951_);
if (v_isSharedCheck_964_ == 0)
{
v___x_956_ = v_value_951_;
v_isShared_957_ = v_isSharedCheck_964_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_value_954_);
lean_dec(v_value_951_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_964_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v_fst_959_; lean_object* v___x_961_; 
v___x_958_ = l_Lean_IR_ToIR_lowerLitValue(v_value_954_);
v_fst_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_fst_959_);
lean_dec_ref(v___x_958_);
if (v_isShared_957_ == 0)
{
lean_ctor_set_tag(v___x_956_, 11);
lean_ctor_set(v___x_956_, 0, v_fst_959_);
v___x_961_ = v___x_956_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_fst_959_);
v___x_961_ = v_reuseFailAlloc_963_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_949_, v_k_944_, v_type_952_, v___x_961_, v_a_945_, v_a_946_, v_a_947_);
return v___x_962_;
}
}
}
case 1:
{
lean_object* v___x_965_; 
lean_dec_ref(v_continueLet_953_);
lean_dec(v_type_952_);
v___x_965_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_943_, v_k_944_, v_a_945_, v_a_946_, v_a_947_);
return v___x_965_;
}
case 4:
{
lean_object* v_fvarId_966_; lean_object* v_args_967_; lean_object* v___f_968_; lean_object* v___x_969_; 
lean_dec(v_type_952_);
v_fvarId_966_ = lean_ctor_get(v_value_951_, 0);
lean_inc(v_fvarId_966_);
v_args_967_ = lean_ctor_get(v_value_951_, 1);
lean_inc_ref(v_args_967_);
lean_dec_ref_known(v_value_951_, 2);
v___f_968_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__1___boxed), 7, 2);
lean_closure_set(v___f_968_, 0, v_args_967_);
lean_closure_set(v___f_968_, 1, v_continueLet_953_);
v___x_969_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_943_, v_k_944_, v_fvarId_966_, v___f_968_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_fvarId_966_);
return v___x_969_;
}
case 5:
{
lean_object* v_i_970_; lean_object* v_args_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_1003_; 
lean_inc(v_fvarId_949_);
lean_dec_ref(v_continueLet_953_);
lean_dec_ref(v_decl_943_);
v_i_970_ = lean_ctor_get(v_value_951_, 0);
v_args_971_ = lean_ctor_get(v_value_951_, 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_value_951_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_973_ = v_value_951_;
v_isShared_974_ = v_isSharedCheck_1003_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_args_971_);
lean_inc(v_i_970_);
lean_dec(v_value_951_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_1003_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
size_t v_sz_975_; size_t v___x_976_; lean_object* v___x_977_; 
v_sz_975_ = lean_array_size(v_args_971_);
v___x_976_ = ((size_t)0ULL);
v___x_977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_975_, v___x_976_, v_args_971_, v_a_945_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v_name_979_; lean_object* v_cidx_980_; lean_object* v_size_981_; lean_object* v_usize_982_; lean_object* v_ssize_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_994_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 1);
v_name_979_ = lean_ctor_get(v_i_970_, 0);
v_cidx_980_ = lean_ctor_get(v_i_970_, 1);
v_size_981_ = lean_ctor_get(v_i_970_, 2);
v_usize_982_ = lean_ctor_get(v_i_970_, 3);
v_ssize_983_ = lean_ctor_get(v_i_970_, 4);
v_isSharedCheck_994_ = !lean_is_exclusive(v_i_970_);
if (v_isSharedCheck_994_ == 0)
{
v___x_985_ = v_i_970_;
v_isShared_986_ = v_isSharedCheck_994_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_ssize_983_);
lean_inc(v_usize_982_);
lean_inc(v_size_981_);
lean_inc(v_cidx_980_);
lean_inc(v_name_979_);
lean_dec(v_i_970_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_994_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_name_979_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_cidx_980_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_size_981_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v_usize_982_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v_ssize_983_);
v___x_988_ = v_reuseFailAlloc_993_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_990_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set_tag(v___x_973_, 0);
lean_ctor_set(v___x_973_, 1, v_a_978_);
lean_ctor_set(v___x_973_, 0, v___x_988_);
v___x_990_ = v___x_973_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_a_978_);
v___x_990_ = v_reuseFailAlloc_992_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_949_, v_k_944_, v_type_952_, v___x_990_, v_a_945_, v_a_946_, v_a_947_);
return v___x_991_;
}
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_del_object(v___x_973_);
lean_dec_ref(v_i_970_);
lean_dec(v_type_952_);
lean_dec(v_fvarId_949_);
lean_dec_ref(v_k_944_);
v_a_995_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_977_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_977_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
case 6:
{
lean_object* v_i_1004_; lean_object* v_var_1005_; lean_object* v___f_1006_; lean_object* v___x_1007_; 
lean_dec(v_type_952_);
v_i_1004_ = lean_ctor_get(v_value_951_, 0);
lean_inc(v_i_1004_);
v_var_1005_ = lean_ctor_get(v_value_951_, 1);
lean_inc(v_var_1005_);
lean_dec_ref_known(v_value_951_, 2);
v___f_1006_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__2___boxed), 7, 2);
lean_closure_set(v___f_1006_, 0, v_i_1004_);
lean_closure_set(v___f_1006_, 1, v_continueLet_953_);
v___x_1007_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_943_, v_k_944_, v_var_1005_, v___f_1006_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_var_1005_);
return v___x_1007_;
}
case 7:
{
lean_object* v_i_1008_; lean_object* v_var_1009_; lean_object* v___f_1010_; lean_object* v___x_1011_; 
lean_dec(v_type_952_);
v_i_1008_ = lean_ctor_get(v_value_951_, 0);
lean_inc(v_i_1008_);
v_var_1009_ = lean_ctor_get(v_value_951_, 1);
lean_inc(v_var_1009_);
lean_dec_ref_known(v_value_951_, 2);
v___f_1010_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__3___boxed), 7, 2);
lean_closure_set(v___f_1010_, 0, v_i_1008_);
lean_closure_set(v___f_1010_, 1, v_continueLet_953_);
v___x_1011_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_943_, v_k_944_, v_var_1009_, v___f_1010_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_var_1009_);
return v___x_1011_;
}
case 8:
{
lean_object* v_n_1012_; lean_object* v_offset_1013_; lean_object* v_var_1014_; lean_object* v___f_1015_; lean_object* v___x_1016_; 
lean_dec(v_type_952_);
v_n_1012_ = lean_ctor_get(v_value_951_, 0);
lean_inc(v_n_1012_);
v_offset_1013_ = lean_ctor_get(v_value_951_, 1);
lean_inc(v_offset_1013_);
v_var_1014_ = lean_ctor_get(v_value_951_, 2);
lean_inc(v_var_1014_);
lean_dec_ref_known(v_value_951_, 3);
v___f_1015_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__4___boxed), 8, 3);
lean_closure_set(v___f_1015_, 0, v_n_1012_);
lean_closure_set(v___f_1015_, 1, v_offset_1013_);
lean_closure_set(v___f_1015_, 2, v_continueLet_953_);
v___x_1016_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_943_, v_k_944_, v_var_1014_, v___f_1015_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_var_1014_);
return v___x_1016_;
}
case 9:
{
lean_object* v_fn_1017_; lean_object* v_args_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1038_; 
lean_inc(v_fvarId_949_);
lean_dec_ref(v_continueLet_953_);
lean_dec_ref(v_decl_943_);
v_fn_1017_ = lean_ctor_get(v_value_951_, 0);
v_args_1018_ = lean_ctor_get(v_value_951_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_value_951_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1020_ = v_value_951_;
v_isShared_1021_ = v_isSharedCheck_1038_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_args_1018_);
lean_inc(v_fn_1017_);
lean_dec(v_value_951_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1038_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
size_t v_sz_1022_; size_t v___x_1023_; lean_object* v___x_1024_; 
v_sz_1022_ = lean_array_size(v_args_1018_);
v___x_1023_ = ((size_t)0ULL);
v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1022_, v___x_1023_, v_args_1018_, v_a_945_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1027_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
if (v_isShared_1021_ == 0)
{
lean_ctor_set_tag(v___x_1020_, 6);
lean_ctor_set(v___x_1020_, 1, v_a_1025_);
v___x_1027_ = v___x_1020_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_fn_1017_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_a_1025_);
v___x_1027_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_949_, v_k_944_, v_type_952_, v___x_1027_, v_a_945_, v_a_946_, v_a_947_);
return v___x_1028_;
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_del_object(v___x_1020_);
lean_dec(v_fn_1017_);
lean_dec(v_type_952_);
lean_dec(v_fvarId_949_);
lean_dec_ref(v_k_944_);
v_a_1030_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1024_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1024_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
case 10:
{
lean_object* v_fn_1039_; lean_object* v_args_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1060_; 
lean_inc(v_fvarId_949_);
lean_dec_ref(v_continueLet_953_);
lean_dec_ref(v_decl_943_);
v_fn_1039_ = lean_ctor_get(v_value_951_, 0);
v_args_1040_ = lean_ctor_get(v_value_951_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_value_951_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1042_ = v_value_951_;
v_isShared_1043_ = v_isSharedCheck_1060_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_args_1040_);
lean_inc(v_fn_1039_);
lean_dec(v_value_951_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1060_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
size_t v_sz_1044_; size_t v___x_1045_; lean_object* v___x_1046_; 
v_sz_1044_ = lean_array_size(v_args_1040_);
v___x_1045_ = ((size_t)0ULL);
v___x_1046_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1044_, v___x_1045_, v_args_1040_, v_a_945_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1049_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
if (v_isShared_1043_ == 0)
{
lean_ctor_set_tag(v___x_1042_, 7);
lean_ctor_set(v___x_1042_, 1, v_a_1047_);
v___x_1049_ = v___x_1042_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_fn_1039_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_a_1047_);
v___x_1049_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_949_, v_k_944_, v_type_952_, v___x_1049_, v_a_945_, v_a_946_, v_a_947_);
return v___x_1050_;
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_del_object(v___x_1042_);
lean_dec(v_fn_1039_);
lean_dec(v_type_952_);
lean_dec(v_fvarId_949_);
lean_dec_ref(v_k_944_);
v_a_1052_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1046_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1046_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
case 11:
{
lean_object* v_n_1061_; lean_object* v_var_1062_; lean_object* v___f_1063_; lean_object* v___x_1064_; 
lean_dec(v_type_952_);
v_n_1061_ = lean_ctor_get(v_value_951_, 0);
lean_inc(v_n_1061_);
v_var_1062_ = lean_ctor_get(v_value_951_, 1);
lean_inc(v_var_1062_);
lean_dec_ref_known(v_value_951_, 2);
v___f_1063_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__5___boxed), 7, 2);
lean_closure_set(v___f_1063_, 0, v_n_1061_);
lean_closure_set(v___f_1063_, 1, v_continueLet_953_);
v___x_1064_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_943_, v_k_944_, v_var_1062_, v___f_1063_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_var_1062_);
return v___x_1064_;
}
case 12:
{
lean_object* v_var_1065_; lean_object* v_i_1066_; uint8_t v_updateHeader_1067_; lean_object* v_args_1068_; lean_object* v___x_1069_; lean_object* v___f_1070_; lean_object* v___x_1071_; 
lean_dec(v_type_952_);
v_var_1065_ = lean_ctor_get(v_value_951_, 0);
lean_inc(v_var_1065_);
v_i_1066_ = lean_ctor_get(v_value_951_, 1);
lean_inc_ref(v_i_1066_);
v_updateHeader_1067_ = lean_ctor_get_uint8(v_value_951_, sizeof(void*)*3);
v_args_1068_ = lean_ctor_get(v_value_951_, 2);
lean_inc_ref(v_args_1068_);
lean_dec_ref_known(v_value_951_, 3);
v___x_1069_ = lean_box(v_updateHeader_1067_);
v___f_1070_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 9, 4);
lean_closure_set(v___f_1070_, 0, v_args_1068_);
lean_closure_set(v___f_1070_, 1, v_i_1066_);
lean_closure_set(v___f_1070_, 2, v___x_1069_);
lean_closure_set(v___f_1070_, 3, v_continueLet_953_);
v___x_1071_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_943_, v_k_944_, v_var_1065_, v___f_1070_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_var_1065_);
return v___x_1071_;
}
case 13:
{
lean_object* v_ty_1072_; lean_object* v_fvarId_1073_; lean_object* v___f_1074_; lean_object* v___x_1075_; 
lean_dec(v_type_952_);
v_ty_1072_ = lean_ctor_get(v_value_951_, 0);
lean_inc_ref(v_ty_1072_);
v_fvarId_1073_ = lean_ctor_get(v_value_951_, 1);
lean_inc(v_fvarId_1073_);
lean_dec_ref_known(v_value_951_, 2);
v___f_1074_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__7___boxed), 7, 2);
lean_closure_set(v___f_1074_, 0, v_ty_1072_);
lean_closure_set(v___f_1074_, 1, v_continueLet_953_);
v___x_1075_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_943_, v_k_944_, v_fvarId_1073_, v___f_1074_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_fvarId_1073_);
return v___x_1075_;
}
case 14:
{
lean_object* v_fvarId_1076_; lean_object* v___f_1077_; lean_object* v___x_1078_; 
lean_dec(v_type_952_);
v_fvarId_1076_ = lean_ctor_get(v_value_951_, 0);
lean_inc(v_fvarId_1076_);
lean_dec_ref_known(v_value_951_, 1);
v___f_1077_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__8___boxed), 6, 1);
lean_closure_set(v___f_1077_, 0, v_continueLet_953_);
v___x_1078_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_943_, v_k_944_, v_fvarId_1076_, v___f_1077_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_fvarId_1076_);
return v___x_1078_;
}
default: 
{
lean_object* v_fvarId_1079_; lean_object* v___f_1080_; lean_object* v___x_1081_; 
lean_dec(v_type_952_);
v_fvarId_1079_ = lean_ctor_get(v_value_951_, 0);
lean_inc(v_fvarId_1079_);
lean_dec_ref_known(v_value_951_, 1);
v___f_1080_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__9___boxed), 6, 1);
lean_closure_set(v___f_1080_, 0, v_continueLet_953_);
v___x_1081_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_943_, v_k_944_, v_fvarId_1079_, v___f_1080_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_fvarId_1079_);
return v___x_1081_;
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__3(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1085_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__2));
v___x_1086_ = lean_unsigned_to_nat(15u);
v___x_1087_ = lean_unsigned_to_nat(128u);
v___x_1088_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1089_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1090_ = l_mkPanicMessageWithDecl(v___x_1089_, v___x_1088_, v___x_1087_, v___x_1086_, v___x_1085_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
if (lean_obj_tag(v_a_1091_) == 1)
{
lean_object* v_info_1096_; lean_object* v_code_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1133_; 
v_info_1096_ = lean_ctor_get(v_a_1091_, 0);
v_code_1097_ = lean_ctor_get(v_a_1091_, 1);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_a_1091_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1099_ = v_a_1091_;
v_isShared_1100_ = v_isSharedCheck_1133_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_code_1097_);
lean_inc(v_info_1096_);
lean_dec(v_a_1091_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1133_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_IR_ToIR_lowerCode(v_code_1097_, v_a_1092_, v_a_1093_, v_a_1094_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1124_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1124_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1124_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v_name_1106_; lean_object* v_cidx_1107_; lean_object* v_size_1108_; lean_object* v_usize_1109_; lean_object* v_ssize_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1123_; 
v_name_1106_ = lean_ctor_get(v_info_1096_, 0);
v_cidx_1107_ = lean_ctor_get(v_info_1096_, 1);
v_size_1108_ = lean_ctor_get(v_info_1096_, 2);
v_usize_1109_ = lean_ctor_get(v_info_1096_, 3);
v_ssize_1110_ = lean_ctor_get(v_info_1096_, 4);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_info_1096_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1112_ = v_info_1096_;
v_isShared_1113_ = v_isSharedCheck_1123_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_ssize_1110_);
lean_inc(v_usize_1109_);
lean_inc(v_size_1108_);
lean_inc(v_cidx_1107_);
lean_inc(v_name_1106_);
lean_dec(v_info_1096_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1123_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_name_1106_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_cidx_1107_);
lean_ctor_set(v_reuseFailAlloc_1122_, 2, v_size_1108_);
lean_ctor_set(v_reuseFailAlloc_1122_, 3, v_usize_1109_);
lean_ctor_set(v_reuseFailAlloc_1122_, 4, v_ssize_1110_);
v___x_1115_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
lean_object* v___x_1117_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set_tag(v___x_1099_, 0);
lean_ctor_set(v___x_1099_, 1, v_a_1102_);
lean_ctor_set(v___x_1099_, 0, v___x_1115_);
v___x_1117_ = v___x_1099_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1115_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_a_1102_);
v___x_1117_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1119_; 
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1117_);
v___x_1119_ = v___x_1104_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_del_object(v___x_1099_);
lean_dec_ref(v_info_1096_);
v_a_1125_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1101_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1101_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
else
{
lean_object* v_code_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1158_; 
v_code_1134_ = lean_ctor_get(v_a_1091_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_a_1091_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1136_ = v_a_1091_;
v_isShared_1137_ = v_isSharedCheck_1158_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_code_1134_);
lean_dec(v_a_1091_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1158_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_IR_ToIR_lowerCode(v_code_1134_, v_a_1092_, v_a_1093_, v_a_1094_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1149_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1149_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1149_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set_tag(v___x_1136_, 1);
lean_ctor_set(v___x_1136_, 0, v_a_1139_);
v___x_1144_ = v___x_1136_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1146_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1144_);
v___x_1146_ = v___x_1141_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_del_object(v___x_1136_);
v_a_1150_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1138_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1138_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(size_t v_sz_1159_, size_t v_i_1160_, lean_object* v_bs_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
uint8_t v___x_1166_; 
v___x_1166_ = lean_usize_dec_lt(v_i_1160_, v_sz_1159_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v_bs_1161_);
return v___x_1167_;
}
else
{
lean_object* v_v_1168_; lean_object* v___x_1169_; 
v_v_1168_ = lean_array_uget_borrowed(v_bs_1161_, v_i_1160_);
lean_inc(v_v_1168_);
v___x_1169_ = l_Lean_IR_ToIR_lowerAlt(v_v_1168_, v___y_1162_, v___y_1163_, v___y_1164_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1171_; lean_object* v_bs_x27_1172_; size_t v___x_1173_; size_t v___x_1174_; lean_object* v___x_1175_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1169_, 1);
v___x_1171_ = lean_unsigned_to_nat(0u);
v_bs_x27_1172_ = lean_array_uset(v_bs_1161_, v_i_1160_, v___x_1171_);
v___x_1173_ = ((size_t)1ULL);
v___x_1174_ = lean_usize_add(v_i_1160_, v___x_1173_);
v___x_1175_ = lean_array_uset(v_bs_x27_1172_, v_i_1160_, v_a_1170_);
v_i_1160_ = v___x_1174_;
v_bs_1161_ = v___x_1175_;
goto _start;
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec_ref(v_bs_1161_);
v_a_1177_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1169_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1169_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__5(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1186_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1187_ = lean_unsigned_to_nat(53u);
v___x_1188_ = lean_unsigned_to_nat(95u);
v___x_1189_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1190_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1191_ = l_mkPanicMessageWithDecl(v___x_1190_, v___x_1189_, v___x_1188_, v___x_1187_, v___x_1186_);
return v___x_1191_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__6(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1192_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1193_ = lean_unsigned_to_nat(44u);
v___x_1194_ = lean_unsigned_to_nat(106u);
v___x_1195_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1196_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1197_ = l_mkPanicMessageWithDecl(v___x_1196_, v___x_1195_, v___x_1194_, v___x_1193_, v___x_1192_);
return v___x_1197_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__7(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1198_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1199_ = lean_unsigned_to_nat(44u);
v___x_1200_ = lean_unsigned_to_nat(114u);
v___x_1201_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1202_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1203_ = l_mkPanicMessageWithDecl(v___x_1202_, v___x_1201_, v___x_1200_, v___x_1199_, v___x_1198_);
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__8(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1204_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1205_ = lean_unsigned_to_nat(34u);
v___x_1206_ = lean_unsigned_to_nat(113u);
v___x_1207_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1208_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1209_ = l_mkPanicMessageWithDecl(v___x_1208_, v___x_1207_, v___x_1206_, v___x_1205_, v___x_1204_);
return v___x_1209_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__9(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1210_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1211_ = lean_unsigned_to_nat(44u);
v___x_1212_ = lean_unsigned_to_nat(110u);
v___x_1213_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1214_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1215_ = l_mkPanicMessageWithDecl(v___x_1214_, v___x_1213_, v___x_1212_, v___x_1211_, v___x_1210_);
return v___x_1215_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__10(void){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1216_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1217_ = lean_unsigned_to_nat(34u);
v___x_1218_ = lean_unsigned_to_nat(109u);
v___x_1219_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1220_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1221_ = l_mkPanicMessageWithDecl(v___x_1220_, v___x_1219_, v___x_1218_, v___x_1217_, v___x_1216_);
return v___x_1221_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__11(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1222_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1223_ = lean_unsigned_to_nat(41u);
v___x_1224_ = lean_unsigned_to_nat(117u);
v___x_1225_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1226_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1227_ = l_mkPanicMessageWithDecl(v___x_1226_, v___x_1225_, v___x_1224_, v___x_1223_, v___x_1222_);
return v___x_1227_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__12(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1228_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1229_ = lean_unsigned_to_nat(41u);
v___x_1230_ = lean_unsigned_to_nat(120u);
v___x_1231_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1232_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1233_ = l_mkPanicMessageWithDecl(v___x_1232_, v___x_1231_, v___x_1230_, v___x_1229_, v___x_1228_);
return v___x_1233_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__13(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1234_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1235_ = lean_unsigned_to_nat(41u);
v___x_1236_ = lean_unsigned_to_nat(123u);
v___x_1237_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1238_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1239_ = l_mkPanicMessageWithDecl(v___x_1238_, v___x_1237_, v___x_1236_, v___x_1235_, v___x_1234_);
return v___x_1239_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__14(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1240_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1241_ = lean_unsigned_to_nat(41u);
v___x_1242_ = lean_unsigned_to_nat(126u);
v___x_1243_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1244_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1245_ = l_mkPanicMessageWithDecl(v___x_1244_, v___x_1243_, v___x_1242_, v___x_1241_, v___x_1240_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object* v_c_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
switch(lean_obj_tag(v_c_1246_))
{
case 0:
{
lean_object* v_decl_1251_; lean_object* v_k_1252_; lean_object* v___x_1253_; 
v_decl_1251_ = lean_ctor_get(v_c_1246_, 0);
lean_inc_ref(v_decl_1251_);
v_k_1252_ = lean_ctor_get(v_c_1246_, 1);
lean_inc_ref(v_k_1252_);
lean_dec_ref_known(v_c_1246_, 2);
v___x_1253_ = l_Lean_IR_ToIR_lowerLet(v_decl_1251_, v_k_1252_, v_a_1247_, v_a_1248_, v_a_1249_);
return v___x_1253_;
}
case 1:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_dec_ref_known(v_c_1246_, 2);
v___x_1254_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__3, &l_Lean_IR_ToIR_lowerCode___closed__3_once, _init_l_Lean_IR_ToIR_lowerCode___closed__3);
v___x_1255_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1254_, v_a_1247_, v_a_1248_, v_a_1249_);
return v___x_1255_;
}
case 2:
{
lean_object* v_decl_1256_; lean_object* v_k_1257_; lean_object* v_fvarId_1258_; lean_object* v_params_1259_; lean_object* v_value_1260_; lean_object* v___x_1261_; 
v_decl_1256_ = lean_ctor_get(v_c_1246_, 0);
lean_inc_ref(v_decl_1256_);
v_k_1257_ = lean_ctor_get(v_c_1246_, 1);
lean_inc_ref(v_k_1257_);
lean_dec_ref_known(v_c_1246_, 2);
v_fvarId_1258_ = lean_ctor_get(v_decl_1256_, 0);
lean_inc(v_fvarId_1258_);
v_params_1259_ = lean_ctor_get(v_decl_1256_, 2);
lean_inc_ref(v_params_1259_);
v_value_1260_ = lean_ctor_get(v_decl_1256_, 4);
lean_inc_ref(v_value_1260_);
lean_dec_ref(v_decl_1256_);
v___x_1261_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_1258_, v_a_1247_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; size_t v_sz_1263_; size_t v___x_1264_; lean_object* v___x_1265_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v_sz_1263_ = lean_array_size(v_params_1259_);
v___x_1264_ = ((size_t)0ULL);
v___x_1265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1263_, v___x_1264_, v_params_1259_, v_a_1247_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1267_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1265_, 1);
v___x_1267_ = l_Lean_IR_ToIR_lowerCode(v_value_1260_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1269_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1269_ = l_Lean_IR_ToIR_lowerCode(v_k_1257_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1278_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1272_ = v___x_1269_;
v_isShared_1273_ = v_isSharedCheck_1278_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1269_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1278_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1274_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1274_, 0, v_a_1262_);
lean_ctor_set(v___x_1274_, 1, v_a_1266_);
lean_ctor_set(v___x_1274_, 2, v_a_1268_);
lean_ctor_set(v___x_1274_, 3, v_a_1270_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1274_);
v___x_1276_ = v___x_1272_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
else
{
lean_dec(v_a_1268_);
lean_dec(v_a_1266_);
lean_dec(v_a_1262_);
return v___x_1269_;
}
}
else
{
lean_dec(v_a_1266_);
lean_dec(v_a_1262_);
lean_dec_ref(v_k_1257_);
return v___x_1267_;
}
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
lean_dec(v_a_1262_);
lean_dec_ref(v_value_1260_);
lean_dec_ref(v_k_1257_);
v_a_1279_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1265_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1265_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec_ref(v_value_1260_);
lean_dec_ref(v_params_1259_);
lean_dec_ref(v_k_1257_);
v_a_1287_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1261_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1261_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_1295_; lean_object* v_args_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1332_; 
v_fvarId_1295_ = lean_ctor_get(v_c_1246_, 0);
v_args_1296_ = lean_ctor_get(v_c_1246_, 1);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_c_1246_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1298_ = v_c_1246_;
v_isShared_1299_ = v_isSharedCheck_1332_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_args_1296_);
lean_inc(v_fvarId_1295_);
lean_dec(v_c_1246_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1332_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_1295_, v_a_1247_);
lean_dec(v_fvarId_1295_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; size_t v_sz_1302_; size_t v___x_1303_; lean_object* v___x_1304_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v_sz_1302_ = lean_array_size(v_args_1296_);
v___x_1303_ = ((size_t)0ULL);
v___x_1304_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1302_, v___x_1303_, v_args_1296_, v_a_1247_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1315_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1307_ = v___x_1304_;
v_isShared_1308_ = v_isSharedCheck_1315_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1304_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1315_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set_tag(v___x_1298_, 11);
lean_ctor_set(v___x_1298_, 1, v_a_1305_);
lean_ctor_set(v___x_1298_, 0, v_a_1301_);
v___x_1310_ = v___x_1298_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1301_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1312_; 
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v___x_1310_);
v___x_1312_ = v___x_1307_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec(v_a_1301_);
lean_del_object(v___x_1298_);
v_a_1316_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1304_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1304_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_del_object(v___x_1298_);
lean_dec_ref(v_args_1296_);
v_a_1324_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1300_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1300_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
case 4:
{
lean_object* v_cases_1333_; lean_object* v_typeName_1334_; lean_object* v_discr_1335_; lean_object* v_alts_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1376_; 
v_cases_1333_ = lean_ctor_get(v_c_1246_, 0);
lean_inc_ref(v_cases_1333_);
lean_dec_ref_known(v_c_1246_, 1);
v_typeName_1334_ = lean_ctor_get(v_cases_1333_, 0);
v_discr_1335_ = lean_ctor_get(v_cases_1333_, 2);
v_alts_1336_ = lean_ctor_get(v_cases_1333_, 3);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_cases_1333_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; 
v_unused_1377_ = lean_ctor_get(v_cases_1333_, 1);
lean_dec(v_unused_1377_);
v___x_1338_ = v_cases_1333_;
v_isShared_1339_ = v_isSharedCheck_1376_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_alts_1336_);
lean_inc(v_discr_1335_);
lean_inc(v_typeName_1334_);
lean_dec(v_cases_1333_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1376_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_discr_1335_, v_a_1247_);
lean_dec(v_discr_1335_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1340_, 1);
if (lean_obj_tag(v_a_1341_) == 0)
{
lean_object* v_id_1342_; size_t v_sz_1343_; size_t v___x_1344_; lean_object* v___x_1345_; 
v_id_1342_ = lean_ctor_get(v_a_1341_, 0);
lean_inc(v_id_1342_);
lean_dec_ref_known(v_a_1341_, 1);
v_sz_1343_ = lean_array_size(v_alts_1336_);
v___x_1344_ = ((size_t)0ULL);
v___x_1345_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_1343_, v___x_1344_, v_alts_1336_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1357_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1357_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1357_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1350_ = l_Lean_IR_nameToIRType(v_typeName_1334_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set_tag(v___x_1338_, 9);
lean_ctor_set(v___x_1338_, 3, v_a_1346_);
lean_ctor_set(v___x_1338_, 2, v___x_1350_);
lean_ctor_set(v___x_1338_, 1, v_id_1342_);
v___x_1352_ = v___x_1338_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_typeName_1334_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_id_1342_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1356_, 3, v_a_1346_);
v___x_1352_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1354_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1352_);
v___x_1354_ = v___x_1348_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec(v_id_1342_);
lean_del_object(v___x_1338_);
lean_dec(v_typeName_1334_);
v_a_1358_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1345_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1345_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_dec(v_a_1341_);
lean_del_object(v___x_1338_);
lean_dec_ref(v_alts_1336_);
lean_dec(v_typeName_1334_);
v___x_1366_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__5, &l_Lean_IR_ToIR_lowerCode___closed__5_once, _init_l_Lean_IR_ToIR_lowerCode___closed__5);
v___x_1367_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1366_, v_a_1247_, v_a_1248_, v_a_1249_);
return v___x_1367_;
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_del_object(v___x_1338_);
lean_dec_ref(v_alts_1336_);
lean_dec(v_typeName_1334_);
v_a_1368_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1340_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1340_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1402_; 
v_fvarId_1378_ = lean_ctor_get(v_c_1246_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_c_1246_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1380_ = v_c_1246_;
v_isShared_1381_ = v_isSharedCheck_1402_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_fvarId_1378_);
lean_dec(v_c_1246_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1402_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1378_, v_a_1247_);
lean_dec(v_fvarId_1378_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1393_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1393_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1393_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1381_ == 0)
{
lean_ctor_set_tag(v___x_1380_, 10);
lean_ctor_set(v___x_1380_, 0, v_a_1383_);
v___x_1388_ = v___x_1380_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1390_; 
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1388_);
v___x_1390_ = v___x_1385_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_del_object(v___x_1380_);
v_a_1394_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1382_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1382_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
case 6:
{
lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1410_; 
v_isSharedCheck_1410_ = !lean_is_exclusive(v_c_1246_);
if (v_isSharedCheck_1410_ == 0)
{
lean_object* v_unused_1411_; 
v_unused_1411_ = lean_ctor_get(v_c_1246_, 0);
lean_dec(v_unused_1411_);
v___x_1404_ = v_c_1246_;
v_isShared_1405_ = v_isSharedCheck_1410_;
goto v_resetjp_1403_;
}
else
{
lean_dec(v_c_1246_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1410_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1406_ = lean_box(12);
if (v_isShared_1405_ == 0)
{
lean_ctor_set_tag(v___x_1404_, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1406_);
v___x_1408_ = v___x_1404_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
case 7:
{
lean_object* v_fvarId_1412_; lean_object* v_i_1413_; lean_object* v_y_1414_; lean_object* v_k_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1454_; 
v_fvarId_1412_ = lean_ctor_get(v_c_1246_, 0);
v_i_1413_ = lean_ctor_get(v_c_1246_, 1);
v_y_1414_ = lean_ctor_get(v_c_1246_, 2);
v_k_1415_ = lean_ctor_get(v_c_1246_, 3);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_c_1246_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1417_ = v_c_1246_;
v_isShared_1418_ = v_isSharedCheck_1454_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_k_1415_);
lean_inc(v_y_1414_);
lean_inc(v_i_1413_);
lean_inc(v_fvarId_1412_);
lean_dec(v_c_1246_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1454_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_IR_ToIR_lowerArg___redArg(v_y_1414_, v_a_1247_);
lean_dec(v_y_1414_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1421_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1419_, 1);
v___x_1421_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1412_, v_a_1247_);
lean_dec(v_fvarId_1412_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
if (lean_obj_tag(v_a_1422_) == 0)
{
lean_object* v_id_1423_; lean_object* v___x_1424_; 
v_id_1423_ = lean_ctor_get(v_a_1422_, 0);
lean_inc(v_id_1423_);
lean_dec_ref_known(v_a_1422_, 1);
v___x_1424_ = l_Lean_IR_ToIR_lowerCode(v_k_1415_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1435_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1427_ = v___x_1424_;
v_isShared_1428_ = v_isSharedCheck_1435_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1424_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1435_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set_tag(v___x_1417_, 2);
lean_ctor_set(v___x_1417_, 3, v_a_1425_);
lean_ctor_set(v___x_1417_, 2, v_a_1420_);
lean_ctor_set(v___x_1417_, 0, v_id_1423_);
v___x_1430_ = v___x_1417_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_id_1423_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_i_1413_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_a_1420_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1432_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1430_);
v___x_1432_ = v___x_1427_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
else
{
lean_dec(v_id_1423_);
lean_dec(v_a_1420_);
lean_del_object(v___x_1417_);
lean_dec(v_i_1413_);
return v___x_1424_;
}
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_dec(v_a_1422_);
lean_dec(v_a_1420_);
lean_del_object(v___x_1417_);
lean_dec_ref(v_k_1415_);
lean_dec(v_i_1413_);
v___x_1436_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__6, &l_Lean_IR_ToIR_lowerCode___closed__6_once, _init_l_Lean_IR_ToIR_lowerCode___closed__6);
v___x_1437_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1436_, v_a_1247_, v_a_1248_, v_a_1249_);
return v___x_1437_;
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec(v_a_1420_);
lean_del_object(v___x_1417_);
lean_dec_ref(v_k_1415_);
lean_dec(v_i_1413_);
v_a_1438_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1421_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1421_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_del_object(v___x_1417_);
lean_dec_ref(v_k_1415_);
lean_dec(v_i_1413_);
lean_dec(v_fvarId_1412_);
v_a_1446_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1419_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1419_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
}
case 8:
{
lean_object* v_fvarId_1455_; lean_object* v_i_1456_; lean_object* v_y_1457_; lean_object* v_k_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1500_; 
v_fvarId_1455_ = lean_ctor_get(v_c_1246_, 0);
v_i_1456_ = lean_ctor_get(v_c_1246_, 1);
v_y_1457_ = lean_ctor_get(v_c_1246_, 2);
v_k_1458_ = lean_ctor_get(v_c_1246_, 3);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_c_1246_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1460_ = v_c_1246_;
v_isShared_1461_ = v_isSharedCheck_1500_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_k_1458_);
lean_inc(v_y_1457_);
lean_inc(v_i_1456_);
lean_inc(v_fvarId_1455_);
lean_dec(v_c_1246_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1500_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1457_, v_a_1247_);
lean_dec(v_y_1457_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1462_, 1);
if (lean_obj_tag(v_a_1463_) == 0)
{
lean_object* v_id_1464_; lean_object* v___x_1465_; 
v_id_1464_ = lean_ctor_get(v_a_1463_, 0);
lean_inc(v_id_1464_);
lean_dec_ref_known(v_a_1463_, 1);
v___x_1465_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1455_, v_a_1247_);
lean_dec(v_fvarId_1455_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___x_1465_, 1);
if (lean_obj_tag(v_a_1466_) == 0)
{
lean_object* v_id_1467_; lean_object* v___x_1468_; 
v_id_1467_ = lean_ctor_get(v_a_1466_, 0);
lean_inc(v_id_1467_);
lean_dec_ref_known(v_a_1466_, 1);
v___x_1468_ = l_Lean_IR_ToIR_lowerCode(v_k_1458_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1479_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1471_ = v___x_1468_;
v_isShared_1472_ = v_isSharedCheck_1479_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1468_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1479_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1461_ == 0)
{
lean_ctor_set_tag(v___x_1460_, 4);
lean_ctor_set(v___x_1460_, 3, v_a_1469_);
lean_ctor_set(v___x_1460_, 2, v_id_1464_);
lean_ctor_set(v___x_1460_, 0, v_id_1467_);
v___x_1474_ = v___x_1460_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_id_1467_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_i_1456_);
lean_ctor_set(v_reuseFailAlloc_1478_, 2, v_id_1464_);
lean_ctor_set(v_reuseFailAlloc_1478_, 3, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_object* v___x_1476_; 
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1474_);
v___x_1476_ = v___x_1471_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_dec(v_id_1467_);
lean_dec(v_id_1464_);
lean_del_object(v___x_1460_);
lean_dec(v_i_1456_);
return v___x_1468_;
}
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_dec(v_a_1466_);
lean_dec(v_id_1464_);
lean_del_object(v___x_1460_);
lean_dec_ref(v_k_1458_);
lean_dec(v_i_1456_);
v___x_1480_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__7, &l_Lean_IR_ToIR_lowerCode___closed__7_once, _init_l_Lean_IR_ToIR_lowerCode___closed__7);
v___x_1481_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1480_, v_a_1247_, v_a_1248_, v_a_1249_);
return v___x_1481_;
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec(v_id_1464_);
lean_del_object(v___x_1460_);
lean_dec_ref(v_k_1458_);
lean_dec(v_i_1456_);
v_a_1482_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1465_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1465_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
else
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_dec(v_a_1463_);
lean_del_object(v___x_1460_);
lean_dec_ref(v_k_1458_);
lean_dec(v_i_1456_);
lean_dec(v_fvarId_1455_);
v___x_1490_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__8, &l_Lean_IR_ToIR_lowerCode___closed__8_once, _init_l_Lean_IR_ToIR_lowerCode___closed__8);
v___x_1491_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1490_, v_a_1247_, v_a_1248_, v_a_1249_);
return v___x_1491_;
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_del_object(v___x_1460_);
lean_dec_ref(v_k_1458_);
lean_dec(v_i_1456_);
lean_dec(v_fvarId_1455_);
v_a_1492_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1462_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1462_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
case 9:
{
lean_object* v_fvarId_1501_; lean_object* v_i_1502_; lean_object* v_offset_1503_; lean_object* v_y_1504_; lean_object* v_ty_1505_; lean_object* v_k_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1549_; 
v_fvarId_1501_ = lean_ctor_get(v_c_1246_, 0);
v_i_1502_ = lean_ctor_get(v_c_1246_, 1);
v_offset_1503_ = lean_ctor_get(v_c_1246_, 2);
v_y_1504_ = lean_ctor_get(v_c_1246_, 3);
v_ty_1505_ = lean_ctor_get(v_c_1246_, 4);
v_k_1506_ = lean_ctor_get(v_c_1246_, 5);
v_isSharedCheck_1549_ = !lean_is_exclusive(v_c_1246_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1508_ = v_c_1246_;
v_isShared_1509_ = v_isSharedCheck_1549_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_k_1506_);
lean_inc(v_ty_1505_);
lean_inc(v_y_1504_);
lean_inc(v_offset_1503_);
lean_inc(v_i_1502_);
lean_inc(v_fvarId_1501_);
lean_dec(v_c_1246_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1549_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1504_, v_a_1247_);
lean_dec(v_y_1504_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref_known(v___x_1510_, 1);
if (lean_obj_tag(v_a_1511_) == 0)
{
lean_object* v_id_1512_; lean_object* v___x_1513_; 
v_id_1512_ = lean_ctor_get(v_a_1511_, 0);
lean_inc(v_id_1512_);
lean_dec_ref_known(v_a_1511_, 1);
v___x_1513_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1501_, v_a_1247_);
lean_dec(v_fvarId_1501_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1513_, 1);
if (lean_obj_tag(v_a_1514_) == 0)
{
lean_object* v_id_1515_; lean_object* v___x_1516_; 
v_id_1515_ = lean_ctor_get(v_a_1514_, 0);
lean_inc(v_id_1515_);
lean_dec_ref_known(v_a_1514_, 1);
v___x_1516_ = l_Lean_IR_ToIR_lowerCode(v_k_1506_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1528_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1519_ = v___x_1516_;
v_isShared_1520_ = v_isSharedCheck_1528_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1516_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1528_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1521_ = l_Lean_IR_toIRType(v_ty_1505_);
lean_dec_ref(v_ty_1505_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 5);
lean_ctor_set(v___x_1508_, 5, v_a_1517_);
lean_ctor_set(v___x_1508_, 4, v___x_1521_);
lean_ctor_set(v___x_1508_, 3, v_id_1512_);
lean_ctor_set(v___x_1508_, 0, v_id_1515_);
v___x_1523_ = v___x_1508_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_id_1515_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_i_1502_);
lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_offset_1503_);
lean_ctor_set(v_reuseFailAlloc_1527_, 3, v_id_1512_);
lean_ctor_set(v_reuseFailAlloc_1527_, 4, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1527_, 5, v_a_1517_);
v___x_1523_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1525_; 
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1523_);
v___x_1525_ = v___x_1519_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
else
{
lean_dec(v_id_1515_);
lean_dec(v_id_1512_);
lean_del_object(v___x_1508_);
lean_dec_ref(v_ty_1505_);
lean_dec(v_offset_1503_);
lean_dec(v_i_1502_);
return v___x_1516_;
}
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec(v_a_1514_);
lean_dec(v_id_1512_);
lean_del_object(v___x_1508_);
lean_dec_ref(v_k_1506_);
lean_dec_ref(v_ty_1505_);
lean_dec(v_offset_1503_);
lean_dec(v_i_1502_);
v___x_1529_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__9, &l_Lean_IR_ToIR_lowerCode___closed__9_once, _init_l_Lean_IR_ToIR_lowerCode___closed__9);
v___x_1530_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1529_, v_a_1247_, v_a_1248_, v_a_1249_);
return v___x_1530_;
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec(v_id_1512_);
lean_del_object(v___x_1508_);
lean_dec_ref(v_k_1506_);
lean_dec_ref(v_ty_1505_);
lean_dec(v_offset_1503_);
lean_dec(v_i_1502_);
v_a_1531_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1513_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1513_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_dec(v_a_1511_);
lean_del_object(v___x_1508_);
lean_dec_ref(v_k_1506_);
lean_dec_ref(v_ty_1505_);
lean_dec(v_offset_1503_);
lean_dec(v_i_1502_);
lean_dec(v_fvarId_1501_);
v___x_1539_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__10, &l_Lean_IR_ToIR_lowerCode___closed__10_once, _init_l_Lean_IR_ToIR_lowerCode___closed__10);
v___x_1540_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1539_, v_a_1247_, v_a_1248_, v_a_1249_);
return v___x_1540_;
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_del_object(v___x_1508_);
lean_dec_ref(v_k_1506_);
lean_dec_ref(v_ty_1505_);
lean_dec(v_offset_1503_);
lean_dec(v_i_1502_);
lean_dec(v_fvarId_1501_);
v_a_1541_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1510_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1510_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
}
case 10:
{
lean_object* v_fvarId_1550_; lean_object* v_cidx_1551_; lean_object* v_k_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1581_; 
v_fvarId_1550_ = lean_ctor_get(v_c_1246_, 0);
v_cidx_1551_ = lean_ctor_get(v_c_1246_, 1);
v_k_1552_ = lean_ctor_get(v_c_1246_, 2);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_c_1246_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1554_ = v_c_1246_;
v_isShared_1555_ = v_isSharedCheck_1581_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_k_1552_);
lean_inc(v_cidx_1551_);
lean_inc(v_fvarId_1550_);
lean_dec(v_c_1246_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1581_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1550_, v_a_1247_);
lean_dec(v_fvarId_1550_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
if (lean_obj_tag(v_a_1557_) == 0)
{
lean_object* v_id_1558_; lean_object* v___x_1559_; 
v_id_1558_ = lean_ctor_get(v_a_1557_, 0);
lean_inc(v_id_1558_);
lean_dec_ref_known(v_a_1557_, 1);
v___x_1559_ = l_Lean_IR_ToIR_lowerCode(v_k_1552_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1570_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1562_ = v___x_1559_;
v_isShared_1563_ = v_isSharedCheck_1570_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1559_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1570_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1555_ == 0)
{
lean_ctor_set_tag(v___x_1554_, 3);
lean_ctor_set(v___x_1554_, 2, v_a_1560_);
lean_ctor_set(v___x_1554_, 0, v_id_1558_);
v___x_1565_ = v___x_1554_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_id_1558_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_cidx_1551_);
lean_ctor_set(v_reuseFailAlloc_1569_, 2, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1567_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1565_);
v___x_1567_ = v___x_1562_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
else
{
lean_dec(v_id_1558_);
lean_del_object(v___x_1554_);
lean_dec(v_cidx_1551_);
return v___x_1559_;
}
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_dec(v_a_1557_);
lean_del_object(v___x_1554_);
lean_dec_ref(v_k_1552_);
lean_dec(v_cidx_1551_);
v___x_1571_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__11, &l_Lean_IR_ToIR_lowerCode___closed__11_once, _init_l_Lean_IR_ToIR_lowerCode___closed__11);
v___x_1572_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1571_, v_a_1247_, v_a_1248_, v_a_1249_);
return v___x_1572_;
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_del_object(v___x_1554_);
lean_dec_ref(v_k_1552_);
lean_dec(v_cidx_1551_);
v_a_1573_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1556_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1556_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
case 11:
{
lean_object* v_fvarId_1582_; lean_object* v_n_1583_; uint8_t v_check_1584_; uint8_t v_persistent_1585_; lean_object* v_k_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1615_; 
v_fvarId_1582_ = lean_ctor_get(v_c_1246_, 0);
v_n_1583_ = lean_ctor_get(v_c_1246_, 1);
v_check_1584_ = lean_ctor_get_uint8(v_c_1246_, sizeof(void*)*3);
v_persistent_1585_ = lean_ctor_get_uint8(v_c_1246_, sizeof(void*)*3 + 1);
v_k_1586_ = lean_ctor_get(v_c_1246_, 2);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_c_1246_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1588_ = v_c_1246_;
v_isShared_1589_ = v_isSharedCheck_1615_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_k_1586_);
lean_inc(v_n_1583_);
lean_inc(v_fvarId_1582_);
lean_dec(v_c_1246_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1615_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1582_, v_a_1247_);
lean_dec(v_fvarId_1582_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1590_, 1);
if (lean_obj_tag(v_a_1591_) == 0)
{
lean_object* v_id_1592_; lean_object* v___x_1593_; 
v_id_1592_ = lean_ctor_get(v_a_1591_, 0);
lean_inc(v_id_1592_);
lean_dec_ref_known(v_a_1591_, 1);
v___x_1593_ = l_Lean_IR_ToIR_lowerCode(v_k_1586_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1604_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1596_ = v___x_1593_;
v_isShared_1597_ = v_isSharedCheck_1604_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1593_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1604_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1589_ == 0)
{
lean_ctor_set_tag(v___x_1588_, 6);
lean_ctor_set(v___x_1588_, 2, v_a_1594_);
lean_ctor_set(v___x_1588_, 0, v_id_1592_);
v___x_1599_ = v___x_1588_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_id_1592_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_n_1583_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_a_1594_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, sizeof(void*)*3, v_check_1584_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, sizeof(void*)*3 + 1, v_persistent_1585_);
v___x_1599_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1601_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v___x_1599_);
v___x_1601_ = v___x_1596_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_dec(v_id_1592_);
lean_del_object(v___x_1588_);
lean_dec(v_n_1583_);
return v___x_1593_;
}
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
lean_dec(v_a_1591_);
lean_del_object(v___x_1588_);
lean_dec_ref(v_k_1586_);
lean_dec(v_n_1583_);
v___x_1605_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__12, &l_Lean_IR_ToIR_lowerCode___closed__12_once, _init_l_Lean_IR_ToIR_lowerCode___closed__12);
v___x_1606_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1605_, v_a_1247_, v_a_1248_, v_a_1249_);
return v___x_1606_;
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_del_object(v___x_1588_);
lean_dec_ref(v_k_1586_);
lean_dec(v_n_1583_);
v_a_1607_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1590_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1590_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
case 12:
{
lean_object* v_fvarId_1616_; lean_object* v_n_1617_; uint8_t v_check_1618_; uint8_t v_persistent_1619_; lean_object* v_k_1620_; lean_object* v___x_1621_; 
v_fvarId_1616_ = lean_ctor_get(v_c_1246_, 0);
lean_inc(v_fvarId_1616_);
v_n_1617_ = lean_ctor_get(v_c_1246_, 1);
lean_inc(v_n_1617_);
v_check_1618_ = lean_ctor_get_uint8(v_c_1246_, sizeof(void*)*4);
v_persistent_1619_ = lean_ctor_get_uint8(v_c_1246_, sizeof(void*)*4 + 1);
v_k_1620_ = lean_ctor_get(v_c_1246_, 3);
lean_inc_ref(v_k_1620_);
lean_dec_ref_known(v_c_1246_, 4);
v___x_1621_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1616_, v_a_1247_);
lean_dec(v_fvarId_1616_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
if (lean_obj_tag(v_a_1622_) == 0)
{
lean_object* v_id_1623_; lean_object* v___x_1624_; 
v_id_1623_ = lean_ctor_get(v_a_1622_, 0);
lean_inc(v_id_1623_);
lean_dec_ref_known(v_a_1622_, 1);
v___x_1624_ = l_Lean_IR_ToIR_lowerCode(v_k_1620_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1633_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1627_ = v___x_1624_;
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1629_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v___x_1629_, 0, v_id_1623_);
lean_ctor_set(v___x_1629_, 1, v_n_1617_);
lean_ctor_set(v___x_1629_, 2, v_a_1625_);
lean_ctor_set_uint8(v___x_1629_, sizeof(void*)*3, v_check_1618_);
lean_ctor_set_uint8(v___x_1629_, sizeof(void*)*3 + 1, v_persistent_1619_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1629_);
v___x_1631_ = v___x_1627_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
else
{
lean_dec(v_id_1623_);
lean_dec(v_n_1617_);
return v___x_1624_;
}
}
else
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
lean_dec(v_a_1622_);
lean_dec_ref(v_k_1620_);
lean_dec(v_n_1617_);
v___x_1634_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__13, &l_Lean_IR_ToIR_lowerCode___closed__13_once, _init_l_Lean_IR_ToIR_lowerCode___closed__13);
v___x_1635_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1634_, v_a_1247_, v_a_1248_, v_a_1249_);
return v___x_1635_;
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec_ref(v_k_1620_);
lean_dec(v_n_1617_);
v_a_1636_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1621_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1621_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
default: 
{
lean_object* v_fvarId_1644_; lean_object* v_k_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1674_; 
v_fvarId_1644_ = lean_ctor_get(v_c_1246_, 0);
v_k_1645_ = lean_ctor_get(v_c_1246_, 1);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_c_1246_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1647_ = v_c_1246_;
v_isShared_1648_ = v_isSharedCheck_1674_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_k_1645_);
lean_inc(v_fvarId_1644_);
lean_dec(v_c_1246_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1674_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1644_, v_a_1247_);
lean_dec(v_fvarId_1644_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref_known(v___x_1649_, 1);
if (lean_obj_tag(v_a_1650_) == 0)
{
lean_object* v_id_1651_; lean_object* v___x_1652_; 
v_id_1651_ = lean_ctor_get(v_a_1650_, 0);
lean_inc(v_id_1651_);
lean_dec_ref_known(v_a_1650_, 1);
v___x_1652_ = l_Lean_IR_ToIR_lowerCode(v_k_1645_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1663_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1663_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1663_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1648_ == 0)
{
lean_ctor_set_tag(v___x_1647_, 8);
lean_ctor_set(v___x_1647_, 1, v_a_1653_);
lean_ctor_set(v___x_1647_, 0, v_id_1651_);
v___x_1658_ = v___x_1647_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_id_1651_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1660_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1658_);
v___x_1660_ = v___x_1655_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
else
{
lean_dec(v_id_1651_);
lean_del_object(v___x_1647_);
return v___x_1652_;
}
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec(v_a_1650_);
lean_del_object(v___x_1647_);
lean_dec_ref(v_k_1645_);
v___x_1664_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__14, &l_Lean_IR_ToIR_lowerCode___closed__14_once, _init_l_Lean_IR_ToIR_lowerCode___closed__14);
v___x_1665_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1664_, v_a_1247_, v_a_1248_, v_a_1249_);
return v___x_1665_;
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
lean_del_object(v___x_1647_);
lean_dec_ref(v_k_1645_);
v_a_1666_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1649_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1649_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object* v_decl_1675_, lean_object* v_k_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v_fvarId_1681_; lean_object* v___x_1682_; 
v_fvarId_1681_ = lean_ctor_get(v_decl_1675_, 0);
lean_inc(v_fvarId_1681_);
lean_dec_ref(v_decl_1675_);
v___x_1682_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_1681_, v_a_1677_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v___x_1683_; 
lean_dec_ref_known(v___x_1682_, 1);
v___x_1683_ = l_Lean_IR_ToIR_lowerCode(v_k_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
return v___x_1683_;
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
lean_dec_ref(v_k_1676_);
v_a_1684_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v___x_1682_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1682_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg___boxed(lean_object* v_decl_1692_, lean_object* v_k_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1692_, v_k_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue___boxed(lean_object* v_decl_1699_, lean_object* v_k_1700_, lean_object* v_fvarId_1701_, lean_object* v_f_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1699_, v_k_1700_, v_fvarId_1701_, v_f_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
lean_dec(v_a_1703_);
lean_dec(v_fvarId_1701_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4___boxed(lean_object* v_sz_1708_, lean_object* v_i_1709_, lean_object* v_bs_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
size_t v_sz_boxed_1715_; size_t v_i_boxed_1716_; lean_object* v_res_1717_; 
v_sz_boxed_1715_ = lean_unbox_usize(v_sz_1708_);
lean_dec(v_sz_1708_);
v_i_boxed_1716_ = lean_unbox_usize(v_i_1709_);
lean_dec(v_i_1709_);
v_res_1717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_boxed_1715_, v_i_boxed_1716_, v_bs_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt___boxed(lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_IR_ToIR_lowerAlt(v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___boxed(lean_object* v_decl_1724_, lean_object* v_k_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_IR_ToIR_lowerLet(v_decl_1724_, v_k_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_a_1726_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode___boxed(lean_object* v_c_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_IR_ToIR_lowerCode(v_c_1731_, v_a_1732_, v_a_1733_, v_a_1734_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
lean_dec(v_a_1732_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object* v_decl_1737_, lean_object* v_k_1738_, lean_object* v_x_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1737_, v_k_1738_, v_a_1740_, v_a_1741_, v_a_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object* v_decl_1745_, lean_object* v_k_1746_, lean_object* v_x_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(v_decl_1745_, v_k_1746_, v_x_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
lean_dec(v_a_1750_);
lean_dec_ref(v_a_1749_);
lean_dec(v_a_1748_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(size_t v_sz_1753_, size_t v_i_1754_, lean_object* v_bs_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1753_, v_i_1754_, v_bs_1755_, v___y_1756_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object* v_sz_1761_, lean_object* v_i_1762_, lean_object* v_bs_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
size_t v_sz_boxed_1768_; size_t v_i_boxed_1769_; lean_object* v_res_1770_; 
v_sz_boxed_1768_ = lean_unbox_usize(v_sz_1761_);
lean_dec(v_sz_1761_);
v_i_boxed_1769_ = lean_unbox_usize(v_i_1762_);
lean_dec(v_i_1762_);
v_res_1770_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(v_sz_boxed_1768_, v_i_boxed_1769_, v_bs_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(size_t v_sz_1771_, size_t v_i_1772_, lean_object* v_bs_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1771_, v_i_1772_, v_bs_1773_, v___y_1774_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object* v_sz_1779_, lean_object* v_i_1780_, lean_object* v_bs_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
size_t v_sz_boxed_1786_; size_t v_i_boxed_1787_; lean_object* v_res_1788_; 
v_sz_boxed_1786_ = lean_unbox_usize(v_sz_1779_);
lean_dec(v_sz_1779_);
v_i_boxed_1787_ = lean_unbox_usize(v_i_1780_);
lean_dec(v_i_1780_);
v_res_1788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(v_sz_boxed_1786_, v_i_boxed_1787_, v_bs_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object* v_d_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v_toSignature_1794_; lean_object* v_value_1795_; lean_object* v_name_1796_; lean_object* v_type_1797_; lean_object* v_params_1798_; size_t v_sz_1799_; size_t v___x_1800_; lean_object* v___x_1801_; 
v_toSignature_1794_ = lean_ctor_get(v_d_1789_, 0);
lean_inc_ref(v_toSignature_1794_);
v_value_1795_ = lean_ctor_get(v_d_1789_, 1);
lean_inc_ref(v_value_1795_);
lean_dec_ref(v_d_1789_);
v_name_1796_ = lean_ctor_get(v_toSignature_1794_, 0);
lean_inc(v_name_1796_);
v_type_1797_ = lean_ctor_get(v_toSignature_1794_, 2);
lean_inc_ref(v_type_1797_);
v_params_1798_ = lean_ctor_get(v_toSignature_1794_, 3);
lean_inc_ref(v_params_1798_);
lean_dec_ref(v_toSignature_1794_);
v_sz_1799_ = lean_array_size(v_params_1798_);
v___x_1800_ = ((size_t)0ULL);
v___x_1801_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1799_, v___x_1800_, v_params_1798_, v_a_1790_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1858_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1858_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1858_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_IR_toIRType(v_type_1797_);
lean_dec_ref(v_type_1797_);
if (lean_obj_tag(v_value_1795_) == 0)
{
lean_object* v_code_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1833_; 
lean_del_object(v___x_1804_);
v_code_1807_ = lean_ctor_get(v_value_1795_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_value_1795_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1809_ = v_value_1795_;
v_isShared_1810_ = v_isSharedCheck_1833_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_code_1807_);
lean_dec(v_value_1795_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1833_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_IR_ToIR_lowerCode(v_code_1807_, v_a_1790_, v_a_1791_, v_a_1792_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1824_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1824_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1824_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1816_ = lean_box(0);
v___x_1817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1817_, 0, v_name_1796_);
lean_ctor_set(v___x_1817_, 1, v_a_1802_);
lean_ctor_set(v___x_1817_, 2, v___x_1806_);
lean_ctor_set(v___x_1817_, 3, v_a_1812_);
lean_ctor_set(v___x_1817_, 4, v___x_1816_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set_tag(v___x_1809_, 1);
lean_ctor_set(v___x_1809_, 0, v___x_1817_);
v___x_1819_ = v___x_1809_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1821_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v___x_1819_);
v___x_1821_ = v___x_1814_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
lean_del_object(v___x_1809_);
lean_dec(v___x_1806_);
lean_dec(v_a_1802_);
lean_dec(v_name_1796_);
v_a_1825_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1811_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1811_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
else
{
lean_object* v_externAttrData_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1857_; 
v_externAttrData_1834_ = lean_ctor_get(v_value_1795_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v_value_1795_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1836_ = v_value_1795_;
v_isShared_1837_ = v_isSharedCheck_1857_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_externAttrData_1834_);
lean_dec(v_value_1795_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1857_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
uint8_t v___x_1838_; 
v___x_1838_ = l_List_isEmpty___redArg(v_externAttrData_1834_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1839_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1839_, 0, v_name_1796_);
lean_ctor_set(v___x_1839_, 1, v_a_1802_);
lean_ctor_set(v___x_1839_, 2, v___x_1806_);
lean_ctor_set(v___x_1839_, 3, v_externAttrData_1834_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1839_);
v___x_1841_ = v___x_1836_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1843_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1841_);
v___x_1843_ = v___x_1804_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1855_; 
lean_del_object(v___x_1836_);
lean_dec(v_externAttrData_1834_);
lean_del_object(v___x_1804_);
v___x_1846_ = l_Lean_IR_mkDummyExternDecl(v_name_1796_, v_a_1802_, v___x_1806_);
v___x_1847_ = l_Lean_IR_ToIR_addDecl___redArg(v___x_1846_, v_a_1792_);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1855_ == 0)
{
lean_object* v_unused_1856_; 
v_unused_1856_ = lean_ctor_get(v___x_1847_, 0);
lean_dec(v_unused_1856_);
v___x_1849_ = v___x_1847_;
v_isShared_1850_ = v_isSharedCheck_1855_;
goto v_resetjp_1848_;
}
else
{
lean_dec(v___x_1847_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1855_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1851_ = lean_box(0);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1851_);
v___x_1853_ = v___x_1849_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec_ref(v_type_1797_);
lean_dec(v_name_1796_);
lean_dec_ref(v_value_1795_);
v_a_1859_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1801_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1801_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl___boxed(lean_object* v_d_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_IR_ToIR_lowerDecl(v_d_1867_, v_a_1868_, v_a_1869_, v_a_1870_);
lean_dec(v_a_1870_);
lean_dec_ref(v_a_1869_);
lean_dec(v_a_1868_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(lean_object* v_as_1873_, size_t v_sz_1874_, size_t v_i_1875_, lean_object* v_b_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
uint8_t v___x_1880_; 
v___x_1880_ = lean_usize_dec_lt(v_i_1875_, v_sz_1874_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v_b_1876_);
return v___x_1881_;
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v_a_1882_ = lean_array_uget_borrowed(v_as_1873_, v_i_1875_);
lean_inc(v_a_1882_);
v___x_1883_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerDecl___boxed), 5, 1);
lean_closure_set(v___x_1883_, 0, v_a_1882_);
v___x_1884_ = l_Lean_IR_ToIR_M_run___redArg(v___x_1883_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v_a_1887_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref_known(v___x_1884_, 1);
if (lean_obj_tag(v_a_1885_) == 1)
{
lean_object* v_val_1891_; lean_object* v___x_1892_; 
v_val_1891_ = lean_ctor_get(v_a_1885_, 0);
lean_inc(v_val_1891_);
lean_dec_ref_known(v_a_1885_, 1);
v___x_1892_ = lean_array_push(v_b_1876_, v_val_1891_);
v_a_1887_ = v___x_1892_;
goto v___jp_1886_;
}
else
{
lean_dec(v_a_1885_);
v_a_1887_ = v_b_1876_;
goto v___jp_1886_;
}
v___jp_1886_:
{
size_t v___x_1888_; size_t v___x_1889_; 
v___x_1888_ = ((size_t)1ULL);
v___x_1889_ = lean_usize_add(v_i_1875_, v___x_1888_);
v_i_1875_ = v___x_1889_;
v_b_1876_ = v_a_1887_;
goto _start;
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec_ref(v_b_1876_);
v_a_1893_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1884_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1884_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0___boxed(lean_object* v_as_1901_, lean_object* v_sz_1902_, lean_object* v_i_1903_, lean_object* v_b_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
size_t v_sz_boxed_1908_; size_t v_i_boxed_1909_; lean_object* v_res_1910_; 
v_sz_boxed_1908_ = lean_unbox_usize(v_sz_1902_);
lean_dec(v_sz_1902_);
v_i_boxed_1909_ = lean_unbox_usize(v_i_1903_);
lean_dec(v_i_1903_);
v_res_1910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_as_1901_, v_sz_boxed_1908_, v_i_boxed_1909_, v_b_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec_ref(v_as_1901_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object* v_decls_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v_irDecls_1917_; size_t v_sz_1918_; size_t v___x_1919_; lean_object* v___x_1920_; 
v_irDecls_1917_ = ((lean_object*)(l_Lean_IR_toIR___closed__0));
v_sz_1918_ = lean_array_size(v_decls_1913_);
v___x_1919_ = ((size_t)0ULL);
v___x_1920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_decls_1913_, v_sz_1918_, v___x_1919_, v_irDecls_1917_, v_a_1914_, v_a_1915_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object* v_decls_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_IR_toIR(v_decls_1921_, v_a_1922_, v_a_1923_);
lean_dec(v_a_1923_);
lean_dec_ref(v_a_1922_);
lean_dec_ref(v_decls_1921_);
return v_res_1925_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_ToIR(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_ToIRType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_IR_ToIR(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Compiler_IR_ToIR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR_ToIR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR_ToIR(builtin);
}
#ifdef __cplusplus
}
#endif
