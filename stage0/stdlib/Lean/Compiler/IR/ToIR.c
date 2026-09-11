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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v_nbuckets_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_222_ = lean_array_get_size(v_data_221_);
v___x_223_ = lean_unsigned_to_nat(2u);
v_nbuckets_224_ = lean_nat_mul(v___x_222_, v___x_223_);
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_box(0);
v___x_227_ = lean_mk_array(v_nbuckets_224_, v___x_226_);
v___x_228_ = lean_array_propagate_mark(v_data_221_, v___x_227_);
v___x_229_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(v___x_225_, v_data_221_, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(lean_object* v_m_230_, lean_object* v_a_231_, lean_object* v_b_232_){
_start:
{
lean_object* v_size_233_; lean_object* v_buckets_234_; lean_object* v___x_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v_fold_239_; uint64_t v___x_240_; uint64_t v___x_241_; uint64_t v___x_242_; size_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; size_t v___x_247_; lean_object* v_bkt_248_; uint8_t v___x_249_; 
v_size_233_ = lean_ctor_get(v_m_230_, 0);
v_buckets_234_ = lean_ctor_get(v_m_230_, 1);
v___x_235_ = lean_array_get_size(v_buckets_234_);
v___x_236_ = l_Lean_instHashableFVarId_hash(v_a_231_);
v___x_237_ = 32ULL;
v___x_238_ = lean_uint64_shift_right(v___x_236_, v___x_237_);
v_fold_239_ = lean_uint64_xor(v___x_236_, v___x_238_);
v___x_240_ = 16ULL;
v___x_241_ = lean_uint64_shift_right(v_fold_239_, v___x_240_);
v___x_242_ = lean_uint64_xor(v_fold_239_, v___x_241_);
v___x_243_ = lean_uint64_to_usize(v___x_242_);
v___x_244_ = lean_usize_of_nat(v___x_235_);
v___x_245_ = ((size_t)1ULL);
v___x_246_ = lean_usize_sub(v___x_244_, v___x_245_);
v___x_247_ = lean_usize_land(v___x_243_, v___x_246_);
v_bkt_248_ = lean_array_uget_borrowed(v_buckets_234_, v___x_247_);
v___x_249_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_a_231_, v_bkt_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_270_; 
lean_inc_ref(v_buckets_234_);
lean_inc(v_size_233_);
v_isSharedCheck_270_ = !lean_is_exclusive(v_m_230_);
if (v_isSharedCheck_270_ == 0)
{
lean_object* v_unused_271_; lean_object* v_unused_272_; 
v_unused_271_ = lean_ctor_get(v_m_230_, 1);
lean_dec(v_unused_271_);
v_unused_272_ = lean_ctor_get(v_m_230_, 0);
lean_dec(v_unused_272_);
v___x_251_ = v_m_230_;
v_isShared_252_ = v_isSharedCheck_270_;
goto v_resetjp_250_;
}
else
{
lean_dec(v_m_230_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_270_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v_size_x27_254_; lean_object* v___x_255_; lean_object* v_buckets_x27_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_253_ = lean_unsigned_to_nat(1u);
v_size_x27_254_ = lean_nat_add(v_size_233_, v___x_253_);
lean_dec(v_size_233_);
lean_inc(v_bkt_248_);
v___x_255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_255_, 0, v_a_231_);
lean_ctor_set(v___x_255_, 1, v_b_232_);
lean_ctor_set(v___x_255_, 2, v_bkt_248_);
v_buckets_x27_256_ = lean_array_uset(v_buckets_234_, v___x_247_, v___x_255_);
v___x_257_ = lean_unsigned_to_nat(4u);
v___x_258_ = lean_nat_mul(v_size_x27_254_, v___x_257_);
v___x_259_ = lean_unsigned_to_nat(3u);
v___x_260_ = lean_nat_div(v___x_258_, v___x_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_array_get_size(v_buckets_x27_256_);
v___x_262_ = lean_nat_dec_le(v___x_260_, v___x_261_);
lean_dec(v___x_260_);
if (v___x_262_ == 0)
{
lean_object* v_val_263_; lean_object* v___x_265_; 
v_val_263_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(v_buckets_x27_256_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v_val_263_);
lean_ctor_set(v___x_251_, 0, v_size_x27_254_);
v___x_265_ = v___x_251_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_size_x27_254_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_val_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
else
{
lean_object* v___x_268_; 
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v_buckets_x27_256_);
lean_ctor_set(v___x_251_, 0, v_size_x27_254_);
v___x_268_ = v___x_251_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_size_x27_254_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_buckets_x27_256_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_dec(v_b_232_);
lean_dec(v_a_231_);
return v_m_230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object* v_fvarId_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_276_; lean_object* v_vars_277_; lean_object* v_joinPoints_278_; lean_object* v_nextId_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_292_; 
v___x_276_ = lean_st_ref_take(v_a_274_);
v_vars_277_ = lean_ctor_get(v___x_276_, 0);
v_joinPoints_278_ = lean_ctor_get(v___x_276_, 1);
v_nextId_279_ = lean_ctor_get(v___x_276_, 2);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_292_ == 0)
{
v___x_281_ = v___x_276_;
v_isShared_282_ = v_isSharedCheck_292_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_nextId_279_);
lean_inc(v_joinPoints_278_);
lean_inc(v_vars_277_);
lean_dec(v___x_276_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_292_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
lean_inc(v_nextId_279_);
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v_nextId_279_);
v___x_284_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_277_, v_fvarId_273_, v___x_283_);
v___x_285_ = lean_unsigned_to_nat(1u);
v___x_286_ = lean_nat_add(v_nextId_279_, v___x_285_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 2, v___x_286_);
lean_ctor_set(v___x_281_, 0, v___x_284_);
v___x_288_ = v___x_281_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_joinPoints_278_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v___x_286_);
v___x_288_ = v_reuseFailAlloc_291_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_st_ref_put(v_a_274_, v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v_nextId_279_);
return v___x_290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg___boxed(lean_object* v_fvarId_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_293_, v_a_294_);
lean_dec(v_a_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object* v_fvarId_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_297_, v_a_298_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object* v_fvarId_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_IR_ToIR_bindVar(v_fvarId_303_, v_a_304_, v_a_305_, v_a_306_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec(v_a_304_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0(lean_object* v_00_u03b2_309_, lean_object* v_m_310_, lean_object* v_a_311_, lean_object* v_b_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_m_310_, v_a_311_, v_b_312_);
return v___x_313_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(lean_object* v_00_u03b2_314_, lean_object* v_a_315_, lean_object* v_x_316_){
_start:
{
uint8_t v___x_317_; 
v___x_317_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_a_315_, v_x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_318_, lean_object* v_a_319_, lean_object* v_x_320_){
_start:
{
uint8_t v_res_321_; lean_object* v_r_322_; 
v_res_321_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(v_00_u03b2_318_, v_a_319_, v_x_320_);
lean_dec(v_x_320_);
lean_dec(v_a_319_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1(lean_object* v_00_u03b2_323_, lean_object* v_data_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(v_data_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_326_, lean_object* v_i_327_, lean_object* v_source_328_, lean_object* v_target_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(v_i_327_, v_source_328_, v_target_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_331_, lean_object* v_x_332_, lean_object* v_x_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_332_, v_x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object* v_fvarId_335_, lean_object* v_a_336_){
_start:
{
lean_object* v___x_338_; lean_object* v_vars_339_; lean_object* v_joinPoints_340_; lean_object* v_nextId_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_353_; 
v___x_338_ = lean_st_ref_take(v_a_336_);
v_vars_339_ = lean_ctor_get(v___x_338_, 0);
v_joinPoints_340_ = lean_ctor_get(v___x_338_, 1);
v_nextId_341_ = lean_ctor_get(v___x_338_, 2);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_353_ == 0)
{
v___x_343_ = v___x_338_;
v_isShared_344_ = v_isSharedCheck_353_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_nextId_341_);
lean_inc(v_joinPoints_340_);
lean_inc(v_vars_339_);
lean_dec(v___x_338_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_353_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_349_; 
lean_inc(v_nextId_341_);
v___x_345_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_joinPoints_340_, v_fvarId_335_, v_nextId_341_);
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = lean_nat_add(v_nextId_341_, v___x_346_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 2, v___x_347_);
lean_ctor_set(v___x_343_, 1, v___x_345_);
v___x_349_ = v___x_343_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_vars_339_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_352_, 2, v___x_347_);
v___x_349_ = v_reuseFailAlloc_352_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_st_ref_put(v_a_336_, v___x_349_);
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v_nextId_341_);
return v___x_351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object* v_fvarId_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_354_, v_a_355_);
lean_dec(v_a_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object* v_fvarId_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_358_, v_a_359_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object* v_fvarId_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_IR_ToIR_bindJoinPoint(v_fvarId_364_, v_a_365_, v_a_366_, v_a_367_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object* v_fvarId_370_, lean_object* v_a_371_){
_start:
{
lean_object* v___x_373_; lean_object* v_vars_374_; lean_object* v_joinPoints_375_; lean_object* v_nextId_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_388_; 
v___x_373_ = lean_st_ref_take(v_a_371_);
v_vars_374_ = lean_ctor_get(v___x_373_, 0);
v_joinPoints_375_ = lean_ctor_get(v___x_373_, 1);
v_nextId_376_ = lean_ctor_get(v___x_373_, 2);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_388_ == 0)
{
v___x_378_ = v___x_373_;
v_isShared_379_ = v_isSharedCheck_388_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_nextId_376_);
lean_inc(v_joinPoints_375_);
lean_inc(v_vars_374_);
lean_dec(v___x_373_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_388_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_380_ = lean_box(1);
v___x_381_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_374_, v_fvarId_370_, v___x_380_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_381_);
v___x_383_ = v___x_378_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_joinPoints_375_);
lean_ctor_set(v_reuseFailAlloc_387_, 2, v_nextId_376_);
v___x_383_ = v_reuseFailAlloc_387_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = lean_st_ref_put(v_a_371_, v___x_383_);
v___x_385_ = lean_box(0);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg___boxed(lean_object* v_fvarId_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_389_, v_a_390_);
lean_dec(v_a_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object* v_fvarId_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_393_, v_a_394_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object* v_fvarId_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_IR_ToIR_bindErased(v_fvarId_399_, v_a_400_, v_a_401_, v_a_402_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_a_400_);
return v_res_404_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_405_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__0, &l_Lean_IR_ToIR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__1, &l_Lean_IR_ToIR_addDecl___redArg___closed__1_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1);
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object* v_d_410_, lean_object* v_a_411_){
_start:
{
lean_object* v___x_413_; lean_object* v_env_414_; lean_object* v_nextMacroScope_415_; lean_object* v_ngen_416_; lean_object* v_auxDeclNGen_417_; lean_object* v_traceState_418_; lean_object* v_messages_419_; lean_object* v_infoState_420_; lean_object* v_snapshotTasks_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_437_; 
v___x_413_ = lean_st_ref_take(v_a_411_);
v_env_414_ = lean_ctor_get(v___x_413_, 0);
v_nextMacroScope_415_ = lean_ctor_get(v___x_413_, 1);
v_ngen_416_ = lean_ctor_get(v___x_413_, 2);
v_auxDeclNGen_417_ = lean_ctor_get(v___x_413_, 3);
v_traceState_418_ = lean_ctor_get(v___x_413_, 4);
v_messages_419_ = lean_ctor_get(v___x_413_, 6);
v_infoState_420_ = lean_ctor_get(v___x_413_, 7);
v_snapshotTasks_421_ = lean_ctor_get(v___x_413_, 8);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; 
v_unused_438_ = lean_ctor_get(v___x_413_, 5);
lean_dec(v_unused_438_);
v___x_423_ = v___x_413_;
v_isShared_424_ = v_isSharedCheck_437_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_snapshotTasks_421_);
lean_inc(v_infoState_420_);
lean_inc(v_messages_419_);
lean_inc(v_traceState_418_);
lean_inc(v_auxDeclNGen_417_);
lean_inc(v_ngen_416_);
lean_inc(v_nextMacroScope_415_);
lean_inc(v_env_414_);
lean_dec(v___x_413_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_437_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v_toEnvExtension_426_; lean_object* v_asyncMode_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_425_ = l_Lean_IR_declMapExt;
v_toEnvExtension_426_ = lean_ctor_get(v___x_425_, 0);
v_asyncMode_427_ = lean_ctor_get(v_toEnvExtension_426_, 2);
v___x_428_ = lean_box(0);
v___x_429_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_425_, v_env_414_, v_d_410_, v_asyncMode_427_, v___x_428_);
v___x_430_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__2, &l_Lean_IR_ToIR_addDecl___redArg___closed__2_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 5, v___x_430_);
lean_ctor_set(v___x_423_, 0, v___x_429_);
v___x_432_ = v___x_423_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_nextMacroScope_415_);
lean_ctor_set(v_reuseFailAlloc_436_, 2, v_ngen_416_);
lean_ctor_set(v_reuseFailAlloc_436_, 3, v_auxDeclNGen_417_);
lean_ctor_set(v_reuseFailAlloc_436_, 4, v_traceState_418_);
lean_ctor_set(v_reuseFailAlloc_436_, 5, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_436_, 6, v_messages_419_);
lean_ctor_set(v_reuseFailAlloc_436_, 7, v_infoState_420_);
lean_ctor_set(v_reuseFailAlloc_436_, 8, v_snapshotTasks_421_);
v___x_432_ = v_reuseFailAlloc_436_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_433_ = lean_st_ref_put(v_a_411_, v___x_432_);
v___x_434_ = lean_box(0);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object* v_d_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_439_, v_a_440_);
lean_dec(v_a_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object* v_d_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_443_, v_a_446_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object* v_d_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_IR_ToIR_addDecl(v_d_449_, v_a_450_, v_a_451_, v_a_452_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object* v_v_455_){
_start:
{
switch(lean_obj_tag(v_v_455_))
{
case 0:
{
lean_object* v_val_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_470_; 
v_val_456_ = lean_ctor_get(v_v_455_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v_v_455_);
if (v_isSharedCheck_470_ == 0)
{
v___x_458_ = v_v_455_;
v_isShared_459_ = v_isSharedCheck_470_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_val_456_);
lean_dec(v_v_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_470_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___y_461_; lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_cstr_to_nat("4294967296");
v___x_467_ = lean_nat_dec_lt(v_val_456_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; 
v___x_468_ = lean_box(8);
v___y_461_ = v___x_468_;
goto v___jp_460_;
}
else
{
lean_object* v___x_469_; 
v___x_469_ = lean_box(12);
v___y_461_ = v___x_469_;
goto v___jp_460_;
}
v___jp_460_:
{
lean_object* v___x_463_; 
if (v_isShared_459_ == 0)
{
v___x_463_ = v___x_458_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_val_456_);
v___x_463_ = v_reuseFailAlloc_465_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; 
lean_inc(v___y_461_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___y_461_);
return v___x_464_;
}
}
}
}
case 1:
{
lean_object* v_val_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_480_; 
v_val_471_ = lean_ctor_get(v_v_455_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v_v_455_);
if (v_isSharedCheck_480_ == 0)
{
v___x_473_ = v_v_455_;
v_isShared_474_ = v_isSharedCheck_480_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_val_471_);
lean_dec(v_v_455_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_480_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_val_471_);
v___x_476_ = v_reuseFailAlloc_479_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_box(7);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_476_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
return v___x_478_;
}
}
}
case 2:
{
uint8_t v_val_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_val_481_ = lean_ctor_get_uint8(v_v_455_, 0);
lean_dec_ref_known(v_v_455_, 0);
v___x_482_ = lean_uint8_to_nat(v_val_481_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
v___x_484_ = lean_box(1);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_483_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
return v___x_485_;
}
case 3:
{
uint16_t v_val_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_val_486_ = lean_ctor_get_uint16(v_v_455_, 0);
lean_dec_ref_known(v_v_455_, 0);
v___x_487_ = lean_uint16_to_nat(v_val_486_);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
v___x_489_ = lean_box(2);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
return v___x_490_;
}
case 4:
{
uint32_t v_val_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_val_491_ = lean_ctor_get_uint32(v_v_455_, 0);
lean_dec_ref_known(v_v_455_, 0);
v___x_492_ = lean_uint32_to_nat(v_val_491_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
v___x_494_ = lean_box(3);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_493_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
return v___x_495_;
}
case 5:
{
uint64_t v_val_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_val_496_ = lean_ctor_get_uint64(v_v_455_, 0);
lean_dec_ref_known(v_v_455_, 0);
v___x_497_ = lean_uint64_to_nat(v_val_496_);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
v___x_499_ = lean_box(4);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
return v___x_500_;
}
default: 
{
uint64_t v_val_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_val_501_ = lean_ctor_get_uint64(v_v_455_, 0);
lean_dec_ref_known(v_v_455_, 0);
v___x_502_ = lean_uint64_to_nat(v_val_501_);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
v___x_504_ = lean_box(5);
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_503_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
return v___x_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
if (lean_obj_tag(v_a_506_) == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_box(1);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
else
{
lean_object* v_fvarId_511_; lean_object* v___x_512_; 
v_fvarId_511_ = lean_ctor_get(v_a_506_, 0);
v___x_512_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_511_, v_a_507_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_513_, v_a_514_);
lean_dec(v_a_514_);
lean_dec(v_a_513_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_517_, v_a_518_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_IR_ToIR_lowerArg(v_a_523_, v_a_524_, v_a_525_, v_a_526_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec(v_a_523_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg(lean_object* v_p_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_fvarId_532_; lean_object* v_type_533_; uint8_t v_borrow_534_; lean_object* v___x_535_; lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_549_; 
v_fvarId_532_ = lean_ctor_get(v_p_529_, 0);
lean_inc(v_fvarId_532_);
v_type_533_ = lean_ctor_get(v_p_529_, 2);
lean_inc_ref(v_type_533_);
v_borrow_534_ = lean_ctor_get_uint8(v_p_529_, sizeof(void*)*3);
lean_dec_ref(v_p_529_);
v___x_535_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_532_, v_a_530_);
v_a_536_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_549_ == 0)
{
v___x_538_ = v___x_535_;
v_isShared_539_ = v_isSharedCheck_549_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_535_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_549_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; uint8_t v___y_542_; 
v___x_540_ = l_Lean_IR_toIRType(v_type_533_);
lean_dec_ref(v_type_533_);
if (v_borrow_534_ == 0)
{
v___y_542_ = v_borrow_534_;
goto v___jp_541_;
}
else
{
uint8_t v___x_547_; 
v___x_547_ = l_Lean_IR_IRType_isScalar(v___x_540_);
if (v___x_547_ == 0)
{
v___y_542_ = v_borrow_534_;
goto v___jp_541_;
}
else
{
uint8_t v___x_548_; 
v___x_548_ = 0;
v___y_542_ = v___x_548_;
goto v___jp_541_;
}
}
v___jp_541_:
{
lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_543_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_543_, 0, v_a_536_);
lean_ctor_set(v___x_543_, 1, v___x_540_);
lean_ctor_set_uint8(v___x_543_, sizeof(void*)*2, v___y_542_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_543_);
v___x_545_ = v___x_538_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg___boxed(lean_object* v_p_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_550_, v_a_551_);
lean_dec(v_a_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object* v_p_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_554_, v_a_555_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object* v_p_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_IR_ToIR_lowerParam(v_p_560_, v_a_561_, v_a_562_, v_a_563_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCtorInfo(lean_object* v_i_566_){
_start:
{
lean_object* v_name_567_; lean_object* v_cidx_568_; lean_object* v_size_569_; lean_object* v_usize_570_; lean_object* v_ssize_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
v_name_567_ = lean_ctor_get(v_i_566_, 0);
v_cidx_568_ = lean_ctor_get(v_i_566_, 1);
v_size_569_ = lean_ctor_get(v_i_566_, 2);
v_usize_570_ = lean_ctor_get(v_i_566_, 3);
v_ssize_571_ = lean_ctor_get(v_i_566_, 4);
v_isSharedCheck_578_ = !lean_is_exclusive(v_i_566_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v_i_566_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_ssize_571_);
lean_inc(v_usize_570_);
lean_inc(v_size_569_);
lean_inc(v_cidx_568_);
lean_inc(v_name_567_);
lean_dec(v_i_566_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_name_567_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_cidx_568_);
lean_ctor_set(v_reuseFailAlloc_577_, 2, v_size_569_);
lean_ctor_set(v_reuseFailAlloc_577_, 3, v_usize_570_);
lean_ctor_set(v_reuseFailAlloc_577_, 4, v_ssize_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0(void){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_instMonadEIO(lean_box(0));
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(lean_object* v_msg_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v_toApplicative_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_621_; 
v___x_587_ = lean_obj_once(&l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0, &l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0_once, _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0);
v___x_588_ = l_StateRefT_x27_instMonad___redArg(v___x_587_);
v_toApplicative_589_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; 
v_unused_622_ = lean_ctor_get(v___x_588_, 1);
lean_dec(v_unused_622_);
v___x_591_ = v___x_588_;
v_isShared_592_ = v_isSharedCheck_621_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_toApplicative_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_621_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v_toFunctor_593_; lean_object* v_toSeq_594_; lean_object* v_toSeqLeft_595_; lean_object* v_toSeqRight_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_619_; 
v_toFunctor_593_ = lean_ctor_get(v_toApplicative_589_, 0);
v_toSeq_594_ = lean_ctor_get(v_toApplicative_589_, 2);
v_toSeqLeft_595_ = lean_ctor_get(v_toApplicative_589_, 3);
v_toSeqRight_596_ = lean_ctor_get(v_toApplicative_589_, 4);
v_isSharedCheck_619_ = !lean_is_exclusive(v_toApplicative_589_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; 
v_unused_620_ = lean_ctor_get(v_toApplicative_589_, 1);
lean_dec(v_unused_620_);
v___x_598_ = v_toApplicative_589_;
v_isShared_599_ = v_isSharedCheck_619_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_toSeqRight_596_);
lean_inc(v_toSeqLeft_595_);
lean_inc(v_toSeq_594_);
lean_inc(v_toFunctor_593_);
lean_dec(v_toApplicative_589_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_619_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___f_600_; lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___f_603_; lean_object* v___x_604_; lean_object* v___f_605_; lean_object* v___f_606_; lean_object* v___f_607_; lean_object* v___x_609_; 
v___f_600_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1));
v___f_601_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2));
lean_inc_ref(v_toFunctor_593_);
v___f_602_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_602_, 0, v_toFunctor_593_);
v___f_603_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_603_, 0, v_toFunctor_593_);
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v___f_602_);
lean_ctor_set(v___x_604_, 1, v___f_603_);
v___f_605_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_605_, 0, v_toSeqRight_596_);
v___f_606_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_606_, 0, v_toSeqLeft_595_);
v___f_607_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_607_, 0, v_toSeq_594_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 4, v___f_605_);
lean_ctor_set(v___x_598_, 3, v___f_606_);
lean_ctor_set(v___x_598_, 2, v___f_607_);
lean_ctor_set(v___x_598_, 1, v___f_600_);
lean_ctor_set(v___x_598_, 0, v___x_604_);
v___x_609_ = v___x_598_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v___f_600_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v___f_607_);
lean_ctor_set(v_reuseFailAlloc_618_, 3, v___f_606_);
lean_ctor_set(v_reuseFailAlloc_618_, 4, v___f_605_);
v___x_609_ = v_reuseFailAlloc_618_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_611_; 
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v___f_601_);
lean_ctor_set(v___x_591_, 0, v___x_609_);
v___x_611_ = v___x_591_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v___f_601_);
v___x_611_ = v_reuseFailAlloc_617_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_8394__overap_615_; lean_object* v___x_616_; 
v___x_612_ = l_StateRefT_x27_instMonad___redArg(v___x_611_);
v___x_613_ = l_Lean_IR_instInhabitedFnBody_default__1;
v___x_614_ = l_instInhabitedOfMonad___redArg(v___x_612_, v___x_613_);
v___x_8394__overap_615_ = lean_panic_fn_borrowed(v___x_614_, v_msg_582_);
lean_dec(v___x_614_);
lean_inc(v___y_585_);
lean_inc_ref(v___y_584_);
lean_inc(v___y_583_);
v___x_616_ = lean_apply_4(v___x_8394__overap_615_, v___y_583_, v___y_584_, v___y_585_, lean_box(0));
return v___x_616_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object* v_msg_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v_msg_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(size_t v_sz_629_, size_t v_i_630_, lean_object* v_bs_631_, lean_object* v___y_632_){
_start:
{
uint8_t v___x_634_; 
v___x_634_ = lean_usize_dec_lt(v_i_630_, v_sz_629_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v_bs_631_);
return v___x_635_;
}
else
{
lean_object* v_v_636_; lean_object* v___x_637_; 
v_v_636_ = lean_array_uget_borrowed(v_bs_631_, v_i_630_);
v___x_637_ = l_Lean_IR_ToIR_lowerArg___redArg(v_v_636_, v___y_632_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_639_; lean_object* v_bs_x27_640_; size_t v___x_641_; size_t v___x_642_; lean_object* v___x_643_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_637_, 1);
v___x_639_ = lean_unsigned_to_nat(0u);
v_bs_x27_640_ = lean_array_uset(v_bs_631_, v_i_630_, v___x_639_);
v___x_641_ = ((size_t)1ULL);
v___x_642_ = lean_usize_add(v_i_630_, v___x_641_);
v___x_643_ = lean_array_uset(v_bs_x27_640_, v_i_630_, v_a_638_);
v_i_630_ = v___x_642_;
v_bs_631_ = v___x_643_;
goto _start;
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec_ref(v_bs_631_);
v_a_645_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_637_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_637_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object* v_sz_653_, lean_object* v_i_654_, lean_object* v_bs_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
size_t v_sz_boxed_658_; size_t v_i_boxed_659_; lean_object* v_res_660_; 
v_sz_boxed_658_ = lean_unbox_usize(v_sz_653_);
lean_dec(v_sz_653_);
v_i_boxed_659_ = lean_unbox_usize(v_i_654_);
lean_dec(v_i_654_);
v_res_660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_boxed_658_, v_i_boxed_659_, v_bs_655_, v___y_656_);
lean_dec(v___y_656_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(size_t v_sz_661_, size_t v_i_662_, lean_object* v_bs_663_, lean_object* v___y_664_){
_start:
{
uint8_t v___x_666_; 
v___x_666_ = lean_usize_dec_lt(v_i_662_, v_sz_661_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v_bs_663_);
return v___x_667_;
}
else
{
lean_object* v_v_668_; lean_object* v___x_669_; 
v_v_668_ = lean_array_uget_borrowed(v_bs_663_, v_i_662_);
lean_inc(v_v_668_);
v___x_669_ = l_Lean_IR_ToIR_lowerParam___redArg(v_v_668_, v___y_664_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_671_; lean_object* v_bs_x27_672_; size_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
v___x_671_ = lean_unsigned_to_nat(0u);
v_bs_x27_672_ = lean_array_uset(v_bs_663_, v_i_662_, v___x_671_);
v___x_673_ = ((size_t)1ULL);
v___x_674_ = lean_usize_add(v_i_662_, v___x_673_);
v___x_675_ = lean_array_uset(v_bs_x27_672_, v_i_662_, v_a_670_);
v_i_662_ = v___x_674_;
v_bs_663_ = v___x_675_;
goto _start;
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec_ref(v_bs_663_);
v_a_677_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_669_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_669_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg___boxed(lean_object* v_sz_685_, lean_object* v_i_686_, lean_object* v_bs_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
size_t v_sz_boxed_690_; size_t v_i_boxed_691_; lean_object* v_res_692_; 
v_sz_boxed_690_ = lean_unbox_usize(v_sz_685_);
lean_dec(v_sz_685_);
v_i_boxed_691_ = lean_unbox_usize(v_i_686_);
lean_dec(v_i_686_);
v_res_692_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_boxed_690_, v_i_boxed_691_, v_bs_687_, v___y_688_);
lean_dec(v___y_688_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2(lean_object* v_i_693_, lean_object* v_continueLet_694_, lean_object* v_var_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_700_, 0, v_i_693_);
lean_ctor_set(v___x_700_, 1, v_var_695_);
lean_inc(v___y_698_);
lean_inc_ref(v___y_697_);
lean_inc(v___y_696_);
v___x_701_ = lean_apply_5(v_continueLet_694_, v___x_700_, v___y_696_, v___y_697_, v___y_698_, lean_box(0));
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2___boxed(lean_object* v_i_702_, lean_object* v_continueLet_703_, lean_object* v_var_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_IR_ToIR_lowerLet___lam__2(v_i_702_, v_continueLet_703_, v_var_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4(lean_object* v_n_710_, lean_object* v_offset_711_, lean_object* v_continueLet_712_, lean_object* v_var_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_718_, 0, v_n_710_);
lean_ctor_set(v___x_718_, 1, v_offset_711_);
lean_ctor_set(v___x_718_, 2, v_var_713_);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
lean_inc(v___y_714_);
v___x_719_ = lean_apply_5(v_continueLet_712_, v___x_718_, v___y_714_, v___y_715_, v___y_716_, lean_box(0));
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4___boxed(lean_object* v_n_720_, lean_object* v_offset_721_, lean_object* v_continueLet_722_, lean_object* v_var_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_IR_ToIR_lowerLet___lam__4(v_n_720_, v_offset_721_, v_continueLet_722_, v_var_723_, v___y_724_, v___y_725_, v___y_726_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5(lean_object* v_n_729_, lean_object* v_continueLet_730_, lean_object* v_var_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_736_, 0, v_n_729_);
lean_ctor_set(v___x_736_, 1, v_var_731_);
lean_inc(v___y_734_);
lean_inc_ref(v___y_733_);
lean_inc(v___y_732_);
v___x_737_ = lean_apply_5(v_continueLet_730_, v___x_736_, v___y_732_, v___y_733_, v___y_734_, lean_box(0));
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5___boxed(lean_object* v_n_738_, lean_object* v_continueLet_739_, lean_object* v_var_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_IR_ToIR_lowerLet___lam__5(v_n_738_, v_continueLet_739_, v_var_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8(lean_object* v_continueLet_746_, lean_object* v_var_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_752_, 0, v_var_747_);
lean_inc(v___y_750_);
lean_inc_ref(v___y_749_);
lean_inc(v___y_748_);
v___x_753_ = lean_apply_5(v_continueLet_746_, v___x_752_, v___y_748_, v___y_749_, v___y_750_, lean_box(0));
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8___boxed(lean_object* v_continueLet_754_, lean_object* v_var_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_IR_ToIR_lowerLet___lam__8(v_continueLet_754_, v_var_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3(lean_object* v_i_761_, lean_object* v_continueLet_762_, lean_object* v_var_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_768_, 0, v_i_761_);
lean_ctor_set(v___x_768_, 1, v_var_763_);
lean_inc(v___y_766_);
lean_inc_ref(v___y_765_);
lean_inc(v___y_764_);
v___x_769_ = lean_apply_5(v_continueLet_762_, v___x_768_, v___y_764_, v___y_765_, v___y_766_, lean_box(0));
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3___boxed(lean_object* v_i_770_, lean_object* v_continueLet_771_, lean_object* v_var_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_IR_ToIR_lowerLet___lam__3(v_i_770_, v_continueLet_771_, v_var_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7(lean_object* v_ty_778_, lean_object* v_continueLet_779_, lean_object* v_var_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = l_Lean_IR_toIRType(v_ty_778_);
v___x_786_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
lean_ctor_set(v___x_786_, 1, v_var_780_);
lean_inc(v___y_783_);
lean_inc_ref(v___y_782_);
lean_inc(v___y_781_);
v___x_787_ = lean_apply_5(v_continueLet_779_, v___x_786_, v___y_781_, v___y_782_, v___y_783_, lean_box(0));
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7___boxed(lean_object* v_ty_788_, lean_object* v_continueLet_789_, lean_object* v_var_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_IR_ToIR_lowerLet___lam__7(v_ty_788_, v_continueLet_789_, v_var_790_, v___y_791_, v___y_792_, v___y_793_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec_ref(v_ty_788_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6(lean_object* v_args_796_, lean_object* v_i_797_, uint8_t v_updateHeader_798_, lean_object* v_continueLet_799_, lean_object* v_var_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
size_t v_sz_805_; size_t v___x_806_; lean_object* v___x_807_; 
v_sz_805_ = lean_array_size(v_args_796_);
v___x_806_ = ((size_t)0ULL);
v___x_807_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_805_, v___x_806_, v_args_796_, v___y_801_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v_name_809_; lean_object* v_cidx_810_; lean_object* v_size_811_; lean_object* v_usize_812_; lean_object* v_ssize_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_822_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_807_, 1);
v_name_809_ = lean_ctor_get(v_i_797_, 0);
v_cidx_810_ = lean_ctor_get(v_i_797_, 1);
v_size_811_ = lean_ctor_get(v_i_797_, 2);
v_usize_812_ = lean_ctor_get(v_i_797_, 3);
v_ssize_813_ = lean_ctor_get(v_i_797_, 4);
v_isSharedCheck_822_ = !lean_is_exclusive(v_i_797_);
if (v_isSharedCheck_822_ == 0)
{
v___x_815_ = v_i_797_;
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_ssize_813_);
lean_inc(v_usize_812_);
lean_inc(v_size_811_);
lean_inc(v_cidx_810_);
lean_inc(v_name_809_);
lean_dec(v_i_797_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_name_809_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_cidx_810_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v_size_811_);
lean_ctor_set(v_reuseFailAlloc_821_, 3, v_usize_812_);
lean_ctor_set(v_reuseFailAlloc_821_, 4, v_ssize_813_);
v___x_818_ = v_reuseFailAlloc_821_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v___x_819_, 0, v_var_800_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
lean_ctor_set(v___x_819_, 2, v_a_808_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*3, v_updateHeader_798_);
lean_inc(v___y_803_);
lean_inc_ref(v___y_802_);
lean_inc(v___y_801_);
v___x_820_ = lean_apply_5(v_continueLet_799_, v___x_819_, v___y_801_, v___y_802_, v___y_803_, lean_box(0));
return v___x_820_;
}
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec(v_var_800_);
lean_dec_ref(v_continueLet_799_);
lean_dec_ref(v_i_797_);
v_a_823_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_807_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_807_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6___boxed(lean_object* v_args_831_, lean_object* v_i_832_, lean_object* v_updateHeader_833_, lean_object* v_continueLet_834_, lean_object* v_var_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
uint8_t v_updateHeader_9430__boxed_840_; lean_object* v_res_841_; 
v_updateHeader_9430__boxed_840_ = lean_unbox(v_updateHeader_833_);
v_res_841_ = l_Lean_IR_ToIR_lowerLet___lam__6(v_args_831_, v_i_832_, v_updateHeader_9430__boxed_840_, v_continueLet_834_, v_var_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9(lean_object* v_continueLet_842_, lean_object* v_var_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_848_, 0, v_var_843_);
lean_inc(v___y_846_);
lean_inc_ref(v___y_845_);
lean_inc(v___y_844_);
v___x_849_ = lean_apply_5(v_continueLet_842_, v___x_848_, v___y_844_, v___y_845_, v___y_846_, lean_box(0));
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9___boxed(lean_object* v_continueLet_850_, lean_object* v_var_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_IR_ToIR_lowerLet___lam__9(v_continueLet_850_, v_var_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1(lean_object* v_args_857_, lean_object* v_continueLet_858_, lean_object* v_id_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
size_t v_sz_864_; size_t v___x_865_; lean_object* v___x_866_; 
v_sz_864_ = lean_array_size(v_args_857_);
v___x_865_ = ((size_t)0ULL);
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_864_, v___x_865_, v_args_857_, v___y_860_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_866_, 1);
v___x_868_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_868_, 0, v_id_859_);
lean_ctor_set(v___x_868_, 1, v_a_867_);
lean_inc(v___y_862_);
lean_inc_ref(v___y_861_);
lean_inc(v___y_860_);
v___x_869_ = lean_apply_5(v_continueLet_858_, v___x_868_, v___y_860_, v___y_861_, v___y_862_, lean_box(0));
return v___x_869_;
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec(v_id_859_);
lean_dec_ref(v_continueLet_858_);
v_a_870_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_866_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_866_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1___boxed(lean_object* v_args_878_, lean_object* v_continueLet_879_, lean_object* v_id_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_IR_ToIR_lowerLet___lam__1(v_args_878_, v_continueLet_879_, v_id_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0(lean_object* v_fvarId_886_, lean_object* v_k_887_, lean_object* v_type_888_, lean_object* v_e_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_886_, v___y_890_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_896_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref_known(v___x_894_, 1);
v___x_896_ = l_Lean_IR_ToIR_lowerCode(v_k_887_, v___y_890_, v___y_891_, v___y_892_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_905_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_905_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_901_, 0, v_a_895_);
lean_ctor_set(v___x_901_, 1, v_type_888_);
lean_ctor_set(v___x_901_, 2, v_e_889_);
lean_ctor_set(v___x_901_, 3, v_a_897_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_901_);
v___x_903_ = v___x_899_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
else
{
lean_dec(v_a_895_);
lean_dec_ref(v_e_889_);
lean_dec(v_type_888_);
return v___x_896_;
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
lean_dec_ref(v_e_889_);
lean_dec(v_type_888_);
lean_dec_ref(v_k_887_);
v_a_906_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_894_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_894_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object* v_fvarId_914_, lean_object* v_k_915_, lean_object* v_type_916_, lean_object* v_e_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_914_, v_k_915_, v_type_916_, v_e_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(lean_object* v_decl_923_, lean_object* v_k_924_, lean_object* v_fvarId_925_, lean_object* v_f_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_925_, v_a_927_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 1);
if (lean_obj_tag(v_a_932_) == 0)
{
lean_object* v_id_933_; lean_object* v___x_934_; 
lean_dec_ref(v_k_924_);
lean_dec_ref(v_decl_923_);
v_id_933_ = lean_ctor_get(v_a_932_, 0);
lean_inc(v_id_933_);
lean_dec_ref_known(v_a_932_, 1);
lean_inc(v_a_929_);
lean_inc_ref(v_a_928_);
lean_inc(v_a_927_);
v___x_934_ = lean_apply_5(v_f_926_, v_id_933_, v_a_927_, v_a_928_, v_a_929_, lean_box(0));
return v___x_934_;
}
else
{
lean_object* v___x_935_; 
lean_dec_ref(v_f_926_);
v___x_935_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_923_, v_k_924_, v_a_927_, v_a_928_, v_a_929_);
return v___x_935_;
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec_ref(v_f_926_);
lean_dec_ref(v_k_924_);
lean_dec_ref(v_decl_923_);
v_a_936_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_931_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_931_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object* v_decl_944_, lean_object* v_k_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_fvarId_950_; lean_object* v_type_951_; lean_object* v_value_952_; lean_object* v_type_953_; lean_object* v_continueLet_954_; 
v_fvarId_950_ = lean_ctor_get(v_decl_944_, 0);
v_type_951_ = lean_ctor_get(v_decl_944_, 2);
v_value_952_ = lean_ctor_get(v_decl_944_, 3);
lean_inc(v_value_952_);
v_type_953_ = l_Lean_IR_toIRType(v_type_951_);
lean_inc(v_type_953_);
lean_inc_ref(v_k_945_);
lean_inc(v_fvarId_950_);
v_continueLet_954_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 8, 3);
lean_closure_set(v_continueLet_954_, 0, v_fvarId_950_);
lean_closure_set(v_continueLet_954_, 1, v_k_945_);
lean_closure_set(v_continueLet_954_, 2, v_type_953_);
switch(lean_obj_tag(v_value_952_))
{
case 0:
{
lean_object* v_value_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_965_; 
lean_inc(v_fvarId_950_);
lean_dec_ref(v_continueLet_954_);
lean_dec_ref(v_decl_944_);
v_value_955_ = lean_ctor_get(v_value_952_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v_value_952_);
if (v_isSharedCheck_965_ == 0)
{
v___x_957_ = v_value_952_;
v_isShared_958_ = v_isSharedCheck_965_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_value_955_);
lean_dec(v_value_952_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_965_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v_fst_960_; lean_object* v___x_962_; 
v___x_959_ = l_Lean_IR_ToIR_lowerLitValue(v_value_955_);
v_fst_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_fst_960_);
lean_dec_ref(v___x_959_);
if (v_isShared_958_ == 0)
{
lean_ctor_set_tag(v___x_957_, 11);
lean_ctor_set(v___x_957_, 0, v_fst_960_);
v___x_962_ = v___x_957_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_fst_960_);
v___x_962_ = v_reuseFailAlloc_964_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_950_, v_k_945_, v_type_953_, v___x_962_, v_a_946_, v_a_947_, v_a_948_);
return v___x_963_;
}
}
}
case 1:
{
lean_object* v___x_966_; 
lean_dec_ref(v_continueLet_954_);
lean_dec(v_type_953_);
v___x_966_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_944_, v_k_945_, v_a_946_, v_a_947_, v_a_948_);
return v___x_966_;
}
case 4:
{
lean_object* v_fvarId_967_; lean_object* v_args_968_; lean_object* v___f_969_; lean_object* v___x_970_; 
lean_dec(v_type_953_);
v_fvarId_967_ = lean_ctor_get(v_value_952_, 0);
lean_inc(v_fvarId_967_);
v_args_968_ = lean_ctor_get(v_value_952_, 1);
lean_inc_ref(v_args_968_);
lean_dec_ref_known(v_value_952_, 2);
v___f_969_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__1___boxed), 7, 2);
lean_closure_set(v___f_969_, 0, v_args_968_);
lean_closure_set(v___f_969_, 1, v_continueLet_954_);
v___x_970_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_944_, v_k_945_, v_fvarId_967_, v___f_969_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_fvarId_967_);
return v___x_970_;
}
case 5:
{
lean_object* v_i_971_; lean_object* v_args_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_1004_; 
lean_inc(v_fvarId_950_);
lean_dec_ref(v_continueLet_954_);
lean_dec_ref(v_decl_944_);
v_i_971_ = lean_ctor_get(v_value_952_, 0);
v_args_972_ = lean_ctor_get(v_value_952_, 1);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_value_952_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_974_ = v_value_952_;
v_isShared_975_ = v_isSharedCheck_1004_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_args_972_);
lean_inc(v_i_971_);
lean_dec(v_value_952_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_1004_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
size_t v_sz_976_; size_t v___x_977_; lean_object* v___x_978_; 
v_sz_976_ = lean_array_size(v_args_972_);
v___x_977_ = ((size_t)0ULL);
v___x_978_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_976_, v___x_977_, v_args_972_, v_a_946_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v_name_980_; lean_object* v_cidx_981_; lean_object* v_size_982_; lean_object* v_usize_983_; lean_object* v_ssize_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_995_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
v_name_980_ = lean_ctor_get(v_i_971_, 0);
v_cidx_981_ = lean_ctor_get(v_i_971_, 1);
v_size_982_ = lean_ctor_get(v_i_971_, 2);
v_usize_983_ = lean_ctor_get(v_i_971_, 3);
v_ssize_984_ = lean_ctor_get(v_i_971_, 4);
v_isSharedCheck_995_ = !lean_is_exclusive(v_i_971_);
if (v_isSharedCheck_995_ == 0)
{
v___x_986_ = v_i_971_;
v_isShared_987_ = v_isSharedCheck_995_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_ssize_984_);
lean_inc(v_usize_983_);
lean_inc(v_size_982_);
lean_inc(v_cidx_981_);
lean_inc(v_name_980_);
lean_dec(v_i_971_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_995_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_name_980_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_cidx_981_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_size_982_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v_usize_983_);
lean_ctor_set(v_reuseFailAlloc_994_, 4, v_ssize_984_);
v___x_989_ = v_reuseFailAlloc_994_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_991_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set_tag(v___x_974_, 0);
lean_ctor_set(v___x_974_, 1, v_a_979_);
lean_ctor_set(v___x_974_, 0, v___x_989_);
v___x_991_ = v___x_974_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_a_979_);
v___x_991_ = v_reuseFailAlloc_993_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_950_, v_k_945_, v_type_953_, v___x_991_, v_a_946_, v_a_947_, v_a_948_);
return v___x_992_;
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_del_object(v___x_974_);
lean_dec_ref(v_i_971_);
lean_dec(v_type_953_);
lean_dec(v_fvarId_950_);
lean_dec_ref(v_k_945_);
v_a_996_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_978_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_978_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
case 6:
{
lean_object* v_i_1005_; lean_object* v_var_1006_; lean_object* v___f_1007_; lean_object* v___x_1008_; 
lean_dec(v_type_953_);
v_i_1005_ = lean_ctor_get(v_value_952_, 0);
lean_inc(v_i_1005_);
v_var_1006_ = lean_ctor_get(v_value_952_, 1);
lean_inc(v_var_1006_);
lean_dec_ref_known(v_value_952_, 2);
v___f_1007_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__2___boxed), 7, 2);
lean_closure_set(v___f_1007_, 0, v_i_1005_);
lean_closure_set(v___f_1007_, 1, v_continueLet_954_);
v___x_1008_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_944_, v_k_945_, v_var_1006_, v___f_1007_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_var_1006_);
return v___x_1008_;
}
case 7:
{
lean_object* v_i_1009_; lean_object* v_var_1010_; lean_object* v___f_1011_; lean_object* v___x_1012_; 
lean_dec(v_type_953_);
v_i_1009_ = lean_ctor_get(v_value_952_, 0);
lean_inc(v_i_1009_);
v_var_1010_ = lean_ctor_get(v_value_952_, 1);
lean_inc(v_var_1010_);
lean_dec_ref_known(v_value_952_, 2);
v___f_1011_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__3___boxed), 7, 2);
lean_closure_set(v___f_1011_, 0, v_i_1009_);
lean_closure_set(v___f_1011_, 1, v_continueLet_954_);
v___x_1012_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_944_, v_k_945_, v_var_1010_, v___f_1011_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_var_1010_);
return v___x_1012_;
}
case 8:
{
lean_object* v_n_1013_; lean_object* v_offset_1014_; lean_object* v_var_1015_; lean_object* v___f_1016_; lean_object* v___x_1017_; 
lean_dec(v_type_953_);
v_n_1013_ = lean_ctor_get(v_value_952_, 0);
lean_inc(v_n_1013_);
v_offset_1014_ = lean_ctor_get(v_value_952_, 1);
lean_inc(v_offset_1014_);
v_var_1015_ = lean_ctor_get(v_value_952_, 2);
lean_inc(v_var_1015_);
lean_dec_ref_known(v_value_952_, 3);
v___f_1016_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__4___boxed), 8, 3);
lean_closure_set(v___f_1016_, 0, v_n_1013_);
lean_closure_set(v___f_1016_, 1, v_offset_1014_);
lean_closure_set(v___f_1016_, 2, v_continueLet_954_);
v___x_1017_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_944_, v_k_945_, v_var_1015_, v___f_1016_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_var_1015_);
return v___x_1017_;
}
case 9:
{
lean_object* v_fn_1018_; lean_object* v_args_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1039_; 
lean_inc(v_fvarId_950_);
lean_dec_ref(v_continueLet_954_);
lean_dec_ref(v_decl_944_);
v_fn_1018_ = lean_ctor_get(v_value_952_, 0);
v_args_1019_ = lean_ctor_get(v_value_952_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_value_952_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1021_ = v_value_952_;
v_isShared_1022_ = v_isSharedCheck_1039_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_args_1019_);
lean_inc(v_fn_1018_);
lean_dec(v_value_952_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1039_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
size_t v_sz_1023_; size_t v___x_1024_; lean_object* v___x_1025_; 
v_sz_1023_ = lean_array_size(v_args_1019_);
v___x_1024_ = ((size_t)0ULL);
v___x_1025_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1023_, v___x_1024_, v_args_1019_, v_a_946_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
if (v_isShared_1022_ == 0)
{
lean_ctor_set_tag(v___x_1021_, 6);
lean_ctor_set(v___x_1021_, 1, v_a_1026_);
v___x_1028_ = v___x_1021_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_fn_1018_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_a_1026_);
v___x_1028_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_950_, v_k_945_, v_type_953_, v___x_1028_, v_a_946_, v_a_947_, v_a_948_);
return v___x_1029_;
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_del_object(v___x_1021_);
lean_dec(v_fn_1018_);
lean_dec(v_type_953_);
lean_dec(v_fvarId_950_);
lean_dec_ref(v_k_945_);
v_a_1031_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1025_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1025_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
case 10:
{
lean_object* v_fn_1040_; lean_object* v_args_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1061_; 
lean_inc(v_fvarId_950_);
lean_dec_ref(v_continueLet_954_);
lean_dec_ref(v_decl_944_);
v_fn_1040_ = lean_ctor_get(v_value_952_, 0);
v_args_1041_ = lean_ctor_get(v_value_952_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_value_952_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1043_ = v_value_952_;
v_isShared_1044_ = v_isSharedCheck_1061_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_args_1041_);
lean_inc(v_fn_1040_);
lean_dec(v_value_952_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1061_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
size_t v_sz_1045_; size_t v___x_1046_; lean_object* v___x_1047_; 
v_sz_1045_ = lean_array_size(v_args_1041_);
v___x_1046_ = ((size_t)0ULL);
v___x_1047_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1045_, v___x_1046_, v_args_1041_, v_a_946_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1050_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1047_, 1);
if (v_isShared_1044_ == 0)
{
lean_ctor_set_tag(v___x_1043_, 7);
lean_ctor_set(v___x_1043_, 1, v_a_1048_);
v___x_1050_ = v___x_1043_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_fn_1040_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_a_1048_);
v___x_1050_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_950_, v_k_945_, v_type_953_, v___x_1050_, v_a_946_, v_a_947_, v_a_948_);
return v___x_1051_;
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_del_object(v___x_1043_);
lean_dec(v_fn_1040_);
lean_dec(v_type_953_);
lean_dec(v_fvarId_950_);
lean_dec_ref(v_k_945_);
v_a_1053_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1047_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1047_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
case 11:
{
lean_object* v_n_1062_; lean_object* v_var_1063_; lean_object* v___f_1064_; lean_object* v___x_1065_; 
lean_dec(v_type_953_);
v_n_1062_ = lean_ctor_get(v_value_952_, 0);
lean_inc(v_n_1062_);
v_var_1063_ = lean_ctor_get(v_value_952_, 1);
lean_inc(v_var_1063_);
lean_dec_ref_known(v_value_952_, 2);
v___f_1064_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__5___boxed), 7, 2);
lean_closure_set(v___f_1064_, 0, v_n_1062_);
lean_closure_set(v___f_1064_, 1, v_continueLet_954_);
v___x_1065_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_944_, v_k_945_, v_var_1063_, v___f_1064_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_var_1063_);
return v___x_1065_;
}
case 12:
{
lean_object* v_var_1066_; lean_object* v_i_1067_; uint8_t v_updateHeader_1068_; lean_object* v_args_1069_; lean_object* v___x_1070_; lean_object* v___f_1071_; lean_object* v___x_1072_; 
lean_dec(v_type_953_);
v_var_1066_ = lean_ctor_get(v_value_952_, 0);
lean_inc(v_var_1066_);
v_i_1067_ = lean_ctor_get(v_value_952_, 1);
lean_inc_ref(v_i_1067_);
v_updateHeader_1068_ = lean_ctor_get_uint8(v_value_952_, sizeof(void*)*3);
v_args_1069_ = lean_ctor_get(v_value_952_, 2);
lean_inc_ref(v_args_1069_);
lean_dec_ref_known(v_value_952_, 3);
v___x_1070_ = lean_box(v_updateHeader_1068_);
v___f_1071_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 9, 4);
lean_closure_set(v___f_1071_, 0, v_args_1069_);
lean_closure_set(v___f_1071_, 1, v_i_1067_);
lean_closure_set(v___f_1071_, 2, v___x_1070_);
lean_closure_set(v___f_1071_, 3, v_continueLet_954_);
v___x_1072_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_944_, v_k_945_, v_var_1066_, v___f_1071_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_var_1066_);
return v___x_1072_;
}
case 13:
{
lean_object* v_ty_1073_; lean_object* v_fvarId_1074_; lean_object* v___f_1075_; lean_object* v___x_1076_; 
lean_dec(v_type_953_);
v_ty_1073_ = lean_ctor_get(v_value_952_, 0);
lean_inc_ref(v_ty_1073_);
v_fvarId_1074_ = lean_ctor_get(v_value_952_, 1);
lean_inc(v_fvarId_1074_);
lean_dec_ref_known(v_value_952_, 2);
v___f_1075_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__7___boxed), 7, 2);
lean_closure_set(v___f_1075_, 0, v_ty_1073_);
lean_closure_set(v___f_1075_, 1, v_continueLet_954_);
v___x_1076_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_944_, v_k_945_, v_fvarId_1074_, v___f_1075_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_fvarId_1074_);
return v___x_1076_;
}
case 14:
{
lean_object* v_fvarId_1077_; lean_object* v___f_1078_; lean_object* v___x_1079_; 
lean_dec(v_type_953_);
v_fvarId_1077_ = lean_ctor_get(v_value_952_, 0);
lean_inc(v_fvarId_1077_);
lean_dec_ref_known(v_value_952_, 1);
v___f_1078_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__8___boxed), 6, 1);
lean_closure_set(v___f_1078_, 0, v_continueLet_954_);
v___x_1079_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_944_, v_k_945_, v_fvarId_1077_, v___f_1078_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_fvarId_1077_);
return v___x_1079_;
}
default: 
{
lean_object* v_fvarId_1080_; lean_object* v___f_1081_; lean_object* v___x_1082_; 
lean_dec(v_type_953_);
v_fvarId_1080_ = lean_ctor_get(v_value_952_, 0);
lean_inc(v_fvarId_1080_);
lean_dec_ref_known(v_value_952_, 1);
v___f_1081_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__9___boxed), 6, 1);
lean_closure_set(v___f_1081_, 0, v_continueLet_954_);
v___x_1082_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_944_, v_k_945_, v_fvarId_1080_, v___f_1081_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_fvarId_1080_);
return v___x_1082_;
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__3(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1086_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__2));
v___x_1087_ = lean_unsigned_to_nat(15u);
v___x_1088_ = lean_unsigned_to_nat(128u);
v___x_1089_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1090_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1091_ = l_mkPanicMessageWithDecl(v___x_1090_, v___x_1089_, v___x_1088_, v___x_1087_, v___x_1086_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
if (lean_obj_tag(v_a_1092_) == 1)
{
lean_object* v_info_1097_; lean_object* v_code_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1134_; 
v_info_1097_ = lean_ctor_get(v_a_1092_, 0);
v_code_1098_ = lean_ctor_get(v_a_1092_, 1);
v_isSharedCheck_1134_ = !lean_is_exclusive(v_a_1092_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1100_ = v_a_1092_;
v_isShared_1101_ = v_isSharedCheck_1134_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_code_1098_);
lean_inc(v_info_1097_);
lean_dec(v_a_1092_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1134_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Lean_IR_ToIR_lowerCode(v_code_1098_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1125_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1105_ = v___x_1102_;
v_isShared_1106_ = v_isSharedCheck_1125_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1102_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1125_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v_name_1107_; lean_object* v_cidx_1108_; lean_object* v_size_1109_; lean_object* v_usize_1110_; lean_object* v_ssize_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1124_; 
v_name_1107_ = lean_ctor_get(v_info_1097_, 0);
v_cidx_1108_ = lean_ctor_get(v_info_1097_, 1);
v_size_1109_ = lean_ctor_get(v_info_1097_, 2);
v_usize_1110_ = lean_ctor_get(v_info_1097_, 3);
v_ssize_1111_ = lean_ctor_get(v_info_1097_, 4);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_info_1097_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1113_ = v_info_1097_;
v_isShared_1114_ = v_isSharedCheck_1124_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_ssize_1111_);
lean_inc(v_usize_1110_);
lean_inc(v_size_1109_);
lean_inc(v_cidx_1108_);
lean_inc(v_name_1107_);
lean_dec(v_info_1097_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1124_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_name_1107_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_cidx_1108_);
lean_ctor_set(v_reuseFailAlloc_1123_, 2, v_size_1109_);
lean_ctor_set(v_reuseFailAlloc_1123_, 3, v_usize_1110_);
lean_ctor_set(v_reuseFailAlloc_1123_, 4, v_ssize_1111_);
v___x_1116_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1118_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set_tag(v___x_1100_, 0);
lean_ctor_set(v___x_1100_, 1, v_a_1103_);
lean_ctor_set(v___x_1100_, 0, v___x_1116_);
v___x_1118_ = v___x_1100_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_a_1103_);
v___x_1118_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1120_; 
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1118_);
v___x_1120_ = v___x_1105_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_del_object(v___x_1100_);
lean_dec_ref(v_info_1097_);
v_a_1126_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1102_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1102_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
else
{
lean_object* v_code_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1159_; 
v_code_1135_ = lean_ctor_get(v_a_1092_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_a_1092_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1137_ = v_a_1092_;
v_isShared_1138_ = v_isSharedCheck_1159_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_code_1135_);
lean_dec(v_a_1092_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1159_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_IR_ToIR_lowerCode(v_code_1135_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1150_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1150_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1150_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set_tag(v___x_1137_, 1);
lean_ctor_set(v___x_1137_, 0, v_a_1140_);
v___x_1145_ = v___x_1137_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1145_);
v___x_1147_ = v___x_1142_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_del_object(v___x_1137_);
v_a_1151_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1139_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1139_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(size_t v_sz_1160_, size_t v_i_1161_, lean_object* v_bs_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
uint8_t v___x_1167_; 
v___x_1167_ = lean_usize_dec_lt(v_i_1161_, v_sz_1160_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v_bs_1162_);
return v___x_1168_;
}
else
{
lean_object* v_v_1169_; lean_object* v___x_1170_; 
v_v_1169_ = lean_array_uget_borrowed(v_bs_1162_, v_i_1161_);
lean_inc(v_v_1169_);
v___x_1170_ = l_Lean_IR_ToIR_lowerAlt(v_v_1169_, v___y_1163_, v___y_1164_, v___y_1165_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1172_; lean_object* v_bs_x27_1173_; size_t v___x_1174_; size_t v___x_1175_; lean_object* v___x_1176_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1170_, 1);
v___x_1172_ = lean_unsigned_to_nat(0u);
v_bs_x27_1173_ = lean_array_uset(v_bs_1162_, v_i_1161_, v___x_1172_);
v___x_1174_ = ((size_t)1ULL);
v___x_1175_ = lean_usize_add(v_i_1161_, v___x_1174_);
v___x_1176_ = lean_array_uset(v_bs_x27_1173_, v_i_1161_, v_a_1171_);
v_i_1161_ = v___x_1175_;
v_bs_1162_ = v___x_1176_;
goto _start;
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v_bs_1162_);
v_a_1178_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1170_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1170_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__5(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1187_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1188_ = lean_unsigned_to_nat(53u);
v___x_1189_ = lean_unsigned_to_nat(95u);
v___x_1190_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1191_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1192_ = l_mkPanicMessageWithDecl(v___x_1191_, v___x_1190_, v___x_1189_, v___x_1188_, v___x_1187_);
return v___x_1192_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__6(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1193_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1194_ = lean_unsigned_to_nat(44u);
v___x_1195_ = lean_unsigned_to_nat(106u);
v___x_1196_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1197_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1198_ = l_mkPanicMessageWithDecl(v___x_1197_, v___x_1196_, v___x_1195_, v___x_1194_, v___x_1193_);
return v___x_1198_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__7(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1199_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1200_ = lean_unsigned_to_nat(44u);
v___x_1201_ = lean_unsigned_to_nat(114u);
v___x_1202_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1203_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1204_ = l_mkPanicMessageWithDecl(v___x_1203_, v___x_1202_, v___x_1201_, v___x_1200_, v___x_1199_);
return v___x_1204_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__8(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1205_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1206_ = lean_unsigned_to_nat(34u);
v___x_1207_ = lean_unsigned_to_nat(113u);
v___x_1208_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1209_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1210_ = l_mkPanicMessageWithDecl(v___x_1209_, v___x_1208_, v___x_1207_, v___x_1206_, v___x_1205_);
return v___x_1210_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__9(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1211_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1212_ = lean_unsigned_to_nat(44u);
v___x_1213_ = lean_unsigned_to_nat(110u);
v___x_1214_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1215_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1216_ = l_mkPanicMessageWithDecl(v___x_1215_, v___x_1214_, v___x_1213_, v___x_1212_, v___x_1211_);
return v___x_1216_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__10(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1217_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1218_ = lean_unsigned_to_nat(34u);
v___x_1219_ = lean_unsigned_to_nat(109u);
v___x_1220_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1221_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1222_ = l_mkPanicMessageWithDecl(v___x_1221_, v___x_1220_, v___x_1219_, v___x_1218_, v___x_1217_);
return v___x_1222_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__11(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1223_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1224_ = lean_unsigned_to_nat(41u);
v___x_1225_ = lean_unsigned_to_nat(117u);
v___x_1226_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1227_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1228_ = l_mkPanicMessageWithDecl(v___x_1227_, v___x_1226_, v___x_1225_, v___x_1224_, v___x_1223_);
return v___x_1228_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__12(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1229_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1230_ = lean_unsigned_to_nat(41u);
v___x_1231_ = lean_unsigned_to_nat(120u);
v___x_1232_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1233_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1234_ = l_mkPanicMessageWithDecl(v___x_1233_, v___x_1232_, v___x_1231_, v___x_1230_, v___x_1229_);
return v___x_1234_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__13(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1235_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1236_ = lean_unsigned_to_nat(41u);
v___x_1237_ = lean_unsigned_to_nat(123u);
v___x_1238_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1239_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1240_ = l_mkPanicMessageWithDecl(v___x_1239_, v___x_1238_, v___x_1237_, v___x_1236_, v___x_1235_);
return v___x_1240_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__14(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1241_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1242_ = lean_unsigned_to_nat(41u);
v___x_1243_ = lean_unsigned_to_nat(126u);
v___x_1244_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1245_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1246_ = l_mkPanicMessageWithDecl(v___x_1245_, v___x_1244_, v___x_1243_, v___x_1242_, v___x_1241_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object* v_c_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
switch(lean_obj_tag(v_c_1247_))
{
case 0:
{
lean_object* v_decl_1252_; lean_object* v_k_1253_; lean_object* v___x_1254_; 
v_decl_1252_ = lean_ctor_get(v_c_1247_, 0);
lean_inc_ref(v_decl_1252_);
v_k_1253_ = lean_ctor_get(v_c_1247_, 1);
lean_inc_ref(v_k_1253_);
lean_dec_ref_known(v_c_1247_, 2);
v___x_1254_ = l_Lean_IR_ToIR_lowerLet(v_decl_1252_, v_k_1253_, v_a_1248_, v_a_1249_, v_a_1250_);
return v___x_1254_;
}
case 1:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_dec_ref_known(v_c_1247_, 2);
v___x_1255_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__3, &l_Lean_IR_ToIR_lowerCode___closed__3_once, _init_l_Lean_IR_ToIR_lowerCode___closed__3);
v___x_1256_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1255_, v_a_1248_, v_a_1249_, v_a_1250_);
return v___x_1256_;
}
case 2:
{
lean_object* v_decl_1257_; lean_object* v_k_1258_; lean_object* v_fvarId_1259_; lean_object* v_params_1260_; lean_object* v_value_1261_; lean_object* v___x_1262_; 
v_decl_1257_ = lean_ctor_get(v_c_1247_, 0);
lean_inc_ref(v_decl_1257_);
v_k_1258_ = lean_ctor_get(v_c_1247_, 1);
lean_inc_ref(v_k_1258_);
lean_dec_ref_known(v_c_1247_, 2);
v_fvarId_1259_ = lean_ctor_get(v_decl_1257_, 0);
lean_inc(v_fvarId_1259_);
v_params_1260_ = lean_ctor_get(v_decl_1257_, 2);
lean_inc_ref(v_params_1260_);
v_value_1261_ = lean_ctor_get(v_decl_1257_, 4);
lean_inc_ref(v_value_1261_);
lean_dec_ref(v_decl_1257_);
v___x_1262_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_1259_, v_a_1248_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; size_t v_sz_1264_; size_t v___x_1265_; lean_object* v___x_1266_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1262_, 1);
v_sz_1264_ = lean_array_size(v_params_1260_);
v___x_1265_ = ((size_t)0ULL);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1264_, v___x_1265_, v_params_1260_, v_a_1248_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v___x_1268_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1266_, 1);
v___x_1268_ = l_Lean_IR_ToIR_lowerCode(v_value_1261_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1270_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___x_1268_, 1);
v___x_1270_ = l_Lean_IR_ToIR_lowerCode(v_k_1258_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1279_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1279_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1279_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1275_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1275_, 0, v_a_1263_);
lean_ctor_set(v___x_1275_, 1, v_a_1267_);
lean_ctor_set(v___x_1275_, 2, v_a_1269_);
lean_ctor_set(v___x_1275_, 3, v_a_1271_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v___x_1275_);
v___x_1277_ = v___x_1273_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
else
{
lean_dec(v_a_1269_);
lean_dec(v_a_1267_);
lean_dec(v_a_1263_);
return v___x_1270_;
}
}
else
{
lean_dec(v_a_1267_);
lean_dec(v_a_1263_);
lean_dec_ref(v_k_1258_);
return v___x_1268_;
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec(v_a_1263_);
lean_dec_ref(v_value_1261_);
lean_dec_ref(v_k_1258_);
v_a_1280_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1266_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1266_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_value_1261_);
lean_dec_ref(v_params_1260_);
lean_dec_ref(v_k_1258_);
v_a_1288_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1262_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1262_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_1296_; lean_object* v_args_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1333_; 
v_fvarId_1296_ = lean_ctor_get(v_c_1247_, 0);
v_args_1297_ = lean_ctor_get(v_c_1247_, 1);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_c_1247_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1299_ = v_c_1247_;
v_isShared_1300_ = v_isSharedCheck_1333_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_args_1297_);
lean_inc(v_fvarId_1296_);
lean_dec(v_c_1247_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1333_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_1296_, v_a_1248_);
lean_dec(v_fvarId_1296_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; size_t v_sz_1303_; size_t v___x_1304_; lean_object* v___x_1305_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1301_, 1);
v_sz_1303_ = lean_array_size(v_args_1297_);
v___x_1304_ = ((size_t)0ULL);
v___x_1305_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1303_, v___x_1304_, v_args_1297_, v_a_1248_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1316_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1316_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1316_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set_tag(v___x_1299_, 11);
lean_ctor_set(v___x_1299_, 1, v_a_1306_);
lean_ctor_set(v___x_1299_, 0, v_a_1302_);
v___x_1311_ = v___x_1299_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1302_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
lean_object* v___x_1313_; 
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1311_);
v___x_1313_ = v___x_1308_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec(v_a_1302_);
lean_del_object(v___x_1299_);
v_a_1317_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1305_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1305_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_del_object(v___x_1299_);
lean_dec_ref(v_args_1297_);
v_a_1325_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1301_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1301_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
case 4:
{
lean_object* v_cases_1334_; lean_object* v_typeName_1335_; lean_object* v_discr_1336_; lean_object* v_alts_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1377_; 
v_cases_1334_ = lean_ctor_get(v_c_1247_, 0);
lean_inc_ref(v_cases_1334_);
lean_dec_ref_known(v_c_1247_, 1);
v_typeName_1335_ = lean_ctor_get(v_cases_1334_, 0);
v_discr_1336_ = lean_ctor_get(v_cases_1334_, 2);
v_alts_1337_ = lean_ctor_get(v_cases_1334_, 3);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_cases_1334_);
if (v_isSharedCheck_1377_ == 0)
{
lean_object* v_unused_1378_; 
v_unused_1378_ = lean_ctor_get(v_cases_1334_, 1);
lean_dec(v_unused_1378_);
v___x_1339_ = v_cases_1334_;
v_isShared_1340_ = v_isSharedCheck_1377_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_alts_1337_);
lean_inc(v_discr_1336_);
lean_inc(v_typeName_1335_);
lean_dec(v_cases_1334_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1377_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_discr_1336_, v_a_1248_);
lean_dec(v_discr_1336_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref_known(v___x_1341_, 1);
if (lean_obj_tag(v_a_1342_) == 0)
{
lean_object* v_id_1343_; size_t v_sz_1344_; size_t v___x_1345_; lean_object* v___x_1346_; 
v_id_1343_ = lean_ctor_get(v_a_1342_, 0);
lean_inc(v_id_1343_);
lean_dec_ref_known(v_a_1342_, 1);
v_sz_1344_ = lean_array_size(v_alts_1337_);
v___x_1345_ = ((size_t)0ULL);
v___x_1346_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_1344_, v___x_1345_, v_alts_1337_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1358_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1358_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1358_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1351_ = l_Lean_IR_nameToIRType(v_typeName_1335_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set_tag(v___x_1339_, 9);
lean_ctor_set(v___x_1339_, 3, v_a_1347_);
lean_ctor_set(v___x_1339_, 2, v___x_1351_);
lean_ctor_set(v___x_1339_, 1, v_id_1343_);
v___x_1353_ = v___x_1339_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_typeName_1335_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_id_1343_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v_a_1347_);
v___x_1353_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1355_; 
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1353_);
v___x_1355_ = v___x_1349_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec(v_id_1343_);
lean_del_object(v___x_1339_);
lean_dec(v_typeName_1335_);
v_a_1359_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1346_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1346_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_dec(v_a_1342_);
lean_del_object(v___x_1339_);
lean_dec_ref(v_alts_1337_);
lean_dec(v_typeName_1335_);
v___x_1367_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__5, &l_Lean_IR_ToIR_lowerCode___closed__5_once, _init_l_Lean_IR_ToIR_lowerCode___closed__5);
v___x_1368_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1367_, v_a_1248_, v_a_1249_, v_a_1250_);
return v___x_1368_;
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_del_object(v___x_1339_);
lean_dec_ref(v_alts_1337_);
lean_dec(v_typeName_1335_);
v_a_1369_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1341_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1341_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1403_; 
v_fvarId_1379_ = lean_ctor_get(v_c_1247_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_c_1247_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1381_ = v_c_1247_;
v_isShared_1382_ = v_isSharedCheck_1403_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_fvarId_1379_);
lean_dec(v_c_1247_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1403_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1379_, v_a_1248_);
lean_dec(v_fvarId_1379_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1394_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1386_ = v___x_1383_;
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set_tag(v___x_1381_, 10);
lean_ctor_set(v___x_1381_, 0, v_a_1384_);
v___x_1389_ = v___x_1381_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1391_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1389_);
v___x_1391_ = v___x_1386_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_del_object(v___x_1381_);
v_a_1395_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1383_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1383_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
case 6:
{
lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1411_; 
v_isSharedCheck_1411_ = !lean_is_exclusive(v_c_1247_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v_c_1247_, 0);
lean_dec(v_unused_1412_);
v___x_1405_ = v_c_1247_;
v_isShared_1406_ = v_isSharedCheck_1411_;
goto v_resetjp_1404_;
}
else
{
lean_dec(v_c_1247_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1411_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1407_ = lean_box(12);
if (v_isShared_1406_ == 0)
{
lean_ctor_set_tag(v___x_1405_, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1407_);
v___x_1409_ = v___x_1405_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
case 7:
{
lean_object* v_fvarId_1413_; lean_object* v_i_1414_; lean_object* v_y_1415_; lean_object* v_k_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1455_; 
v_fvarId_1413_ = lean_ctor_get(v_c_1247_, 0);
v_i_1414_ = lean_ctor_get(v_c_1247_, 1);
v_y_1415_ = lean_ctor_get(v_c_1247_, 2);
v_k_1416_ = lean_ctor_get(v_c_1247_, 3);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_c_1247_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1418_ = v_c_1247_;
v_isShared_1419_ = v_isSharedCheck_1455_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_k_1416_);
lean_inc(v_y_1415_);
lean_inc(v_i_1414_);
lean_inc(v_fvarId_1413_);
lean_dec(v_c_1247_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1455_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_IR_ToIR_lowerArg___redArg(v_y_1415_, v_a_1248_);
lean_dec(v_y_1415_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1422_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1413_, v_a_1248_);
lean_dec(v_fvarId_1413_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
if (lean_obj_tag(v_a_1423_) == 0)
{
lean_object* v_id_1424_; lean_object* v___x_1425_; 
v_id_1424_ = lean_ctor_get(v_a_1423_, 0);
lean_inc(v_id_1424_);
lean_dec_ref_known(v_a_1423_, 1);
v___x_1425_ = l_Lean_IR_ToIR_lowerCode(v_k_1416_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1436_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1436_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1436_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set_tag(v___x_1418_, 2);
lean_ctor_set(v___x_1418_, 3, v_a_1426_);
lean_ctor_set(v___x_1418_, 2, v_a_1421_);
lean_ctor_set(v___x_1418_, 0, v_id_1424_);
v___x_1431_ = v___x_1418_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_id_1424_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_i_1414_);
lean_ctor_set(v_reuseFailAlloc_1435_, 2, v_a_1421_);
lean_ctor_set(v_reuseFailAlloc_1435_, 3, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1433_; 
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1431_);
v___x_1433_ = v___x_1428_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
else
{
lean_dec(v_id_1424_);
lean_dec(v_a_1421_);
lean_del_object(v___x_1418_);
lean_dec(v_i_1414_);
return v___x_1425_;
}
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
lean_dec(v_a_1423_);
lean_dec(v_a_1421_);
lean_del_object(v___x_1418_);
lean_dec_ref(v_k_1416_);
lean_dec(v_i_1414_);
v___x_1437_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__6, &l_Lean_IR_ToIR_lowerCode___closed__6_once, _init_l_Lean_IR_ToIR_lowerCode___closed__6);
v___x_1438_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1437_, v_a_1248_, v_a_1249_, v_a_1250_);
return v___x_1438_;
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec(v_a_1421_);
lean_del_object(v___x_1418_);
lean_dec_ref(v_k_1416_);
lean_dec(v_i_1414_);
v_a_1439_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1422_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1422_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_del_object(v___x_1418_);
lean_dec_ref(v_k_1416_);
lean_dec(v_i_1414_);
lean_dec(v_fvarId_1413_);
v_a_1447_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1420_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1420_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
case 8:
{
lean_object* v_fvarId_1456_; lean_object* v_i_1457_; lean_object* v_y_1458_; lean_object* v_k_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1501_; 
v_fvarId_1456_ = lean_ctor_get(v_c_1247_, 0);
v_i_1457_ = lean_ctor_get(v_c_1247_, 1);
v_y_1458_ = lean_ctor_get(v_c_1247_, 2);
v_k_1459_ = lean_ctor_get(v_c_1247_, 3);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_c_1247_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1461_ = v_c_1247_;
v_isShared_1462_ = v_isSharedCheck_1501_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_k_1459_);
lean_inc(v_y_1458_);
lean_inc(v_i_1457_);
lean_inc(v_fvarId_1456_);
lean_dec(v_c_1247_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1501_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1458_, v_a_1248_);
lean_dec(v_y_1458_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 1);
if (lean_obj_tag(v_a_1464_) == 0)
{
lean_object* v_id_1465_; lean_object* v___x_1466_; 
v_id_1465_ = lean_ctor_get(v_a_1464_, 0);
lean_inc(v_id_1465_);
lean_dec_ref_known(v_a_1464_, 1);
v___x_1466_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1456_, v_a_1248_);
lean_dec(v_fvarId_1456_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
if (lean_obj_tag(v_a_1467_) == 0)
{
lean_object* v_id_1468_; lean_object* v___x_1469_; 
v_id_1468_ = lean_ctor_get(v_a_1467_, 0);
lean_inc(v_id_1468_);
lean_dec_ref_known(v_a_1467_, 1);
v___x_1469_ = l_Lean_IR_ToIR_lowerCode(v_k_1459_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1480_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1472_ = v___x_1469_;
v_isShared_1473_ = v_isSharedCheck_1480_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1480_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1462_ == 0)
{
lean_ctor_set_tag(v___x_1461_, 4);
lean_ctor_set(v___x_1461_, 3, v_a_1470_);
lean_ctor_set(v___x_1461_, 2, v_id_1465_);
lean_ctor_set(v___x_1461_, 0, v_id_1468_);
v___x_1475_ = v___x_1461_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_id_1468_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_i_1457_);
lean_ctor_set(v_reuseFailAlloc_1479_, 2, v_id_1465_);
lean_ctor_set(v_reuseFailAlloc_1479_, 3, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1477_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___x_1475_);
v___x_1477_ = v___x_1472_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_dec(v_id_1468_);
lean_dec(v_id_1465_);
lean_del_object(v___x_1461_);
lean_dec(v_i_1457_);
return v___x_1469_;
}
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_dec(v_a_1467_);
lean_dec(v_id_1465_);
lean_del_object(v___x_1461_);
lean_dec_ref(v_k_1459_);
lean_dec(v_i_1457_);
v___x_1481_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__7, &l_Lean_IR_ToIR_lowerCode___closed__7_once, _init_l_Lean_IR_ToIR_lowerCode___closed__7);
v___x_1482_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1481_, v_a_1248_, v_a_1249_, v_a_1250_);
return v___x_1482_;
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec(v_id_1465_);
lean_del_object(v___x_1461_);
lean_dec_ref(v_k_1459_);
lean_dec(v_i_1457_);
v_a_1483_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1466_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1466_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
else
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_dec(v_a_1464_);
lean_del_object(v___x_1461_);
lean_dec_ref(v_k_1459_);
lean_dec(v_i_1457_);
lean_dec(v_fvarId_1456_);
v___x_1491_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__8, &l_Lean_IR_ToIR_lowerCode___closed__8_once, _init_l_Lean_IR_ToIR_lowerCode___closed__8);
v___x_1492_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1491_, v_a_1248_, v_a_1249_, v_a_1250_);
return v___x_1492_;
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
lean_del_object(v___x_1461_);
lean_dec_ref(v_k_1459_);
lean_dec(v_i_1457_);
lean_dec(v_fvarId_1456_);
v_a_1493_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1463_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1463_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
}
case 9:
{
lean_object* v_fvarId_1502_; lean_object* v_i_1503_; lean_object* v_offset_1504_; lean_object* v_y_1505_; lean_object* v_ty_1506_; lean_object* v_k_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1550_; 
v_fvarId_1502_ = lean_ctor_get(v_c_1247_, 0);
v_i_1503_ = lean_ctor_get(v_c_1247_, 1);
v_offset_1504_ = lean_ctor_get(v_c_1247_, 2);
v_y_1505_ = lean_ctor_get(v_c_1247_, 3);
v_ty_1506_ = lean_ctor_get(v_c_1247_, 4);
v_k_1507_ = lean_ctor_get(v_c_1247_, 5);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_c_1247_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1509_ = v_c_1247_;
v_isShared_1510_ = v_isSharedCheck_1550_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_k_1507_);
lean_inc(v_ty_1506_);
lean_inc(v_y_1505_);
lean_inc(v_offset_1504_);
lean_inc(v_i_1503_);
lean_inc(v_fvarId_1502_);
lean_dec(v_c_1247_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1550_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1505_, v_a_1248_);
lean_dec(v_y_1505_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1511_, 1);
if (lean_obj_tag(v_a_1512_) == 0)
{
lean_object* v_id_1513_; lean_object* v___x_1514_; 
v_id_1513_ = lean_ctor_get(v_a_1512_, 0);
lean_inc(v_id_1513_);
lean_dec_ref_known(v_a_1512_, 1);
v___x_1514_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1502_, v_a_1248_);
lean_dec(v_fvarId_1502_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
if (lean_obj_tag(v_a_1515_) == 0)
{
lean_object* v_id_1516_; lean_object* v___x_1517_; 
v_id_1516_ = lean_ctor_get(v_a_1515_, 0);
lean_inc(v_id_1516_);
lean_dec_ref_known(v_a_1515_, 1);
v___x_1517_ = l_Lean_IR_ToIR_lowerCode(v_k_1507_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1529_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1520_ = v___x_1517_;
v_isShared_1521_ = v_isSharedCheck_1529_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1529_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1522_ = l_Lean_IR_toIRType(v_ty_1506_);
lean_dec_ref(v_ty_1506_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set_tag(v___x_1509_, 5);
lean_ctor_set(v___x_1509_, 5, v_a_1518_);
lean_ctor_set(v___x_1509_, 4, v___x_1522_);
lean_ctor_set(v___x_1509_, 3, v_id_1513_);
lean_ctor_set(v___x_1509_, 0, v_id_1516_);
v___x_1524_ = v___x_1509_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_id_1516_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_i_1503_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_offset_1504_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v_id_1513_);
lean_ctor_set(v_reuseFailAlloc_1528_, 4, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1528_, 5, v_a_1518_);
v___x_1524_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1526_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1524_);
v___x_1526_ = v___x_1520_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
else
{
lean_dec(v_id_1516_);
lean_dec(v_id_1513_);
lean_del_object(v___x_1509_);
lean_dec_ref(v_ty_1506_);
lean_dec(v_offset_1504_);
lean_dec(v_i_1503_);
return v___x_1517_;
}
}
else
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_dec(v_a_1515_);
lean_dec(v_id_1513_);
lean_del_object(v___x_1509_);
lean_dec_ref(v_k_1507_);
lean_dec_ref(v_ty_1506_);
lean_dec(v_offset_1504_);
lean_dec(v_i_1503_);
v___x_1530_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__9, &l_Lean_IR_ToIR_lowerCode___closed__9_once, _init_l_Lean_IR_ToIR_lowerCode___closed__9);
v___x_1531_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1530_, v_a_1248_, v_a_1249_, v_a_1250_);
return v___x_1531_;
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec(v_id_1513_);
lean_del_object(v___x_1509_);
lean_dec_ref(v_k_1507_);
lean_dec_ref(v_ty_1506_);
lean_dec(v_offset_1504_);
lean_dec(v_i_1503_);
v_a_1532_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1514_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1514_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_dec(v_a_1512_);
lean_del_object(v___x_1509_);
lean_dec_ref(v_k_1507_);
lean_dec_ref(v_ty_1506_);
lean_dec(v_offset_1504_);
lean_dec(v_i_1503_);
lean_dec(v_fvarId_1502_);
v___x_1540_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__10, &l_Lean_IR_ToIR_lowerCode___closed__10_once, _init_l_Lean_IR_ToIR_lowerCode___closed__10);
v___x_1541_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1540_, v_a_1248_, v_a_1249_, v_a_1250_);
return v___x_1541_;
}
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_del_object(v___x_1509_);
lean_dec_ref(v_k_1507_);
lean_dec_ref(v_ty_1506_);
lean_dec(v_offset_1504_);
lean_dec(v_i_1503_);
lean_dec(v_fvarId_1502_);
v_a_1542_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1511_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1511_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
}
case 10:
{
lean_object* v_fvarId_1551_; lean_object* v_cidx_1552_; lean_object* v_k_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1582_; 
v_fvarId_1551_ = lean_ctor_get(v_c_1247_, 0);
v_cidx_1552_ = lean_ctor_get(v_c_1247_, 1);
v_k_1553_ = lean_ctor_get(v_c_1247_, 2);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_c_1247_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1555_ = v_c_1247_;
v_isShared_1556_ = v_isSharedCheck_1582_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_k_1553_);
lean_inc(v_cidx_1552_);
lean_inc(v_fvarId_1551_);
lean_dec(v_c_1247_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1582_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1551_, v_a_1248_);
lean_dec(v_fvarId_1551_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1557_, 1);
if (lean_obj_tag(v_a_1558_) == 0)
{
lean_object* v_id_1559_; lean_object* v___x_1560_; 
v_id_1559_ = lean_ctor_get(v_a_1558_, 0);
lean_inc(v_id_1559_);
lean_dec_ref_known(v_a_1558_, 1);
v___x_1560_ = l_Lean_IR_ToIR_lowerCode(v_k_1553_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1571_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1563_ = v___x_1560_;
v_isShared_1564_ = v_isSharedCheck_1571_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1571_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1556_ == 0)
{
lean_ctor_set_tag(v___x_1555_, 3);
lean_ctor_set(v___x_1555_, 2, v_a_1561_);
lean_ctor_set(v___x_1555_, 0, v_id_1559_);
v___x_1566_ = v___x_1555_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_id_1559_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_cidx_1552_);
lean_ctor_set(v_reuseFailAlloc_1570_, 2, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1568_; 
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v___x_1566_);
v___x_1568_ = v___x_1563_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
else
{
lean_dec(v_id_1559_);
lean_del_object(v___x_1555_);
lean_dec(v_cidx_1552_);
return v___x_1560_;
}
}
else
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
lean_dec(v_a_1558_);
lean_del_object(v___x_1555_);
lean_dec_ref(v_k_1553_);
lean_dec(v_cidx_1552_);
v___x_1572_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__11, &l_Lean_IR_ToIR_lowerCode___closed__11_once, _init_l_Lean_IR_ToIR_lowerCode___closed__11);
v___x_1573_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1572_, v_a_1248_, v_a_1249_, v_a_1250_);
return v___x_1573_;
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_del_object(v___x_1555_);
lean_dec_ref(v_k_1553_);
lean_dec(v_cidx_1552_);
v_a_1574_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1557_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1557_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
case 11:
{
lean_object* v_fvarId_1583_; lean_object* v_n_1584_; uint8_t v_check_1585_; uint8_t v_persistent_1586_; lean_object* v_k_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1616_; 
v_fvarId_1583_ = lean_ctor_get(v_c_1247_, 0);
v_n_1584_ = lean_ctor_get(v_c_1247_, 1);
v_check_1585_ = lean_ctor_get_uint8(v_c_1247_, sizeof(void*)*3);
v_persistent_1586_ = lean_ctor_get_uint8(v_c_1247_, sizeof(void*)*3 + 1);
v_k_1587_ = lean_ctor_get(v_c_1247_, 2);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_c_1247_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1589_ = v_c_1247_;
v_isShared_1590_ = v_isSharedCheck_1616_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_k_1587_);
lean_inc(v_n_1584_);
lean_inc(v_fvarId_1583_);
lean_dec(v_c_1247_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1616_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1583_, v_a_1248_);
lean_dec(v_fvarId_1583_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1591_, 1);
if (lean_obj_tag(v_a_1592_) == 0)
{
lean_object* v_id_1593_; lean_object* v___x_1594_; 
v_id_1593_ = lean_ctor_get(v_a_1592_, 0);
lean_inc(v_id_1593_);
lean_dec_ref_known(v_a_1592_, 1);
v___x_1594_ = l_Lean_IR_ToIR_lowerCode(v_k_1587_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1605_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1597_ = v___x_1594_;
v_isShared_1598_ = v_isSharedCheck_1605_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1594_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1605_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1590_ == 0)
{
lean_ctor_set_tag(v___x_1589_, 6);
lean_ctor_set(v___x_1589_, 2, v_a_1595_);
lean_ctor_set(v___x_1589_, 0, v_id_1593_);
v___x_1600_ = v___x_1589_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_id_1593_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_n_1584_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_a_1595_);
lean_ctor_set_uint8(v_reuseFailAlloc_1604_, sizeof(void*)*3, v_check_1585_);
lean_ctor_set_uint8(v_reuseFailAlloc_1604_, sizeof(void*)*3 + 1, v_persistent_1586_);
v___x_1600_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1602_; 
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v___x_1600_);
v___x_1602_ = v___x_1597_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
else
{
lean_dec(v_id_1593_);
lean_del_object(v___x_1589_);
lean_dec(v_n_1584_);
return v___x_1594_;
}
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_dec(v_a_1592_);
lean_del_object(v___x_1589_);
lean_dec_ref(v_k_1587_);
lean_dec(v_n_1584_);
v___x_1606_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__12, &l_Lean_IR_ToIR_lowerCode___closed__12_once, _init_l_Lean_IR_ToIR_lowerCode___closed__12);
v___x_1607_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1606_, v_a_1248_, v_a_1249_, v_a_1250_);
return v___x_1607_;
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_del_object(v___x_1589_);
lean_dec_ref(v_k_1587_);
lean_dec(v_n_1584_);
v_a_1608_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1591_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1591_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
case 12:
{
lean_object* v_fvarId_1617_; lean_object* v_n_1618_; uint8_t v_check_1619_; uint8_t v_persistent_1620_; lean_object* v_k_1621_; lean_object* v___x_1622_; 
v_fvarId_1617_ = lean_ctor_get(v_c_1247_, 0);
lean_inc(v_fvarId_1617_);
v_n_1618_ = lean_ctor_get(v_c_1247_, 1);
lean_inc(v_n_1618_);
v_check_1619_ = lean_ctor_get_uint8(v_c_1247_, sizeof(void*)*4);
v_persistent_1620_ = lean_ctor_get_uint8(v_c_1247_, sizeof(void*)*4 + 1);
v_k_1621_ = lean_ctor_get(v_c_1247_, 3);
lean_inc_ref(v_k_1621_);
lean_dec_ref_known(v_c_1247_, 4);
v___x_1622_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1617_, v_a_1248_);
lean_dec(v_fvarId_1617_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v___x_1622_, 1);
if (lean_obj_tag(v_a_1623_) == 0)
{
lean_object* v_id_1624_; lean_object* v___x_1625_; 
v_id_1624_ = lean_ctor_get(v_a_1623_, 0);
lean_inc(v_id_1624_);
lean_dec_ref_known(v_a_1623_, 1);
v___x_1625_ = l_Lean_IR_ToIR_lowerCode(v_k_1621_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1634_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1634_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1634_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v___x_1632_; 
v___x_1630_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v___x_1630_, 0, v_id_1624_);
lean_ctor_set(v___x_1630_, 1, v_n_1618_);
lean_ctor_set(v___x_1630_, 2, v_a_1626_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3, v_check_1619_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 1, v_persistent_1620_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1630_);
v___x_1632_ = v___x_1628_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
else
{
lean_dec(v_id_1624_);
lean_dec(v_n_1618_);
return v___x_1625_;
}
}
else
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_dec(v_a_1623_);
lean_dec_ref(v_k_1621_);
lean_dec(v_n_1618_);
v___x_1635_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__13, &l_Lean_IR_ToIR_lowerCode___closed__13_once, _init_l_Lean_IR_ToIR_lowerCode___closed__13);
v___x_1636_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1635_, v_a_1248_, v_a_1249_, v_a_1250_);
return v___x_1636_;
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec_ref(v_k_1621_);
lean_dec(v_n_1618_);
v_a_1637_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1622_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1622_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
default: 
{
lean_object* v_fvarId_1645_; lean_object* v_k_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1675_; 
v_fvarId_1645_ = lean_ctor_get(v_c_1247_, 0);
v_k_1646_ = lean_ctor_get(v_c_1247_, 1);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_c_1247_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1648_ = v_c_1247_;
v_isShared_1649_ = v_isSharedCheck_1675_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_k_1646_);
lean_inc(v_fvarId_1645_);
lean_dec(v_c_1247_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1675_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1645_, v_a_1248_);
lean_dec(v_fvarId_1645_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1650_, 1);
if (lean_obj_tag(v_a_1651_) == 0)
{
lean_object* v_id_1652_; lean_object* v___x_1653_; 
v_id_1652_ = lean_ctor_get(v_a_1651_, 0);
lean_inc(v_id_1652_);
lean_dec_ref_known(v_a_1651_, 1);
v___x_1653_ = l_Lean_IR_ToIR_lowerCode(v_k_1646_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1664_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1656_ = v___x_1653_;
v_isShared_1657_ = v_isSharedCheck_1664_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1653_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1664_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1649_ == 0)
{
lean_ctor_set_tag(v___x_1648_, 8);
lean_ctor_set(v___x_1648_, 1, v_a_1654_);
lean_ctor_set(v___x_1648_, 0, v_id_1652_);
v___x_1659_ = v___x_1648_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_id_1652_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1661_; 
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1659_);
v___x_1661_ = v___x_1656_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_dec(v_id_1652_);
lean_del_object(v___x_1648_);
return v___x_1653_;
}
}
else
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
lean_dec(v_a_1651_);
lean_del_object(v___x_1648_);
lean_dec_ref(v_k_1646_);
v___x_1665_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__14, &l_Lean_IR_ToIR_lowerCode___closed__14_once, _init_l_Lean_IR_ToIR_lowerCode___closed__14);
v___x_1666_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1665_, v_a_1248_, v_a_1249_, v_a_1250_);
return v___x_1666_;
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_del_object(v___x_1648_);
lean_dec_ref(v_k_1646_);
v_a_1667_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1650_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1650_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object* v_decl_1676_, lean_object* v_k_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v_fvarId_1682_; lean_object* v___x_1683_; 
v_fvarId_1682_ = lean_ctor_get(v_decl_1676_, 0);
lean_inc(v_fvarId_1682_);
lean_dec_ref(v_decl_1676_);
v___x_1683_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_1682_, v_a_1678_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v___x_1684_; 
lean_dec_ref_known(v___x_1683_, 1);
v___x_1684_ = l_Lean_IR_ToIR_lowerCode(v_k_1677_, v_a_1678_, v_a_1679_, v_a_1680_);
return v___x_1684_;
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec_ref(v_k_1677_);
v_a_1685_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1683_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1683_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg___boxed(lean_object* v_decl_1693_, lean_object* v_k_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1693_, v_k_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
lean_dec(v_a_1695_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue___boxed(lean_object* v_decl_1700_, lean_object* v_k_1701_, lean_object* v_fvarId_1702_, lean_object* v_f_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1700_, v_k_1701_, v_fvarId_1702_, v_f_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
lean_dec(v_a_1704_);
lean_dec(v_fvarId_1702_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4___boxed(lean_object* v_sz_1709_, lean_object* v_i_1710_, lean_object* v_bs_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
size_t v_sz_boxed_1716_; size_t v_i_boxed_1717_; lean_object* v_res_1718_; 
v_sz_boxed_1716_ = lean_unbox_usize(v_sz_1709_);
lean_dec(v_sz_1709_);
v_i_boxed_1717_ = lean_unbox_usize(v_i_1710_);
lean_dec(v_i_1710_);
v_res_1718_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_boxed_1716_, v_i_boxed_1717_, v_bs_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt___boxed(lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_IR_ToIR_lowerAlt(v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_);
lean_dec(v_a_1722_);
lean_dec_ref(v_a_1721_);
lean_dec(v_a_1720_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___boxed(lean_object* v_decl_1725_, lean_object* v_k_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_IR_ToIR_lowerLet(v_decl_1725_, v_k_1726_, v_a_1727_, v_a_1728_, v_a_1729_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
lean_dec(v_a_1727_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode___boxed(lean_object* v_c_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_IR_ToIR_lowerCode(v_c_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
lean_dec(v_a_1735_);
lean_dec_ref(v_a_1734_);
lean_dec(v_a_1733_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object* v_decl_1738_, lean_object* v_k_1739_, lean_object* v_x_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1738_, v_k_1739_, v_a_1741_, v_a_1742_, v_a_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object* v_decl_1746_, lean_object* v_k_1747_, lean_object* v_x_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(v_decl_1746_, v_k_1747_, v_x_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
lean_dec(v_a_1749_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(size_t v_sz_1754_, size_t v_i_1755_, lean_object* v_bs_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1754_, v_i_1755_, v_bs_1756_, v___y_1757_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object* v_sz_1762_, lean_object* v_i_1763_, lean_object* v_bs_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
size_t v_sz_boxed_1769_; size_t v_i_boxed_1770_; lean_object* v_res_1771_; 
v_sz_boxed_1769_ = lean_unbox_usize(v_sz_1762_);
lean_dec(v_sz_1762_);
v_i_boxed_1770_ = lean_unbox_usize(v_i_1763_);
lean_dec(v_i_1763_);
v_res_1771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(v_sz_boxed_1769_, v_i_boxed_1770_, v_bs_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(size_t v_sz_1772_, size_t v_i_1773_, lean_object* v_bs_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1772_, v_i_1773_, v_bs_1774_, v___y_1775_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object* v_sz_1780_, lean_object* v_i_1781_, lean_object* v_bs_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
size_t v_sz_boxed_1787_; size_t v_i_boxed_1788_; lean_object* v_res_1789_; 
v_sz_boxed_1787_ = lean_unbox_usize(v_sz_1780_);
lean_dec(v_sz_1780_);
v_i_boxed_1788_ = lean_unbox_usize(v_i_1781_);
lean_dec(v_i_1781_);
v_res_1789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(v_sz_boxed_1787_, v_i_boxed_1788_, v_bs_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object* v_d_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v_toSignature_1795_; lean_object* v_value_1796_; lean_object* v_name_1797_; lean_object* v_type_1798_; lean_object* v_params_1799_; size_t v_sz_1800_; size_t v___x_1801_; lean_object* v___x_1802_; 
v_toSignature_1795_ = lean_ctor_get(v_d_1790_, 0);
lean_inc_ref(v_toSignature_1795_);
v_value_1796_ = lean_ctor_get(v_d_1790_, 1);
lean_inc_ref(v_value_1796_);
lean_dec_ref(v_d_1790_);
v_name_1797_ = lean_ctor_get(v_toSignature_1795_, 0);
lean_inc(v_name_1797_);
v_type_1798_ = lean_ctor_get(v_toSignature_1795_, 2);
lean_inc_ref(v_type_1798_);
v_params_1799_ = lean_ctor_get(v_toSignature_1795_, 3);
lean_inc_ref(v_params_1799_);
lean_dec_ref(v_toSignature_1795_);
v_sz_1800_ = lean_array_size(v_params_1799_);
v___x_1801_ = ((size_t)0ULL);
v___x_1802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1800_, v___x_1801_, v_params_1799_, v_a_1791_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1859_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1859_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1859_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_IR_toIRType(v_type_1798_);
lean_dec_ref(v_type_1798_);
if (lean_obj_tag(v_value_1796_) == 0)
{
lean_object* v_code_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1834_; 
lean_del_object(v___x_1805_);
v_code_1808_ = lean_ctor_get(v_value_1796_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_value_1796_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1810_ = v_value_1796_;
v_isShared_1811_ = v_isSharedCheck_1834_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_code_1808_);
lean_dec(v_value_1796_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1834_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Lean_IR_ToIR_lowerCode(v_code_1808_, v_a_1791_, v_a_1792_, v_a_1793_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1825_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1825_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1825_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1817_ = lean_box(0);
v___x_1818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1818_, 0, v_name_1797_);
lean_ctor_set(v___x_1818_, 1, v_a_1803_);
lean_ctor_set(v___x_1818_, 2, v___x_1807_);
lean_ctor_set(v___x_1818_, 3, v_a_1813_);
lean_ctor_set(v___x_1818_, 4, v___x_1817_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set_tag(v___x_1810_, 1);
lean_ctor_set(v___x_1810_, 0, v___x_1818_);
v___x_1820_ = v___x_1810_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1822_; 
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1820_);
v___x_1822_ = v___x_1815_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_del_object(v___x_1810_);
lean_dec(v___x_1807_);
lean_dec(v_a_1803_);
lean_dec(v_name_1797_);
v_a_1826_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1812_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1812_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
else
{
lean_object* v_externAttrData_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1858_; 
v_externAttrData_1835_ = lean_ctor_get(v_value_1796_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_value_1796_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1837_ = v_value_1796_;
v_isShared_1838_ = v_isSharedCheck_1858_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_externAttrData_1835_);
lean_dec(v_value_1796_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1858_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
uint8_t v___x_1839_; 
v___x_1839_ = l_List_isEmpty___redArg(v_externAttrData_1835_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1840_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1840_, 0, v_name_1797_);
lean_ctor_set(v___x_1840_, 1, v_a_1803_);
lean_ctor_set(v___x_1840_, 2, v___x_1807_);
lean_ctor_set(v___x_1840_, 3, v_externAttrData_1835_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1840_);
v___x_1842_ = v___x_1837_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1844_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1842_);
v___x_1844_ = v___x_1805_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1856_; 
lean_del_object(v___x_1837_);
lean_dec(v_externAttrData_1835_);
lean_del_object(v___x_1805_);
v___x_1847_ = l_Lean_IR_mkDummyExternDecl(v_name_1797_, v_a_1803_, v___x_1807_);
v___x_1848_ = l_Lean_IR_ToIR_addDecl___redArg(v___x_1847_, v_a_1793_);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1856_ == 0)
{
lean_object* v_unused_1857_; 
v_unused_1857_ = lean_ctor_get(v___x_1848_, 0);
lean_dec(v_unused_1857_);
v___x_1850_ = v___x_1848_;
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
else
{
lean_dec(v___x_1848_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1852_ = lean_box(0);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1852_);
v___x_1854_ = v___x_1850_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec_ref(v_type_1798_);
lean_dec(v_name_1797_);
lean_dec_ref(v_value_1796_);
v_a_1860_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1802_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1802_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl___boxed(lean_object* v_d_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_IR_ToIR_lowerDecl(v_d_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(lean_object* v_as_1874_, size_t v_sz_1875_, size_t v_i_1876_, lean_object* v_b_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
uint8_t v___x_1881_; 
v___x_1881_ = lean_usize_dec_lt(v_i_1876_, v_sz_1875_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v_b_1877_);
return v___x_1882_;
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v_a_1883_ = lean_array_uget_borrowed(v_as_1874_, v_i_1876_);
lean_inc(v_a_1883_);
v___x_1884_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerDecl___boxed), 5, 1);
lean_closure_set(v___x_1884_, 0, v_a_1883_);
v___x_1885_ = l_Lean_IR_ToIR_M_run___redArg(v___x_1884_, v___y_1878_, v___y_1879_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v_a_1888_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
if (lean_obj_tag(v_a_1886_) == 1)
{
lean_object* v_val_1892_; lean_object* v___x_1893_; 
v_val_1892_ = lean_ctor_get(v_a_1886_, 0);
lean_inc(v_val_1892_);
lean_dec_ref_known(v_a_1886_, 1);
v___x_1893_ = lean_array_push(v_b_1877_, v_val_1892_);
v_a_1888_ = v___x_1893_;
goto v___jp_1887_;
}
else
{
lean_dec(v_a_1886_);
v_a_1888_ = v_b_1877_;
goto v___jp_1887_;
}
v___jp_1887_:
{
size_t v___x_1889_; size_t v___x_1890_; 
v___x_1889_ = ((size_t)1ULL);
v___x_1890_ = lean_usize_add(v_i_1876_, v___x_1889_);
v_i_1876_ = v___x_1890_;
v_b_1877_ = v_a_1888_;
goto _start;
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec_ref(v_b_1877_);
v_a_1894_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1885_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1885_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0___boxed(lean_object* v_as_1902_, lean_object* v_sz_1903_, lean_object* v_i_1904_, lean_object* v_b_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
size_t v_sz_boxed_1909_; size_t v_i_boxed_1910_; lean_object* v_res_1911_; 
v_sz_boxed_1909_ = lean_unbox_usize(v_sz_1903_);
lean_dec(v_sz_1903_);
v_i_boxed_1910_ = lean_unbox_usize(v_i_1904_);
lean_dec(v_i_1904_);
v_res_1911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_as_1902_, v_sz_boxed_1909_, v_i_boxed_1910_, v_b_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec_ref(v_as_1902_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object* v_decls_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_){
_start:
{
lean_object* v_irDecls_1918_; size_t v_sz_1919_; size_t v___x_1920_; lean_object* v___x_1921_; 
v_irDecls_1918_ = ((lean_object*)(l_Lean_IR_toIR___closed__0));
v_sz_1919_ = lean_array_size(v_decls_1914_);
v___x_1920_ = ((size_t)0ULL);
v___x_1921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_decls_1914_, v_sz_1919_, v___x_1920_, v_irDecls_1918_, v_a_1915_, v_a_1916_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object* v_decls_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_IR_toIR(v_decls_1922_, v_a_1923_, v_a_1924_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
lean_dec_ref(v_decls_1922_);
return v_res_1926_;
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
