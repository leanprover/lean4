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
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_380_ = lean_box(0);
v___x_381_ = lean_box(1);
v___x_382_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_374_, v_fvarId_370_, v___x_381_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_382_);
v___x_384_ = v___x_378_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_382_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_joinPoints_375_);
lean_ctor_set(v_reuseFailAlloc_387_, 2, v_nextId_376_);
v___x_384_ = v_reuseFailAlloc_387_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_st_ref_put(v_a_371_, v___x_384_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_380_);
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
v___x_405_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_413_; lean_object* v_env_414_; lean_object* v_nextMacroScope_415_; lean_object* v_ngen_416_; lean_object* v_auxDeclNGen_417_; lean_object* v_traceState_418_; lean_object* v_recordedDeps_419_; lean_object* v_messages_420_; lean_object* v_infoState_421_; lean_object* v_snapshotTasks_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_438_; 
v___x_413_ = lean_st_ref_take(v_a_411_);
v_env_414_ = lean_ctor_get(v___x_413_, 0);
v_nextMacroScope_415_ = lean_ctor_get(v___x_413_, 1);
v_ngen_416_ = lean_ctor_get(v___x_413_, 2);
v_auxDeclNGen_417_ = lean_ctor_get(v___x_413_, 3);
v_traceState_418_ = lean_ctor_get(v___x_413_, 4);
v_recordedDeps_419_ = lean_ctor_get(v___x_413_, 6);
v_messages_420_ = lean_ctor_get(v___x_413_, 7);
v_infoState_421_ = lean_ctor_get(v___x_413_, 8);
v_snapshotTasks_422_ = lean_ctor_get(v___x_413_, 9);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; 
v_unused_439_ = lean_ctor_get(v___x_413_, 5);
lean_dec(v_unused_439_);
v___x_424_ = v___x_413_;
v_isShared_425_ = v_isSharedCheck_438_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_snapshotTasks_422_);
lean_inc(v_infoState_421_);
lean_inc(v_messages_420_);
lean_inc(v_recordedDeps_419_);
lean_inc(v_traceState_418_);
lean_inc(v_auxDeclNGen_417_);
lean_inc(v_ngen_416_);
lean_inc(v_nextMacroScope_415_);
lean_inc(v_env_414_);
lean_dec(v___x_413_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_438_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v_toEnvExtension_427_; lean_object* v_asyncMode_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_426_ = l_Lean_IR_declMapExt;
v_toEnvExtension_427_ = lean_ctor_get(v___x_426_, 0);
v_asyncMode_428_ = lean_ctor_get(v_toEnvExtension_427_, 2);
v___x_429_ = lean_box(0);
v___x_430_ = lean_box(0);
v___x_431_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_426_, v_env_414_, v_d_410_, v_asyncMode_428_, v___x_430_);
v___x_432_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__2, &l_Lean_IR_ToIR_addDecl___redArg___closed__2_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 5, v___x_432_);
lean_ctor_set(v___x_424_, 0, v___x_431_);
v___x_434_ = v___x_424_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_nextMacroScope_415_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_ngen_416_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_auxDeclNGen_417_);
lean_ctor_set(v_reuseFailAlloc_437_, 4, v_traceState_418_);
lean_ctor_set(v_reuseFailAlloc_437_, 5, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_437_, 6, v_recordedDeps_419_);
lean_ctor_set(v_reuseFailAlloc_437_, 7, v_messages_420_);
lean_ctor_set(v_reuseFailAlloc_437_, 8, v_infoState_421_);
lean_ctor_set(v_reuseFailAlloc_437_, 9, v_snapshotTasks_422_);
v___x_434_ = v_reuseFailAlloc_437_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_st_ref_put(v_a_411_, v___x_434_);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_429_);
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object* v_d_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_440_, v_a_441_);
lean_dec(v_a_441_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object* v_d_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_444_, v_a_447_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object* v_d_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_IR_ToIR_addDecl(v_d_450_, v_a_451_, v_a_452_, v_a_453_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object* v_v_456_){
_start:
{
switch(lean_obj_tag(v_v_456_))
{
case 0:
{
lean_object* v_val_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_471_; 
v_val_457_ = lean_ctor_get(v_v_456_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v_v_456_);
if (v_isSharedCheck_471_ == 0)
{
v___x_459_ = v_v_456_;
v_isShared_460_ = v_isSharedCheck_471_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_val_457_);
lean_dec(v_v_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_471_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___y_462_; lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = lean_cstr_to_nat("4294967296");
v___x_468_ = lean_nat_dec_lt(v_val_457_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; 
v___x_469_ = lean_box(8);
v___y_462_ = v___x_469_;
goto v___jp_461_;
}
else
{
lean_object* v___x_470_; 
v___x_470_ = lean_box(12);
v___y_462_ = v___x_470_;
goto v___jp_461_;
}
v___jp_461_:
{
lean_object* v___x_464_; 
if (v_isShared_460_ == 0)
{
v___x_464_ = v___x_459_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_val_457_);
v___x_464_ = v_reuseFailAlloc_466_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_465_; 
lean_inc(v___y_462_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v___y_462_);
return v___x_465_;
}
}
}
}
case 1:
{
lean_object* v_val_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_481_; 
v_val_472_ = lean_ctor_get(v_v_456_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v_v_456_);
if (v_isSharedCheck_481_ == 0)
{
v___x_474_ = v_v_456_;
v_isShared_475_ = v_isSharedCheck_481_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_val_472_);
lean_dec(v_v_456_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_481_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_val_472_);
v___x_477_ = v_reuseFailAlloc_480_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_box(7);
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_477_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
return v___x_479_;
}
}
}
case 2:
{
uint8_t v_val_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_val_482_ = lean_ctor_get_uint8(v_v_456_, 0);
lean_dec_ref_known(v_v_456_, 0);
v___x_483_ = lean_uint8_to_nat(v_val_482_);
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
v___x_485_ = lean_box(1);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
return v___x_486_;
}
case 3:
{
uint16_t v_val_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_val_487_ = lean_ctor_get_uint16(v_v_456_, 0);
lean_dec_ref_known(v_v_456_, 0);
v___x_488_ = lean_uint16_to_nat(v_val_487_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
v___x_490_ = lean_box(2);
v___x_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_489_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
return v___x_491_;
}
case 4:
{
uint32_t v_val_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_val_492_ = lean_ctor_get_uint32(v_v_456_, 0);
lean_dec_ref_known(v_v_456_, 0);
v___x_493_ = lean_uint32_to_nat(v_val_492_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
v___x_495_ = lean_box(3);
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
return v___x_496_;
}
case 5:
{
uint64_t v_val_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v_val_497_ = lean_ctor_get_uint64(v_v_456_, 0);
lean_dec_ref_known(v_v_456_, 0);
v___x_498_ = lean_uint64_to_nat(v_val_497_);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
v___x_500_ = lean_box(4);
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
return v___x_501_;
}
default: 
{
uint64_t v_val_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_val_502_ = lean_ctor_get_uint64(v_v_456_, 0);
lean_dec_ref_known(v_v_456_, 0);
v___x_503_ = lean_uint64_to_nat(v_val_502_);
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
v___x_505_ = lean_box(5);
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
return v___x_506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
if (lean_obj_tag(v_a_507_) == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_box(1);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
else
{
lean_object* v_fvarId_512_; lean_object* v___x_513_; 
v_fvarId_512_ = lean_ctor_get(v_a_507_, 0);
v___x_513_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_512_, v_a_508_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_514_, v_a_515_);
lean_dec(v_a_515_);
lean_dec(v_a_514_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_518_, v_a_519_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_IR_ToIR_lowerArg(v_a_524_, v_a_525_, v_a_526_, v_a_527_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
lean_dec(v_a_525_);
lean_dec(v_a_524_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg(lean_object* v_p_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_fvarId_533_; lean_object* v_type_534_; uint8_t v_borrow_535_; lean_object* v___x_536_; lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_550_; 
v_fvarId_533_ = lean_ctor_get(v_p_530_, 0);
lean_inc(v_fvarId_533_);
v_type_534_ = lean_ctor_get(v_p_530_, 2);
lean_inc_ref(v_type_534_);
v_borrow_535_ = lean_ctor_get_uint8(v_p_530_, sizeof(void*)*3);
lean_dec_ref(v_p_530_);
v___x_536_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_533_, v_a_531_);
v_a_537_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_550_ == 0)
{
v___x_539_ = v___x_536_;
v_isShared_540_ = v_isSharedCheck_550_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_550_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; uint8_t v___y_543_; 
v___x_541_ = l_Lean_IR_toIRType(v_type_534_);
lean_dec_ref(v_type_534_);
if (v_borrow_535_ == 0)
{
v___y_543_ = v_borrow_535_;
goto v___jp_542_;
}
else
{
uint8_t v___x_548_; 
v___x_548_ = l_Lean_IR_IRType_isScalar(v___x_541_);
if (v___x_548_ == 0)
{
v___y_543_ = v_borrow_535_;
goto v___jp_542_;
}
else
{
uint8_t v___x_549_; 
v___x_549_ = 0;
v___y_543_ = v___x_549_;
goto v___jp_542_;
}
}
v___jp_542_:
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_544_, 0, v_a_537_);
lean_ctor_set(v___x_544_, 1, v___x_541_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*2, v___y_543_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v___x_544_);
v___x_546_ = v___x_539_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg___boxed(lean_object* v_p_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_551_, v_a_552_);
lean_dec(v_a_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object* v_p_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_555_, v_a_556_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object* v_p_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_IR_ToIR_lowerParam(v_p_561_, v_a_562_, v_a_563_, v_a_564_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
lean_dec(v_a_562_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCtorInfo(lean_object* v_i_567_){
_start:
{
lean_object* v_name_568_; lean_object* v_cidx_569_; lean_object* v_size_570_; lean_object* v_usize_571_; lean_object* v_ssize_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
v_name_568_ = lean_ctor_get(v_i_567_, 0);
v_cidx_569_ = lean_ctor_get(v_i_567_, 1);
v_size_570_ = lean_ctor_get(v_i_567_, 2);
v_usize_571_ = lean_ctor_get(v_i_567_, 3);
v_ssize_572_ = lean_ctor_get(v_i_567_, 4);
v_isSharedCheck_579_ = !lean_is_exclusive(v_i_567_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v_i_567_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_ssize_572_);
lean_inc(v_usize_571_);
lean_inc(v_size_570_);
lean_inc(v_cidx_569_);
lean_inc(v_name_568_);
lean_dec(v_i_567_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_name_568_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_cidx_569_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v_size_570_);
lean_ctor_set(v_reuseFailAlloc_578_, 3, v_usize_571_);
lean_ctor_set(v_reuseFailAlloc_578_, 4, v_ssize_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0(void){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_instMonadEIO___redArg();
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(lean_object* v_msg_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v_toApplicative_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_622_; 
v___x_588_ = lean_obj_once(&l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0, &l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0_once, _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0);
v___x_589_ = l_StateRefT_x27_instMonad___redArg(v___x_588_);
v_toApplicative_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; 
v_unused_623_ = lean_ctor_get(v___x_589_, 1);
lean_dec(v_unused_623_);
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_622_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_toApplicative_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_622_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v_toFunctor_594_; lean_object* v_toSeq_595_; lean_object* v_toSeqLeft_596_; lean_object* v_toSeqRight_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_620_; 
v_toFunctor_594_ = lean_ctor_get(v_toApplicative_590_, 0);
v_toSeq_595_ = lean_ctor_get(v_toApplicative_590_, 2);
v_toSeqLeft_596_ = lean_ctor_get(v_toApplicative_590_, 3);
v_toSeqRight_597_ = lean_ctor_get(v_toApplicative_590_, 4);
v_isSharedCheck_620_ = !lean_is_exclusive(v_toApplicative_590_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v_toApplicative_590_, 1);
lean_dec(v_unused_621_);
v___x_599_ = v_toApplicative_590_;
v_isShared_600_ = v_isSharedCheck_620_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_toSeqRight_597_);
lean_inc(v_toSeqLeft_596_);
lean_inc(v_toSeq_595_);
lean_inc(v_toFunctor_594_);
lean_dec(v_toApplicative_590_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_620_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___f_603_; lean_object* v___f_604_; lean_object* v___x_605_; lean_object* v___f_606_; lean_object* v___f_607_; lean_object* v___f_608_; lean_object* v___x_610_; 
v___f_601_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1));
v___f_602_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2));
lean_inc_ref(v_toFunctor_594_);
v___f_603_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_603_, 0, v_toFunctor_594_);
v___f_604_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_604_, 0, v_toFunctor_594_);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___f_603_);
lean_ctor_set(v___x_605_, 1, v___f_604_);
v___f_606_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_606_, 0, v_toSeqRight_597_);
v___f_607_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_607_, 0, v_toSeqLeft_596_);
v___f_608_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_608_, 0, v_toSeq_595_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 4, v___f_606_);
lean_ctor_set(v___x_599_, 3, v___f_607_);
lean_ctor_set(v___x_599_, 2, v___f_608_);
lean_ctor_set(v___x_599_, 1, v___f_601_);
lean_ctor_set(v___x_599_, 0, v___x_605_);
v___x_610_ = v___x_599_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v___f_601_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v___f_608_);
lean_ctor_set(v_reuseFailAlloc_619_, 3, v___f_607_);
lean_ctor_set(v_reuseFailAlloc_619_, 4, v___f_606_);
v___x_610_ = v_reuseFailAlloc_619_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_612_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v___f_602_);
lean_ctor_set(v___x_592_, 0, v___x_610_);
v___x_612_ = v___x_592_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_610_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v___f_602_);
v___x_612_ = v_reuseFailAlloc_618_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_8394__overap_616_; lean_object* v___x_617_; 
v___x_613_ = l_StateRefT_x27_instMonad___redArg(v___x_612_);
v___x_614_ = l_Lean_IR_instInhabitedFnBody_default__1;
v___x_615_ = l_instInhabitedOfMonad___redArg(v___x_613_, v___x_614_);
v___x_8394__overap_616_ = lean_panic_fn_borrowed(v___x_615_, v_msg_583_);
lean_dec(v___x_615_);
lean_inc(v___y_586_);
lean_inc_ref(v___y_585_);
lean_inc(v___y_584_);
v___x_617_ = lean_apply_4(v___x_8394__overap_616_, v___y_584_, v___y_585_, v___y_586_, lean_box(0));
return v___x_617_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object* v_msg_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v_msg_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(size_t v_sz_630_, size_t v_i_631_, lean_object* v_bs_632_, lean_object* v___y_633_){
_start:
{
uint8_t v___x_635_; 
v___x_635_ = lean_usize_dec_lt(v_i_631_, v_sz_630_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v_bs_632_);
return v___x_636_;
}
else
{
lean_object* v_v_637_; lean_object* v___x_638_; lean_object* v_bs_x27_639_; lean_object* v___x_640_; 
v_v_637_ = lean_array_uget(v_bs_632_, v_i_631_);
v___x_638_ = lean_unsigned_to_nat(0u);
v_bs_x27_639_ = lean_array_uset(v_bs_632_, v_i_631_, v___x_638_);
v___x_640_ = l_Lean_IR_ToIR_lowerArg___redArg(v_v_637_, v___y_633_);
lean_dec(v_v_637_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; size_t v___x_642_; size_t v___x_643_; lean_object* v___x_644_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v___x_640_, 1);
v___x_642_ = ((size_t)1ULL);
v___x_643_ = lean_usize_add(v_i_631_, v___x_642_);
v___x_644_ = lean_array_uset(v_bs_x27_639_, v_i_631_, v_a_641_);
v_i_631_ = v___x_643_;
v_bs_632_ = v___x_644_;
goto _start;
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec_ref(v_bs_x27_639_);
v_a_646_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_640_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_640_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object* v_sz_654_, lean_object* v_i_655_, lean_object* v_bs_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
size_t v_sz_boxed_659_; size_t v_i_boxed_660_; lean_object* v_res_661_; 
v_sz_boxed_659_ = lean_unbox_usize(v_sz_654_);
lean_dec(v_sz_654_);
v_i_boxed_660_ = lean_unbox_usize(v_i_655_);
lean_dec(v_i_655_);
v_res_661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_boxed_659_, v_i_boxed_660_, v_bs_656_, v___y_657_);
lean_dec(v___y_657_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(size_t v_sz_662_, size_t v_i_663_, lean_object* v_bs_664_, lean_object* v___y_665_){
_start:
{
uint8_t v___x_667_; 
v___x_667_ = lean_usize_dec_lt(v_i_663_, v_sz_662_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v_bs_664_);
return v___x_668_;
}
else
{
lean_object* v_v_669_; lean_object* v___x_670_; lean_object* v_bs_x27_671_; lean_object* v___x_672_; 
v_v_669_ = lean_array_uget(v_bs_664_, v_i_663_);
v___x_670_ = lean_unsigned_to_nat(0u);
v_bs_x27_671_ = lean_array_uset(v_bs_664_, v_i_663_, v___x_670_);
v___x_672_ = l_Lean_IR_ToIR_lowerParam___redArg(v_v_669_, v___y_665_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
lean_dec_ref_known(v___x_672_, 1);
v___x_674_ = ((size_t)1ULL);
v___x_675_ = lean_usize_add(v_i_663_, v___x_674_);
v___x_676_ = lean_array_uset(v_bs_x27_671_, v_i_663_, v_a_673_);
v_i_663_ = v___x_675_;
v_bs_664_ = v___x_676_;
goto _start;
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec_ref(v_bs_x27_671_);
v_a_678_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_672_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_672_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg___boxed(lean_object* v_sz_686_, lean_object* v_i_687_, lean_object* v_bs_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
size_t v_sz_boxed_691_; size_t v_i_boxed_692_; lean_object* v_res_693_; 
v_sz_boxed_691_ = lean_unbox_usize(v_sz_686_);
lean_dec(v_sz_686_);
v_i_boxed_692_ = lean_unbox_usize(v_i_687_);
lean_dec(v_i_687_);
v_res_693_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_boxed_691_, v_i_boxed_692_, v_bs_688_, v___y_689_);
lean_dec(v___y_689_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2(lean_object* v_i_694_, lean_object* v_continueLet_695_, lean_object* v_var_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_701_, 0, v_i_694_);
lean_ctor_set(v___x_701_, 1, v_var_696_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
lean_inc(v___y_697_);
v___x_702_ = lean_apply_5(v_continueLet_695_, v___x_701_, v___y_697_, v___y_698_, v___y_699_, lean_box(0));
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2___boxed(lean_object* v_i_703_, lean_object* v_continueLet_704_, lean_object* v_var_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_IR_ToIR_lowerLet___lam__2(v_i_703_, v_continueLet_704_, v_var_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4(lean_object* v_n_711_, lean_object* v_offset_712_, lean_object* v_continueLet_713_, lean_object* v_var_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_719_, 0, v_n_711_);
lean_ctor_set(v___x_719_, 1, v_offset_712_);
lean_ctor_set(v___x_719_, 2, v_var_714_);
lean_inc(v___y_717_);
lean_inc_ref(v___y_716_);
lean_inc(v___y_715_);
v___x_720_ = lean_apply_5(v_continueLet_713_, v___x_719_, v___y_715_, v___y_716_, v___y_717_, lean_box(0));
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4___boxed(lean_object* v_n_721_, lean_object* v_offset_722_, lean_object* v_continueLet_723_, lean_object* v_var_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_IR_ToIR_lowerLet___lam__4(v_n_721_, v_offset_722_, v_continueLet_723_, v_var_724_, v___y_725_, v___y_726_, v___y_727_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5(lean_object* v_n_730_, lean_object* v_continueLet_731_, lean_object* v_var_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_737_, 0, v_n_730_);
lean_ctor_set(v___x_737_, 1, v_var_732_);
lean_inc(v___y_735_);
lean_inc_ref(v___y_734_);
lean_inc(v___y_733_);
v___x_738_ = lean_apply_5(v_continueLet_731_, v___x_737_, v___y_733_, v___y_734_, v___y_735_, lean_box(0));
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5___boxed(lean_object* v_n_739_, lean_object* v_continueLet_740_, lean_object* v_var_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_IR_ToIR_lowerLet___lam__5(v_n_739_, v_continueLet_740_, v_var_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8(lean_object* v_continueLet_747_, lean_object* v_var_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_753_, 0, v_var_748_);
lean_inc(v___y_751_);
lean_inc_ref(v___y_750_);
lean_inc(v___y_749_);
v___x_754_ = lean_apply_5(v_continueLet_747_, v___x_753_, v___y_749_, v___y_750_, v___y_751_, lean_box(0));
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8___boxed(lean_object* v_continueLet_755_, lean_object* v_var_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_IR_ToIR_lowerLet___lam__8(v_continueLet_755_, v_var_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3(lean_object* v_i_762_, lean_object* v_continueLet_763_, lean_object* v_var_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_769_, 0, v_i_762_);
lean_ctor_set(v___x_769_, 1, v_var_764_);
lean_inc(v___y_767_);
lean_inc_ref(v___y_766_);
lean_inc(v___y_765_);
v___x_770_ = lean_apply_5(v_continueLet_763_, v___x_769_, v___y_765_, v___y_766_, v___y_767_, lean_box(0));
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3___boxed(lean_object* v_i_771_, lean_object* v_continueLet_772_, lean_object* v_var_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_IR_ToIR_lowerLet___lam__3(v_i_771_, v_continueLet_772_, v_var_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7(lean_object* v_ty_779_, lean_object* v_continueLet_780_, lean_object* v_var_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_786_ = l_Lean_IR_toIRType(v_ty_779_);
v___x_787_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
lean_ctor_set(v___x_787_, 1, v_var_781_);
lean_inc(v___y_784_);
lean_inc_ref(v___y_783_);
lean_inc(v___y_782_);
v___x_788_ = lean_apply_5(v_continueLet_780_, v___x_787_, v___y_782_, v___y_783_, v___y_784_, lean_box(0));
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7___boxed(lean_object* v_ty_789_, lean_object* v_continueLet_790_, lean_object* v_var_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_IR_ToIR_lowerLet___lam__7(v_ty_789_, v_continueLet_790_, v_var_791_, v___y_792_, v___y_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v_ty_789_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6(lean_object* v_args_797_, lean_object* v_i_798_, uint8_t v_updateHeader_799_, lean_object* v_continueLet_800_, lean_object* v_var_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
size_t v_sz_806_; size_t v___x_807_; lean_object* v___x_808_; 
v_sz_806_ = lean_array_size(v_args_797_);
v___x_807_ = ((size_t)0ULL);
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_806_, v___x_807_, v_args_797_, v___y_802_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v_name_810_; lean_object* v_cidx_811_; lean_object* v_size_812_; lean_object* v_usize_813_; lean_object* v_ssize_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_823_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
v_name_810_ = lean_ctor_get(v_i_798_, 0);
v_cidx_811_ = lean_ctor_get(v_i_798_, 1);
v_size_812_ = lean_ctor_get(v_i_798_, 2);
v_usize_813_ = lean_ctor_get(v_i_798_, 3);
v_ssize_814_ = lean_ctor_get(v_i_798_, 4);
v_isSharedCheck_823_ = !lean_is_exclusive(v_i_798_);
if (v_isSharedCheck_823_ == 0)
{
v___x_816_ = v_i_798_;
v_isShared_817_ = v_isSharedCheck_823_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_ssize_814_);
lean_inc(v_usize_813_);
lean_inc(v_size_812_);
lean_inc(v_cidx_811_);
lean_inc(v_name_810_);
lean_dec(v_i_798_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_823_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_name_810_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_cidx_811_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_size_812_);
lean_ctor_set(v_reuseFailAlloc_822_, 3, v_usize_813_);
lean_ctor_set(v_reuseFailAlloc_822_, 4, v_ssize_814_);
v___x_819_ = v_reuseFailAlloc_822_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v___x_820_, 0, v_var_801_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
lean_ctor_set(v___x_820_, 2, v_a_809_);
lean_ctor_set_uint8(v___x_820_, sizeof(void*)*3, v_updateHeader_799_);
lean_inc(v___y_804_);
lean_inc_ref(v___y_803_);
lean_inc(v___y_802_);
v___x_821_ = lean_apply_5(v_continueLet_800_, v___x_820_, v___y_802_, v___y_803_, v___y_804_, lean_box(0));
return v___x_821_;
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_dec(v_var_801_);
lean_dec_ref(v_continueLet_800_);
lean_dec_ref(v_i_798_);
v_a_824_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_808_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_808_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6___boxed(lean_object* v_args_832_, lean_object* v_i_833_, lean_object* v_updateHeader_834_, lean_object* v_continueLet_835_, lean_object* v_var_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
uint8_t v_updateHeader_9451__boxed_841_; lean_object* v_res_842_; 
v_updateHeader_9451__boxed_841_ = lean_unbox(v_updateHeader_834_);
v_res_842_ = l_Lean_IR_ToIR_lowerLet___lam__6(v_args_832_, v_i_833_, v_updateHeader_9451__boxed_841_, v_continueLet_835_, v_var_836_, v___y_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9(lean_object* v_continueLet_843_, lean_object* v_var_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_849_, 0, v_var_844_);
lean_inc(v___y_847_);
lean_inc_ref(v___y_846_);
lean_inc(v___y_845_);
v___x_850_ = lean_apply_5(v_continueLet_843_, v___x_849_, v___y_845_, v___y_846_, v___y_847_, lean_box(0));
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9___boxed(lean_object* v_continueLet_851_, lean_object* v_var_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_IR_ToIR_lowerLet___lam__9(v_continueLet_851_, v_var_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1(lean_object* v_args_858_, lean_object* v_continueLet_859_, lean_object* v_id_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
size_t v_sz_865_; size_t v___x_866_; lean_object* v___x_867_; 
v_sz_865_ = lean_array_size(v_args_858_);
v___x_866_ = ((size_t)0ULL);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_865_, v___x_866_, v_args_858_, v___y_861_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v___x_869_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_869_, 0, v_id_860_);
lean_ctor_set(v___x_869_, 1, v_a_868_);
lean_inc(v___y_863_);
lean_inc_ref(v___y_862_);
lean_inc(v___y_861_);
v___x_870_ = lean_apply_5(v_continueLet_859_, v___x_869_, v___y_861_, v___y_862_, v___y_863_, lean_box(0));
return v___x_870_;
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_dec(v_id_860_);
lean_dec_ref(v_continueLet_859_);
v_a_871_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_867_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_867_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1___boxed(lean_object* v_args_879_, lean_object* v_continueLet_880_, lean_object* v_id_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_IR_ToIR_lowerLet___lam__1(v_args_879_, v_continueLet_880_, v_id_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0(lean_object* v_fvarId_887_, lean_object* v_k_888_, lean_object* v_type_889_, lean_object* v_e_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_887_, v___y_891_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_897_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_896_);
lean_dec_ref_known(v___x_895_, 1);
v___x_897_ = l_Lean_IR_ToIR_lowerCode(v_k_888_, v___y_891_, v___y_892_, v___y_893_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_906_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_906_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_906_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_906_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_904_; 
v___x_902_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_902_, 0, v_a_896_);
lean_ctor_set(v___x_902_, 1, v_type_889_);
lean_ctor_set(v___x_902_, 2, v_e_890_);
lean_ctor_set(v___x_902_, 3, v_a_898_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_902_);
v___x_904_ = v___x_900_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
else
{
lean_dec(v_a_896_);
lean_dec_ref(v_e_890_);
lean_dec(v_type_889_);
return v___x_897_;
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec_ref(v_e_890_);
lean_dec(v_type_889_);
lean_dec_ref(v_k_888_);
v_a_907_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_895_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_895_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object* v_fvarId_915_, lean_object* v_k_916_, lean_object* v_type_917_, lean_object* v_e_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_915_, v_k_916_, v_type_917_, v_e_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(lean_object* v_decl_924_, lean_object* v_k_925_, lean_object* v_fvarId_926_, lean_object* v_f_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_926_, v_a_928_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 1);
if (lean_obj_tag(v_a_933_) == 0)
{
lean_object* v_id_934_; lean_object* v___x_935_; 
lean_dec_ref(v_k_925_);
lean_dec_ref(v_decl_924_);
v_id_934_ = lean_ctor_get(v_a_933_, 0);
lean_inc(v_id_934_);
lean_dec_ref_known(v_a_933_, 1);
lean_inc(v_a_930_);
lean_inc_ref(v_a_929_);
lean_inc(v_a_928_);
v___x_935_ = lean_apply_5(v_f_927_, v_id_934_, v_a_928_, v_a_929_, v_a_930_, lean_box(0));
return v___x_935_;
}
else
{
lean_object* v___x_936_; 
lean_dec_ref(v_f_927_);
v___x_936_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_924_, v_k_925_, v_a_928_, v_a_929_, v_a_930_);
return v___x_936_;
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v_f_927_);
lean_dec_ref(v_k_925_);
lean_dec_ref(v_decl_924_);
v_a_937_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_932_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_932_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object* v_decl_945_, lean_object* v_k_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v_fvarId_951_; lean_object* v_type_952_; lean_object* v_value_953_; lean_object* v_type_954_; lean_object* v_continueLet_955_; 
v_fvarId_951_ = lean_ctor_get(v_decl_945_, 0);
v_type_952_ = lean_ctor_get(v_decl_945_, 2);
v_value_953_ = lean_ctor_get(v_decl_945_, 3);
lean_inc(v_value_953_);
v_type_954_ = l_Lean_IR_toIRType(v_type_952_);
lean_inc(v_type_954_);
lean_inc_ref(v_k_946_);
lean_inc(v_fvarId_951_);
v_continueLet_955_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 8, 3);
lean_closure_set(v_continueLet_955_, 0, v_fvarId_951_);
lean_closure_set(v_continueLet_955_, 1, v_k_946_);
lean_closure_set(v_continueLet_955_, 2, v_type_954_);
switch(lean_obj_tag(v_value_953_))
{
case 0:
{
lean_object* v_value_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_966_; 
lean_inc(v_fvarId_951_);
lean_dec_ref(v_continueLet_955_);
lean_dec_ref(v_decl_945_);
v_value_956_ = lean_ctor_get(v_value_953_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v_value_953_);
if (v_isSharedCheck_966_ == 0)
{
v___x_958_ = v_value_953_;
v_isShared_959_ = v_isSharedCheck_966_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_value_956_);
lean_dec(v_value_953_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_966_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v_fst_961_; lean_object* v___x_963_; 
v___x_960_ = l_Lean_IR_ToIR_lowerLitValue(v_value_956_);
v_fst_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_fst_961_);
lean_dec_ref(v___x_960_);
if (v_isShared_959_ == 0)
{
lean_ctor_set_tag(v___x_958_, 11);
lean_ctor_set(v___x_958_, 0, v_fst_961_);
v___x_963_ = v___x_958_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_fst_961_);
v___x_963_ = v_reuseFailAlloc_965_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_951_, v_k_946_, v_type_954_, v___x_963_, v_a_947_, v_a_948_, v_a_949_);
return v___x_964_;
}
}
}
case 1:
{
lean_object* v___x_967_; 
lean_dec_ref(v_continueLet_955_);
lean_dec(v_type_954_);
v___x_967_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_945_, v_k_946_, v_a_947_, v_a_948_, v_a_949_);
return v___x_967_;
}
case 4:
{
lean_object* v_fvarId_968_; lean_object* v_args_969_; lean_object* v___f_970_; lean_object* v___x_971_; 
lean_dec(v_type_954_);
v_fvarId_968_ = lean_ctor_get(v_value_953_, 0);
lean_inc(v_fvarId_968_);
v_args_969_ = lean_ctor_get(v_value_953_, 1);
lean_inc_ref(v_args_969_);
lean_dec_ref_known(v_value_953_, 2);
v___f_970_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__1___boxed), 7, 2);
lean_closure_set(v___f_970_, 0, v_args_969_);
lean_closure_set(v___f_970_, 1, v_continueLet_955_);
v___x_971_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_945_, v_k_946_, v_fvarId_968_, v___f_970_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_fvarId_968_);
return v___x_971_;
}
case 5:
{
lean_object* v_i_972_; lean_object* v_args_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1005_; 
lean_inc(v_fvarId_951_);
lean_dec_ref(v_continueLet_955_);
lean_dec_ref(v_decl_945_);
v_i_972_ = lean_ctor_get(v_value_953_, 0);
v_args_973_ = lean_ctor_get(v_value_953_, 1);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_value_953_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_975_ = v_value_953_;
v_isShared_976_ = v_isSharedCheck_1005_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_args_973_);
lean_inc(v_i_972_);
lean_dec(v_value_953_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1005_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
size_t v_sz_977_; size_t v___x_978_; lean_object* v___x_979_; 
v_sz_977_ = lean_array_size(v_args_973_);
v___x_978_ = ((size_t)0ULL);
v___x_979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_977_, v___x_978_, v_args_973_, v_a_947_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v_name_981_; lean_object* v_cidx_982_; lean_object* v_size_983_; lean_object* v_usize_984_; lean_object* v_ssize_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_996_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
v_name_981_ = lean_ctor_get(v_i_972_, 0);
v_cidx_982_ = lean_ctor_get(v_i_972_, 1);
v_size_983_ = lean_ctor_get(v_i_972_, 2);
v_usize_984_ = lean_ctor_get(v_i_972_, 3);
v_ssize_985_ = lean_ctor_get(v_i_972_, 4);
v_isSharedCheck_996_ = !lean_is_exclusive(v_i_972_);
if (v_isSharedCheck_996_ == 0)
{
v___x_987_ = v_i_972_;
v_isShared_988_ = v_isSharedCheck_996_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_ssize_985_);
lean_inc(v_usize_984_);
lean_inc(v_size_983_);
lean_inc(v_cidx_982_);
lean_inc(v_name_981_);
lean_dec(v_i_972_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_996_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_name_981_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_cidx_982_);
lean_ctor_set(v_reuseFailAlloc_995_, 2, v_size_983_);
lean_ctor_set(v_reuseFailAlloc_995_, 3, v_usize_984_);
lean_ctor_set(v_reuseFailAlloc_995_, 4, v_ssize_985_);
v___x_990_ = v_reuseFailAlloc_995_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_992_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set_tag(v___x_975_, 0);
lean_ctor_set(v___x_975_, 1, v_a_980_);
lean_ctor_set(v___x_975_, 0, v___x_990_);
v___x_992_ = v___x_975_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_a_980_);
v___x_992_ = v_reuseFailAlloc_994_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_951_, v_k_946_, v_type_954_, v___x_992_, v_a_947_, v_a_948_, v_a_949_);
return v___x_993_;
}
}
}
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_del_object(v___x_975_);
lean_dec_ref(v_i_972_);
lean_dec(v_type_954_);
lean_dec(v_fvarId_951_);
lean_dec_ref(v_k_946_);
v_a_997_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_979_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_979_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
}
case 6:
{
lean_object* v_i_1006_; lean_object* v_var_1007_; lean_object* v___f_1008_; lean_object* v___x_1009_; 
lean_dec(v_type_954_);
v_i_1006_ = lean_ctor_get(v_value_953_, 0);
lean_inc(v_i_1006_);
v_var_1007_ = lean_ctor_get(v_value_953_, 1);
lean_inc(v_var_1007_);
lean_dec_ref_known(v_value_953_, 2);
v___f_1008_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__2___boxed), 7, 2);
lean_closure_set(v___f_1008_, 0, v_i_1006_);
lean_closure_set(v___f_1008_, 1, v_continueLet_955_);
v___x_1009_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_945_, v_k_946_, v_var_1007_, v___f_1008_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_var_1007_);
return v___x_1009_;
}
case 7:
{
lean_object* v_i_1010_; lean_object* v_var_1011_; lean_object* v___f_1012_; lean_object* v___x_1013_; 
lean_dec(v_type_954_);
v_i_1010_ = lean_ctor_get(v_value_953_, 0);
lean_inc(v_i_1010_);
v_var_1011_ = lean_ctor_get(v_value_953_, 1);
lean_inc(v_var_1011_);
lean_dec_ref_known(v_value_953_, 2);
v___f_1012_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__3___boxed), 7, 2);
lean_closure_set(v___f_1012_, 0, v_i_1010_);
lean_closure_set(v___f_1012_, 1, v_continueLet_955_);
v___x_1013_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_945_, v_k_946_, v_var_1011_, v___f_1012_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_var_1011_);
return v___x_1013_;
}
case 8:
{
lean_object* v_n_1014_; lean_object* v_offset_1015_; lean_object* v_var_1016_; lean_object* v___f_1017_; lean_object* v___x_1018_; 
lean_dec(v_type_954_);
v_n_1014_ = lean_ctor_get(v_value_953_, 0);
lean_inc(v_n_1014_);
v_offset_1015_ = lean_ctor_get(v_value_953_, 1);
lean_inc(v_offset_1015_);
v_var_1016_ = lean_ctor_get(v_value_953_, 2);
lean_inc(v_var_1016_);
lean_dec_ref_known(v_value_953_, 3);
v___f_1017_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__4___boxed), 8, 3);
lean_closure_set(v___f_1017_, 0, v_n_1014_);
lean_closure_set(v___f_1017_, 1, v_offset_1015_);
lean_closure_set(v___f_1017_, 2, v_continueLet_955_);
v___x_1018_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_945_, v_k_946_, v_var_1016_, v___f_1017_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_var_1016_);
return v___x_1018_;
}
case 9:
{
lean_object* v_fn_1019_; lean_object* v_args_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1040_; 
lean_inc(v_fvarId_951_);
lean_dec_ref(v_continueLet_955_);
lean_dec_ref(v_decl_945_);
v_fn_1019_ = lean_ctor_get(v_value_953_, 0);
v_args_1020_ = lean_ctor_get(v_value_953_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_value_953_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1022_ = v_value_953_;
v_isShared_1023_ = v_isSharedCheck_1040_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_args_1020_);
lean_inc(v_fn_1019_);
lean_dec(v_value_953_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1040_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
size_t v_sz_1024_; size_t v___x_1025_; lean_object* v___x_1026_; 
v_sz_1024_ = lean_array_size(v_args_1020_);
v___x_1025_ = ((size_t)0ULL);
v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1024_, v___x_1025_, v_args_1020_, v_a_947_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1029_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 1);
if (v_isShared_1023_ == 0)
{
lean_ctor_set_tag(v___x_1022_, 6);
lean_ctor_set(v___x_1022_, 1, v_a_1027_);
v___x_1029_ = v___x_1022_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_fn_1019_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_a_1027_);
v___x_1029_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_951_, v_k_946_, v_type_954_, v___x_1029_, v_a_947_, v_a_948_, v_a_949_);
return v___x_1030_;
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_del_object(v___x_1022_);
lean_dec(v_fn_1019_);
lean_dec(v_type_954_);
lean_dec(v_fvarId_951_);
lean_dec_ref(v_k_946_);
v_a_1032_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1026_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1026_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
case 10:
{
lean_object* v_fn_1041_; lean_object* v_args_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1062_; 
lean_inc(v_fvarId_951_);
lean_dec_ref(v_continueLet_955_);
lean_dec_ref(v_decl_945_);
v_fn_1041_ = lean_ctor_get(v_value_953_, 0);
v_args_1042_ = lean_ctor_get(v_value_953_, 1);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_value_953_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1044_ = v_value_953_;
v_isShared_1045_ = v_isSharedCheck_1062_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_args_1042_);
lean_inc(v_fn_1041_);
lean_dec(v_value_953_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1062_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
size_t v_sz_1046_; size_t v___x_1047_; lean_object* v___x_1048_; 
v_sz_1046_ = lean_array_size(v_args_1042_);
v___x_1047_ = ((size_t)0ULL);
v___x_1048_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1046_, v___x_1047_, v_args_1042_, v_a_947_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1051_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 1);
if (v_isShared_1045_ == 0)
{
lean_ctor_set_tag(v___x_1044_, 7);
lean_ctor_set(v___x_1044_, 1, v_a_1049_);
v___x_1051_ = v___x_1044_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_fn_1041_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_a_1049_);
v___x_1051_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_951_, v_k_946_, v_type_954_, v___x_1051_, v_a_947_, v_a_948_, v_a_949_);
return v___x_1052_;
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_del_object(v___x_1044_);
lean_dec(v_fn_1041_);
lean_dec(v_type_954_);
lean_dec(v_fvarId_951_);
lean_dec_ref(v_k_946_);
v_a_1054_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1048_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1048_);
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
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
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
}
case 11:
{
lean_object* v_n_1063_; lean_object* v_var_1064_; lean_object* v___f_1065_; lean_object* v___x_1066_; 
lean_dec(v_type_954_);
v_n_1063_ = lean_ctor_get(v_value_953_, 0);
lean_inc(v_n_1063_);
v_var_1064_ = lean_ctor_get(v_value_953_, 1);
lean_inc(v_var_1064_);
lean_dec_ref_known(v_value_953_, 2);
v___f_1065_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__5___boxed), 7, 2);
lean_closure_set(v___f_1065_, 0, v_n_1063_);
lean_closure_set(v___f_1065_, 1, v_continueLet_955_);
v___x_1066_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_945_, v_k_946_, v_var_1064_, v___f_1065_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_var_1064_);
return v___x_1066_;
}
case 12:
{
lean_object* v_var_1067_; lean_object* v_i_1068_; uint8_t v_updateHeader_1069_; lean_object* v_args_1070_; lean_object* v___x_1071_; lean_object* v___f_1072_; lean_object* v___x_1073_; 
lean_dec(v_type_954_);
v_var_1067_ = lean_ctor_get(v_value_953_, 0);
lean_inc(v_var_1067_);
v_i_1068_ = lean_ctor_get(v_value_953_, 1);
lean_inc_ref(v_i_1068_);
v_updateHeader_1069_ = lean_ctor_get_uint8(v_value_953_, sizeof(void*)*3);
v_args_1070_ = lean_ctor_get(v_value_953_, 2);
lean_inc_ref(v_args_1070_);
lean_dec_ref_known(v_value_953_, 3);
v___x_1071_ = lean_box(v_updateHeader_1069_);
v___f_1072_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 9, 4);
lean_closure_set(v___f_1072_, 0, v_args_1070_);
lean_closure_set(v___f_1072_, 1, v_i_1068_);
lean_closure_set(v___f_1072_, 2, v___x_1071_);
lean_closure_set(v___f_1072_, 3, v_continueLet_955_);
v___x_1073_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_945_, v_k_946_, v_var_1067_, v___f_1072_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_var_1067_);
return v___x_1073_;
}
case 13:
{
lean_object* v_ty_1074_; lean_object* v_fvarId_1075_; lean_object* v___f_1076_; lean_object* v___x_1077_; 
lean_dec(v_type_954_);
v_ty_1074_ = lean_ctor_get(v_value_953_, 0);
lean_inc_ref(v_ty_1074_);
v_fvarId_1075_ = lean_ctor_get(v_value_953_, 1);
lean_inc(v_fvarId_1075_);
lean_dec_ref_known(v_value_953_, 2);
v___f_1076_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__7___boxed), 7, 2);
lean_closure_set(v___f_1076_, 0, v_ty_1074_);
lean_closure_set(v___f_1076_, 1, v_continueLet_955_);
v___x_1077_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_945_, v_k_946_, v_fvarId_1075_, v___f_1076_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_fvarId_1075_);
return v___x_1077_;
}
case 14:
{
lean_object* v_fvarId_1078_; lean_object* v___f_1079_; lean_object* v___x_1080_; 
lean_dec(v_type_954_);
v_fvarId_1078_ = lean_ctor_get(v_value_953_, 0);
lean_inc(v_fvarId_1078_);
lean_dec_ref_known(v_value_953_, 1);
v___f_1079_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__8___boxed), 6, 1);
lean_closure_set(v___f_1079_, 0, v_continueLet_955_);
v___x_1080_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_945_, v_k_946_, v_fvarId_1078_, v___f_1079_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_fvarId_1078_);
return v___x_1080_;
}
default: 
{
lean_object* v_fvarId_1081_; lean_object* v___f_1082_; lean_object* v___x_1083_; 
lean_dec(v_type_954_);
v_fvarId_1081_ = lean_ctor_get(v_value_953_, 0);
lean_inc(v_fvarId_1081_);
lean_dec_ref_known(v_value_953_, 1);
v___f_1082_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__9___boxed), 6, 1);
lean_closure_set(v___f_1082_, 0, v_continueLet_955_);
v___x_1083_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_945_, v_k_946_, v_fvarId_1081_, v___f_1082_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_fvarId_1081_);
return v___x_1083_;
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__3(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1087_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__2));
v___x_1088_ = lean_unsigned_to_nat(15u);
v___x_1089_ = lean_unsigned_to_nat(128u);
v___x_1090_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1091_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1092_ = l_mkPanicMessageWithDecl(v___x_1091_, v___x_1090_, v___x_1089_, v___x_1088_, v___x_1087_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
if (lean_obj_tag(v_a_1093_) == 1)
{
lean_object* v_info_1098_; lean_object* v_code_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1135_; 
v_info_1098_ = lean_ctor_get(v_a_1093_, 0);
v_code_1099_ = lean_ctor_get(v_a_1093_, 1);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_a_1093_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1101_ = v_a_1093_;
v_isShared_1102_ = v_isSharedCheck_1135_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_code_1099_);
lean_inc(v_info_1098_);
lean_dec(v_a_1093_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1135_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Lean_IR_ToIR_lowerCode(v_code_1099_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1126_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1126_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1126_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v_name_1108_; lean_object* v_cidx_1109_; lean_object* v_size_1110_; lean_object* v_usize_1111_; lean_object* v_ssize_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1125_; 
v_name_1108_ = lean_ctor_get(v_info_1098_, 0);
v_cidx_1109_ = lean_ctor_get(v_info_1098_, 1);
v_size_1110_ = lean_ctor_get(v_info_1098_, 2);
v_usize_1111_ = lean_ctor_get(v_info_1098_, 3);
v_ssize_1112_ = lean_ctor_get(v_info_1098_, 4);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_info_1098_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1114_ = v_info_1098_;
v_isShared_1115_ = v_isSharedCheck_1125_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_ssize_1112_);
lean_inc(v_usize_1111_);
lean_inc(v_size_1110_);
lean_inc(v_cidx_1109_);
lean_inc(v_name_1108_);
lean_dec(v_info_1098_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1125_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_name_1108_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_cidx_1109_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v_size_1110_);
lean_ctor_set(v_reuseFailAlloc_1124_, 3, v_usize_1111_);
lean_ctor_set(v_reuseFailAlloc_1124_, 4, v_ssize_1112_);
v___x_1117_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1119_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set_tag(v___x_1101_, 0);
lean_ctor_set(v___x_1101_, 1, v_a_1104_);
lean_ctor_set(v___x_1101_, 0, v___x_1117_);
v___x_1119_ = v___x_1101_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_a_1104_);
v___x_1119_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1121_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1119_);
v___x_1121_ = v___x_1106_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_del_object(v___x_1101_);
lean_dec_ref(v_info_1098_);
v_a_1127_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1103_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1103_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
else
{
lean_object* v_code_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1160_; 
v_code_1136_ = lean_ctor_get(v_a_1093_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_a_1093_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1138_ = v_a_1093_;
v_isShared_1139_ = v_isSharedCheck_1160_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_code_1136_);
lean_dec(v_a_1093_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1160_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_IR_ToIR_lowerCode(v_code_1136_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1151_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1143_ = v___x_1140_;
v_isShared_1144_ = v_isSharedCheck_1151_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1140_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1151_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1139_ == 0)
{
lean_ctor_set_tag(v___x_1138_, 1);
lean_ctor_set(v___x_1138_, 0, v_a_1141_);
v___x_1146_ = v___x_1138_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1148_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v___x_1146_);
v___x_1148_ = v___x_1143_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_del_object(v___x_1138_);
v_a_1152_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1140_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1140_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(size_t v_sz_1161_, size_t v_i_1162_, lean_object* v_bs_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
uint8_t v___x_1168_; 
v___x_1168_ = lean_usize_dec_lt(v_i_1162_, v_sz_1161_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v_bs_1163_);
return v___x_1169_;
}
else
{
lean_object* v_v_1170_; lean_object* v___x_1171_; lean_object* v_bs_x27_1172_; lean_object* v___x_1173_; 
v_v_1170_ = lean_array_uget(v_bs_1163_, v_i_1162_);
v___x_1171_ = lean_unsigned_to_nat(0u);
v_bs_x27_1172_ = lean_array_uset(v_bs_1163_, v_i_1162_, v___x_1171_);
v___x_1173_ = l_Lean_IR_ToIR_lowerAlt(v_v_1170_, v___y_1164_, v___y_1165_, v___y_1166_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; size_t v___x_1175_; size_t v___x_1176_; lean_object* v___x_1177_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1174_);
lean_dec_ref_known(v___x_1173_, 1);
v___x_1175_ = ((size_t)1ULL);
v___x_1176_ = lean_usize_add(v_i_1162_, v___x_1175_);
v___x_1177_ = lean_array_uset(v_bs_x27_1172_, v_i_1162_, v_a_1174_);
v_i_1162_ = v___x_1176_;
v_bs_1163_ = v___x_1177_;
goto _start;
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec_ref(v_bs_x27_1172_);
v_a_1179_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1173_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1173_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__5(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1188_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1189_ = lean_unsigned_to_nat(53u);
v___x_1190_ = lean_unsigned_to_nat(95u);
v___x_1191_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1192_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1193_ = l_mkPanicMessageWithDecl(v___x_1192_, v___x_1191_, v___x_1190_, v___x_1189_, v___x_1188_);
return v___x_1193_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__6(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1194_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1195_ = lean_unsigned_to_nat(44u);
v___x_1196_ = lean_unsigned_to_nat(106u);
v___x_1197_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1198_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1199_ = l_mkPanicMessageWithDecl(v___x_1198_, v___x_1197_, v___x_1196_, v___x_1195_, v___x_1194_);
return v___x_1199_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__7(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1200_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1201_ = lean_unsigned_to_nat(44u);
v___x_1202_ = lean_unsigned_to_nat(114u);
v___x_1203_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1204_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1205_ = l_mkPanicMessageWithDecl(v___x_1204_, v___x_1203_, v___x_1202_, v___x_1201_, v___x_1200_);
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__8(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1206_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1207_ = lean_unsigned_to_nat(34u);
v___x_1208_ = lean_unsigned_to_nat(113u);
v___x_1209_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1210_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1211_ = l_mkPanicMessageWithDecl(v___x_1210_, v___x_1209_, v___x_1208_, v___x_1207_, v___x_1206_);
return v___x_1211_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__9(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1212_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1213_ = lean_unsigned_to_nat(44u);
v___x_1214_ = lean_unsigned_to_nat(110u);
v___x_1215_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1216_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1217_ = l_mkPanicMessageWithDecl(v___x_1216_, v___x_1215_, v___x_1214_, v___x_1213_, v___x_1212_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__10(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1218_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1219_ = lean_unsigned_to_nat(34u);
v___x_1220_ = lean_unsigned_to_nat(109u);
v___x_1221_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1222_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1223_ = l_mkPanicMessageWithDecl(v___x_1222_, v___x_1221_, v___x_1220_, v___x_1219_, v___x_1218_);
return v___x_1223_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__11(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1224_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1225_ = lean_unsigned_to_nat(41u);
v___x_1226_ = lean_unsigned_to_nat(117u);
v___x_1227_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1228_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1229_ = l_mkPanicMessageWithDecl(v___x_1228_, v___x_1227_, v___x_1226_, v___x_1225_, v___x_1224_);
return v___x_1229_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__12(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1230_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1231_ = lean_unsigned_to_nat(41u);
v___x_1232_ = lean_unsigned_to_nat(120u);
v___x_1233_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1234_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1235_ = l_mkPanicMessageWithDecl(v___x_1234_, v___x_1233_, v___x_1232_, v___x_1231_, v___x_1230_);
return v___x_1235_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__13(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1236_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1237_ = lean_unsigned_to_nat(41u);
v___x_1238_ = lean_unsigned_to_nat(123u);
v___x_1239_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1240_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1241_ = l_mkPanicMessageWithDecl(v___x_1240_, v___x_1239_, v___x_1238_, v___x_1237_, v___x_1236_);
return v___x_1241_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__14(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1242_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1243_ = lean_unsigned_to_nat(41u);
v___x_1244_ = lean_unsigned_to_nat(126u);
v___x_1245_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1246_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1247_ = l_mkPanicMessageWithDecl(v___x_1246_, v___x_1245_, v___x_1244_, v___x_1243_, v___x_1242_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object* v_c_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_){
_start:
{
switch(lean_obj_tag(v_c_1248_))
{
case 0:
{
lean_object* v_decl_1253_; lean_object* v_k_1254_; lean_object* v___x_1255_; 
v_decl_1253_ = lean_ctor_get(v_c_1248_, 0);
lean_inc_ref(v_decl_1253_);
v_k_1254_ = lean_ctor_get(v_c_1248_, 1);
lean_inc_ref(v_k_1254_);
lean_dec_ref_known(v_c_1248_, 2);
v___x_1255_ = l_Lean_IR_ToIR_lowerLet(v_decl_1253_, v_k_1254_, v_a_1249_, v_a_1250_, v_a_1251_);
return v___x_1255_;
}
case 1:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_dec_ref_known(v_c_1248_, 2);
v___x_1256_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__3, &l_Lean_IR_ToIR_lowerCode___closed__3_once, _init_l_Lean_IR_ToIR_lowerCode___closed__3);
v___x_1257_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1256_, v_a_1249_, v_a_1250_, v_a_1251_);
return v___x_1257_;
}
case 2:
{
lean_object* v_decl_1258_; lean_object* v_k_1259_; lean_object* v_fvarId_1260_; lean_object* v_params_1261_; lean_object* v_value_1262_; lean_object* v___x_1263_; 
v_decl_1258_ = lean_ctor_get(v_c_1248_, 0);
lean_inc_ref(v_decl_1258_);
v_k_1259_ = lean_ctor_get(v_c_1248_, 1);
lean_inc_ref(v_k_1259_);
lean_dec_ref_known(v_c_1248_, 2);
v_fvarId_1260_ = lean_ctor_get(v_decl_1258_, 0);
lean_inc(v_fvarId_1260_);
v_params_1261_ = lean_ctor_get(v_decl_1258_, 2);
lean_inc_ref(v_params_1261_);
v_value_1262_ = lean_ctor_get(v_decl_1258_, 4);
lean_inc_ref(v_value_1262_);
lean_dec_ref(v_decl_1258_);
v___x_1263_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_1260_, v_a_1249_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; size_t v_sz_1265_; size_t v___x_1266_; lean_object* v___x_1267_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___x_1263_, 1);
v_sz_1265_ = lean_array_size(v_params_1261_);
v___x_1266_ = ((size_t)0ULL);
v___x_1267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1265_, v___x_1266_, v_params_1261_, v_a_1249_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1269_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1269_ = l_Lean_IR_ToIR_lowerCode(v_value_1262_, v_a_1249_, v_a_1250_, v_a_1251_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1271_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v___x_1271_ = l_Lean_IR_ToIR_lowerCode(v_k_1259_, v_a_1249_, v_a_1250_, v_a_1251_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1280_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1276_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1276_, 0, v_a_1264_);
lean_ctor_set(v___x_1276_, 1, v_a_1268_);
lean_ctor_set(v___x_1276_, 2, v_a_1270_);
lean_ctor_set(v___x_1276_, 3, v_a_1272_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1276_);
v___x_1278_ = v___x_1274_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
else
{
lean_dec(v_a_1270_);
lean_dec(v_a_1268_);
lean_dec(v_a_1264_);
return v___x_1271_;
}
}
else
{
lean_dec(v_a_1268_);
lean_dec(v_a_1264_);
lean_dec_ref(v_k_1259_);
return v___x_1269_;
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec(v_a_1264_);
lean_dec_ref(v_value_1262_);
lean_dec_ref(v_k_1259_);
v_a_1281_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1267_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1267_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec_ref(v_value_1262_);
lean_dec_ref(v_params_1261_);
lean_dec_ref(v_k_1259_);
v_a_1289_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1263_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1263_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_1297_; lean_object* v_args_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1334_; 
v_fvarId_1297_ = lean_ctor_get(v_c_1248_, 0);
v_args_1298_ = lean_ctor_get(v_c_1248_, 1);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_c_1248_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1300_ = v_c_1248_;
v_isShared_1301_ = v_isSharedCheck_1334_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_args_1298_);
lean_inc(v_fvarId_1297_);
lean_dec(v_c_1248_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1334_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_1297_, v_a_1249_);
lean_dec(v_fvarId_1297_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; size_t v_sz_1304_; size_t v___x_1305_; lean_object* v___x_1306_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
lean_dec_ref_known(v___x_1302_, 1);
v_sz_1304_ = lean_array_size(v_args_1298_);
v___x_1305_ = ((size_t)0ULL);
v___x_1306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1304_, v___x_1305_, v_args_1298_, v_a_1249_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1317_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1317_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1317_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1301_ == 0)
{
lean_ctor_set_tag(v___x_1300_, 11);
lean_ctor_set(v___x_1300_, 1, v_a_1307_);
lean_ctor_set(v___x_1300_, 0, v_a_1303_);
v___x_1312_ = v___x_1300_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1303_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1314_; 
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1312_);
v___x_1314_ = v___x_1309_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec(v_a_1303_);
lean_del_object(v___x_1300_);
v_a_1318_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1306_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1306_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_del_object(v___x_1300_);
lean_dec_ref(v_args_1298_);
v_a_1326_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1302_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1302_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
case 4:
{
lean_object* v_cases_1335_; lean_object* v_typeName_1336_; lean_object* v_discr_1337_; lean_object* v_alts_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1378_; 
v_cases_1335_ = lean_ctor_get(v_c_1248_, 0);
lean_inc_ref(v_cases_1335_);
lean_dec_ref_known(v_c_1248_, 1);
v_typeName_1336_ = lean_ctor_get(v_cases_1335_, 0);
v_discr_1337_ = lean_ctor_get(v_cases_1335_, 2);
v_alts_1338_ = lean_ctor_get(v_cases_1335_, 3);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_cases_1335_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v_cases_1335_, 1);
lean_dec(v_unused_1379_);
v___x_1340_ = v_cases_1335_;
v_isShared_1341_ = v_isSharedCheck_1378_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_alts_1338_);
lean_inc(v_discr_1337_);
lean_inc(v_typeName_1336_);
lean_dec(v_cases_1335_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1378_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_discr_1337_, v_a_1249_);
lean_dec(v_discr_1337_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1342_, 1);
if (lean_obj_tag(v_a_1343_) == 0)
{
lean_object* v_id_1344_; size_t v_sz_1345_; size_t v___x_1346_; lean_object* v___x_1347_; 
v_id_1344_ = lean_ctor_get(v_a_1343_, 0);
lean_inc(v_id_1344_);
lean_dec_ref_known(v_a_1343_, 1);
v_sz_1345_ = lean_array_size(v_alts_1338_);
v___x_1346_ = ((size_t)0ULL);
v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_1345_, v___x_1346_, v_alts_1338_, v_a_1249_, v_a_1250_, v_a_1251_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1359_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1359_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1359_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1352_ = l_Lean_IR_nameToIRType(v_typeName_1336_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set_tag(v___x_1340_, 9);
lean_ctor_set(v___x_1340_, 3, v_a_1348_);
lean_ctor_set(v___x_1340_, 2, v___x_1352_);
lean_ctor_set(v___x_1340_, 1, v_id_1344_);
v___x_1354_ = v___x_1340_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_typeName_1336_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_id_1344_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1358_, 3, v_a_1348_);
v___x_1354_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1356_; 
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1354_);
v___x_1356_ = v___x_1350_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_id_1344_);
lean_del_object(v___x_1340_);
lean_dec(v_typeName_1336_);
v_a_1360_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1347_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1347_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_dec(v_a_1343_);
lean_del_object(v___x_1340_);
lean_dec_ref(v_alts_1338_);
lean_dec(v_typeName_1336_);
v___x_1368_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__5, &l_Lean_IR_ToIR_lowerCode___closed__5_once, _init_l_Lean_IR_ToIR_lowerCode___closed__5);
v___x_1369_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1368_, v_a_1249_, v_a_1250_, v_a_1251_);
return v___x_1369_;
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_del_object(v___x_1340_);
lean_dec_ref(v_alts_1338_);
lean_dec(v_typeName_1336_);
v_a_1370_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1342_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1342_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1404_; 
v_fvarId_1380_ = lean_ctor_get(v_c_1248_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_c_1248_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1382_ = v_c_1248_;
v_isShared_1383_ = v_isSharedCheck_1404_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_fvarId_1380_);
lean_dec(v_c_1248_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1404_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1380_, v_a_1249_);
lean_dec(v_fvarId_1380_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1395_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1387_ = v___x_1384_;
v_isShared_1388_ = v_isSharedCheck_1395_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1395_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1383_ == 0)
{
lean_ctor_set_tag(v___x_1382_, 10);
lean_ctor_set(v___x_1382_, 0, v_a_1385_);
v___x_1390_ = v___x_1382_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1392_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1390_);
v___x_1392_ = v___x_1387_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_del_object(v___x_1382_);
v_a_1396_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1384_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1384_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
case 6:
{
lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1412_; 
v_isSharedCheck_1412_ = !lean_is_exclusive(v_c_1248_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; 
v_unused_1413_ = lean_ctor_get(v_c_1248_, 0);
lean_dec(v_unused_1413_);
v___x_1406_ = v_c_1248_;
v_isShared_1407_ = v_isSharedCheck_1412_;
goto v_resetjp_1405_;
}
else
{
lean_dec(v_c_1248_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1412_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1408_ = lean_box(12);
if (v_isShared_1407_ == 0)
{
lean_ctor_set_tag(v___x_1406_, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1408_);
v___x_1410_ = v___x_1406_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
case 7:
{
lean_object* v_fvarId_1414_; lean_object* v_i_1415_; lean_object* v_y_1416_; lean_object* v_k_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1456_; 
v_fvarId_1414_ = lean_ctor_get(v_c_1248_, 0);
v_i_1415_ = lean_ctor_get(v_c_1248_, 1);
v_y_1416_ = lean_ctor_get(v_c_1248_, 2);
v_k_1417_ = lean_ctor_get(v_c_1248_, 3);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_c_1248_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1419_ = v_c_1248_;
v_isShared_1420_ = v_isSharedCheck_1456_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_k_1417_);
lean_inc(v_y_1416_);
lean_inc(v_i_1415_);
lean_inc(v_fvarId_1414_);
lean_dec(v_c_1248_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1456_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_IR_ToIR_lowerArg___redArg(v_y_1416_, v_a_1249_);
lean_dec(v_y_1416_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1423_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
v___x_1423_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1414_, v_a_1249_);
lean_dec(v_fvarId_1414_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1423_, 1);
if (lean_obj_tag(v_a_1424_) == 0)
{
lean_object* v_id_1425_; lean_object* v___x_1426_; 
v_id_1425_ = lean_ctor_get(v_a_1424_, 0);
lean_inc(v_id_1425_);
lean_dec_ref_known(v_a_1424_, 1);
v___x_1426_ = l_Lean_IR_ToIR_lowerCode(v_k_1417_, v_a_1249_, v_a_1250_, v_a_1251_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1437_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1429_ = v___x_1426_;
v_isShared_1430_ = v_isSharedCheck_1437_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1437_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1420_ == 0)
{
lean_ctor_set_tag(v___x_1419_, 2);
lean_ctor_set(v___x_1419_, 3, v_a_1427_);
lean_ctor_set(v___x_1419_, 2, v_a_1422_);
lean_ctor_set(v___x_1419_, 0, v_id_1425_);
v___x_1432_ = v___x_1419_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_id_1425_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_i_1415_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v_a_1422_);
lean_ctor_set(v_reuseFailAlloc_1436_, 3, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1434_; 
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v___x_1432_);
v___x_1434_ = v___x_1429_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
else
{
lean_dec(v_id_1425_);
lean_dec(v_a_1422_);
lean_del_object(v___x_1419_);
lean_dec(v_i_1415_);
return v___x_1426_;
}
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_dec(v_a_1424_);
lean_dec(v_a_1422_);
lean_del_object(v___x_1419_);
lean_dec_ref(v_k_1417_);
lean_dec(v_i_1415_);
v___x_1438_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__6, &l_Lean_IR_ToIR_lowerCode___closed__6_once, _init_l_Lean_IR_ToIR_lowerCode___closed__6);
v___x_1439_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1438_, v_a_1249_, v_a_1250_, v_a_1251_);
return v___x_1439_;
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_a_1422_);
lean_del_object(v___x_1419_);
lean_dec_ref(v_k_1417_);
lean_dec(v_i_1415_);
v_a_1440_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1423_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1423_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_del_object(v___x_1419_);
lean_dec_ref(v_k_1417_);
lean_dec(v_i_1415_);
lean_dec(v_fvarId_1414_);
v_a_1448_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1421_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1421_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
case 8:
{
lean_object* v_fvarId_1457_; lean_object* v_i_1458_; lean_object* v_y_1459_; lean_object* v_k_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1502_; 
v_fvarId_1457_ = lean_ctor_get(v_c_1248_, 0);
v_i_1458_ = lean_ctor_get(v_c_1248_, 1);
v_y_1459_ = lean_ctor_get(v_c_1248_, 2);
v_k_1460_ = lean_ctor_get(v_c_1248_, 3);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_c_1248_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1462_ = v_c_1248_;
v_isShared_1463_ = v_isSharedCheck_1502_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_k_1460_);
lean_inc(v_y_1459_);
lean_inc(v_i_1458_);
lean_inc(v_fvarId_1457_);
lean_dec(v_c_1248_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1502_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1459_, v_a_1249_);
lean_dec(v_y_1459_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1465_);
lean_dec_ref_known(v___x_1464_, 1);
if (lean_obj_tag(v_a_1465_) == 0)
{
lean_object* v_id_1466_; lean_object* v___x_1467_; 
v_id_1466_ = lean_ctor_get(v_a_1465_, 0);
lean_inc(v_id_1466_);
lean_dec_ref_known(v_a_1465_, 1);
v___x_1467_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1457_, v_a_1249_);
lean_dec(v_fvarId_1457_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1468_);
lean_dec_ref_known(v___x_1467_, 1);
if (lean_obj_tag(v_a_1468_) == 0)
{
lean_object* v_id_1469_; lean_object* v___x_1470_; 
v_id_1469_ = lean_ctor_get(v_a_1468_, 0);
lean_inc(v_id_1469_);
lean_dec_ref_known(v_a_1468_, 1);
v___x_1470_ = l_Lean_IR_ToIR_lowerCode(v_k_1460_, v_a_1249_, v_a_1250_, v_a_1251_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1481_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1481_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1481_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1463_ == 0)
{
lean_ctor_set_tag(v___x_1462_, 4);
lean_ctor_set(v___x_1462_, 3, v_a_1471_);
lean_ctor_set(v___x_1462_, 2, v_id_1466_);
lean_ctor_set(v___x_1462_, 0, v_id_1469_);
v___x_1476_ = v___x_1462_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_id_1469_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_i_1458_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_id_1466_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1478_; 
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1476_);
v___x_1478_ = v___x_1473_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_dec(v_id_1469_);
lean_dec(v_id_1466_);
lean_del_object(v___x_1462_);
lean_dec(v_i_1458_);
return v___x_1470_;
}
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_dec(v_a_1468_);
lean_dec(v_id_1466_);
lean_del_object(v___x_1462_);
lean_dec_ref(v_k_1460_);
lean_dec(v_i_1458_);
v___x_1482_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__7, &l_Lean_IR_ToIR_lowerCode___closed__7_once, _init_l_Lean_IR_ToIR_lowerCode___closed__7);
v___x_1483_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1482_, v_a_1249_, v_a_1250_, v_a_1251_);
return v___x_1483_;
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec(v_id_1466_);
lean_del_object(v___x_1462_);
lean_dec_ref(v_k_1460_);
lean_dec(v_i_1458_);
v_a_1484_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1467_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1467_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
else
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
lean_dec(v_a_1465_);
lean_del_object(v___x_1462_);
lean_dec_ref(v_k_1460_);
lean_dec(v_i_1458_);
lean_dec(v_fvarId_1457_);
v___x_1492_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__8, &l_Lean_IR_ToIR_lowerCode___closed__8_once, _init_l_Lean_IR_ToIR_lowerCode___closed__8);
v___x_1493_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1492_, v_a_1249_, v_a_1250_, v_a_1251_);
return v___x_1493_;
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_del_object(v___x_1462_);
lean_dec_ref(v_k_1460_);
lean_dec(v_i_1458_);
lean_dec(v_fvarId_1457_);
v_a_1494_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1464_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1464_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
}
case 9:
{
lean_object* v_fvarId_1503_; lean_object* v_i_1504_; lean_object* v_offset_1505_; lean_object* v_y_1506_; lean_object* v_ty_1507_; lean_object* v_k_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1551_; 
v_fvarId_1503_ = lean_ctor_get(v_c_1248_, 0);
v_i_1504_ = lean_ctor_get(v_c_1248_, 1);
v_offset_1505_ = lean_ctor_get(v_c_1248_, 2);
v_y_1506_ = lean_ctor_get(v_c_1248_, 3);
v_ty_1507_ = lean_ctor_get(v_c_1248_, 4);
v_k_1508_ = lean_ctor_get(v_c_1248_, 5);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_c_1248_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1510_ = v_c_1248_;
v_isShared_1511_ = v_isSharedCheck_1551_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_k_1508_);
lean_inc(v_ty_1507_);
lean_inc(v_y_1506_);
lean_inc(v_offset_1505_);
lean_inc(v_i_1504_);
lean_inc(v_fvarId_1503_);
lean_dec(v_c_1248_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1551_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1506_, v_a_1249_);
lean_dec(v_y_1506_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1512_, 1);
if (lean_obj_tag(v_a_1513_) == 0)
{
lean_object* v_id_1514_; lean_object* v___x_1515_; 
v_id_1514_ = lean_ctor_get(v_a_1513_, 0);
lean_inc(v_id_1514_);
lean_dec_ref_known(v_a_1513_, 1);
v___x_1515_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1503_, v_a_1249_);
lean_dec(v_fvarId_1503_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref_known(v___x_1515_, 1);
if (lean_obj_tag(v_a_1516_) == 0)
{
lean_object* v_id_1517_; lean_object* v___x_1518_; 
v_id_1517_ = lean_ctor_get(v_a_1516_, 0);
lean_inc(v_id_1517_);
lean_dec_ref_known(v_a_1516_, 1);
v___x_1518_ = l_Lean_IR_ToIR_lowerCode(v_k_1508_, v_a_1249_, v_a_1250_, v_a_1251_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1530_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1521_ = v___x_1518_;
v_isShared_1522_ = v_isSharedCheck_1530_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1518_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1530_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1523_ = l_Lean_IR_toIRType(v_ty_1507_);
lean_dec_ref(v_ty_1507_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set_tag(v___x_1510_, 5);
lean_ctor_set(v___x_1510_, 5, v_a_1519_);
lean_ctor_set(v___x_1510_, 4, v___x_1523_);
lean_ctor_set(v___x_1510_, 3, v_id_1514_);
lean_ctor_set(v___x_1510_, 0, v_id_1517_);
v___x_1525_ = v___x_1510_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_id_1517_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_i_1504_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_offset_1505_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v_id_1514_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1529_, 5, v_a_1519_);
v___x_1525_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1527_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v___x_1525_);
v___x_1527_ = v___x_1521_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
else
{
lean_dec(v_id_1517_);
lean_dec(v_id_1514_);
lean_del_object(v___x_1510_);
lean_dec_ref(v_ty_1507_);
lean_dec(v_offset_1505_);
lean_dec(v_i_1504_);
return v___x_1518_;
}
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_dec(v_a_1516_);
lean_dec(v_id_1514_);
lean_del_object(v___x_1510_);
lean_dec_ref(v_k_1508_);
lean_dec_ref(v_ty_1507_);
lean_dec(v_offset_1505_);
lean_dec(v_i_1504_);
v___x_1531_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__9, &l_Lean_IR_ToIR_lowerCode___closed__9_once, _init_l_Lean_IR_ToIR_lowerCode___closed__9);
v___x_1532_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1531_, v_a_1249_, v_a_1250_, v_a_1251_);
return v___x_1532_;
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec(v_id_1514_);
lean_del_object(v___x_1510_);
lean_dec_ref(v_k_1508_);
lean_dec_ref(v_ty_1507_);
lean_dec(v_offset_1505_);
lean_dec(v_i_1504_);
v_a_1533_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1515_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1515_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
lean_dec(v_a_1513_);
lean_del_object(v___x_1510_);
lean_dec_ref(v_k_1508_);
lean_dec_ref(v_ty_1507_);
lean_dec(v_offset_1505_);
lean_dec(v_i_1504_);
lean_dec(v_fvarId_1503_);
v___x_1541_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__10, &l_Lean_IR_ToIR_lowerCode___closed__10_once, _init_l_Lean_IR_ToIR_lowerCode___closed__10);
v___x_1542_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1541_, v_a_1249_, v_a_1250_, v_a_1251_);
return v___x_1542_;
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_del_object(v___x_1510_);
lean_dec_ref(v_k_1508_);
lean_dec_ref(v_ty_1507_);
lean_dec(v_offset_1505_);
lean_dec(v_i_1504_);
lean_dec(v_fvarId_1503_);
v_a_1543_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1512_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1512_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
case 10:
{
lean_object* v_fvarId_1552_; lean_object* v_cidx_1553_; lean_object* v_k_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1583_; 
v_fvarId_1552_ = lean_ctor_get(v_c_1248_, 0);
v_cidx_1553_ = lean_ctor_get(v_c_1248_, 1);
v_k_1554_ = lean_ctor_get(v_c_1248_, 2);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_c_1248_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1556_ = v_c_1248_;
v_isShared_1557_ = v_isSharedCheck_1583_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_k_1554_);
lean_inc(v_cidx_1553_);
lean_inc(v_fvarId_1552_);
lean_dec(v_c_1248_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1583_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1552_, v_a_1249_);
lean_dec(v_fvarId_1552_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1558_, 1);
if (lean_obj_tag(v_a_1559_) == 0)
{
lean_object* v_id_1560_; lean_object* v___x_1561_; 
v_id_1560_ = lean_ctor_get(v_a_1559_, 0);
lean_inc(v_id_1560_);
lean_dec_ref_known(v_a_1559_, 1);
v___x_1561_ = l_Lean_IR_ToIR_lowerCode(v_k_1554_, v_a_1249_, v_a_1250_, v_a_1251_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1572_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1564_ = v___x_1561_;
v_isShared_1565_ = v_isSharedCheck_1572_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1561_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1572_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1557_ == 0)
{
lean_ctor_set_tag(v___x_1556_, 3);
lean_ctor_set(v___x_1556_, 2, v_a_1562_);
lean_ctor_set(v___x_1556_, 0, v_id_1560_);
v___x_1567_ = v___x_1556_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_id_1560_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_cidx_1553_);
lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1569_; 
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1567_);
v___x_1569_ = v___x_1564_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
else
{
lean_dec(v_id_1560_);
lean_del_object(v___x_1556_);
lean_dec(v_cidx_1553_);
return v___x_1561_;
}
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_dec(v_a_1559_);
lean_del_object(v___x_1556_);
lean_dec_ref(v_k_1554_);
lean_dec(v_cidx_1553_);
v___x_1573_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__11, &l_Lean_IR_ToIR_lowerCode___closed__11_once, _init_l_Lean_IR_ToIR_lowerCode___closed__11);
v___x_1574_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1573_, v_a_1249_, v_a_1250_, v_a_1251_);
return v___x_1574_;
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_del_object(v___x_1556_);
lean_dec_ref(v_k_1554_);
lean_dec(v_cidx_1553_);
v_a_1575_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1558_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1558_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
case 11:
{
lean_object* v_fvarId_1584_; lean_object* v_n_1585_; uint8_t v_check_1586_; uint8_t v_persistent_1587_; lean_object* v_k_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1617_; 
v_fvarId_1584_ = lean_ctor_get(v_c_1248_, 0);
v_n_1585_ = lean_ctor_get(v_c_1248_, 1);
v_check_1586_ = lean_ctor_get_uint8(v_c_1248_, sizeof(void*)*3);
v_persistent_1587_ = lean_ctor_get_uint8(v_c_1248_, sizeof(void*)*3 + 1);
v_k_1588_ = lean_ctor_get(v_c_1248_, 2);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_c_1248_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1590_ = v_c_1248_;
v_isShared_1591_ = v_isSharedCheck_1617_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_k_1588_);
lean_inc(v_n_1585_);
lean_inc(v_fvarId_1584_);
lean_dec(v_c_1248_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1617_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1584_, v_a_1249_);
lean_dec(v_fvarId_1584_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref_known(v___x_1592_, 1);
if (lean_obj_tag(v_a_1593_) == 0)
{
lean_object* v_id_1594_; lean_object* v___x_1595_; 
v_id_1594_ = lean_ctor_get(v_a_1593_, 0);
lean_inc(v_id_1594_);
lean_dec_ref_known(v_a_1593_, 1);
v___x_1595_ = l_Lean_IR_ToIR_lowerCode(v_k_1588_, v_a_1249_, v_a_1250_, v_a_1251_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1606_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1606_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1606_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1591_ == 0)
{
lean_ctor_set_tag(v___x_1590_, 6);
lean_ctor_set(v___x_1590_, 2, v_a_1596_);
lean_ctor_set(v___x_1590_, 0, v_id_1594_);
v___x_1601_ = v___x_1590_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_id_1594_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_n_1585_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_a_1596_);
lean_ctor_set_uint8(v_reuseFailAlloc_1605_, sizeof(void*)*3, v_check_1586_);
lean_ctor_set_uint8(v_reuseFailAlloc_1605_, sizeof(void*)*3 + 1, v_persistent_1587_);
v___x_1601_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1603_; 
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v___x_1601_);
v___x_1603_ = v___x_1598_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
else
{
lean_dec(v_id_1594_);
lean_del_object(v___x_1590_);
lean_dec(v_n_1585_);
return v___x_1595_;
}
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_dec(v_a_1593_);
lean_del_object(v___x_1590_);
lean_dec_ref(v_k_1588_);
lean_dec(v_n_1585_);
v___x_1607_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__12, &l_Lean_IR_ToIR_lowerCode___closed__12_once, _init_l_Lean_IR_ToIR_lowerCode___closed__12);
v___x_1608_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1607_, v_a_1249_, v_a_1250_, v_a_1251_);
return v___x_1608_;
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_del_object(v___x_1590_);
lean_dec_ref(v_k_1588_);
lean_dec(v_n_1585_);
v_a_1609_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1592_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1592_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
case 12:
{
lean_object* v_fvarId_1618_; lean_object* v_n_1619_; uint8_t v_check_1620_; uint8_t v_persistent_1621_; lean_object* v_k_1622_; lean_object* v___x_1623_; 
v_fvarId_1618_ = lean_ctor_get(v_c_1248_, 0);
lean_inc(v_fvarId_1618_);
v_n_1619_ = lean_ctor_get(v_c_1248_, 1);
lean_inc(v_n_1619_);
v_check_1620_ = lean_ctor_get_uint8(v_c_1248_, sizeof(void*)*4);
v_persistent_1621_ = lean_ctor_get_uint8(v_c_1248_, sizeof(void*)*4 + 1);
v_k_1622_ = lean_ctor_get(v_c_1248_, 3);
lean_inc_ref(v_k_1622_);
lean_dec_ref_known(v_c_1248_, 4);
v___x_1623_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1618_, v_a_1249_);
lean_dec(v_fvarId_1618_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 1);
if (lean_obj_tag(v_a_1624_) == 0)
{
lean_object* v_id_1625_; lean_object* v___x_1626_; 
v_id_1625_ = lean_ctor_get(v_a_1624_, 0);
lean_inc(v_id_1625_);
lean_dec_ref_known(v_a_1624_, 1);
v___x_1626_ = l_Lean_IR_ToIR_lowerCode(v_k_1622_, v_a_1249_, v_a_1250_, v_a_1251_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1635_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1629_ = v___x_1626_;
v_isShared_1630_ = v_isSharedCheck_1635_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1626_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1635_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1631_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v___x_1631_, 0, v_id_1625_);
lean_ctor_set(v___x_1631_, 1, v_n_1619_);
lean_ctor_set(v___x_1631_, 2, v_a_1627_);
lean_ctor_set_uint8(v___x_1631_, sizeof(void*)*3, v_check_1620_);
lean_ctor_set_uint8(v___x_1631_, sizeof(void*)*3 + 1, v_persistent_1621_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v___x_1631_);
v___x_1633_ = v___x_1629_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
else
{
lean_dec(v_id_1625_);
lean_dec(v_n_1619_);
return v___x_1626_;
}
}
else
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec(v_a_1624_);
lean_dec_ref(v_k_1622_);
lean_dec(v_n_1619_);
v___x_1636_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__13, &l_Lean_IR_ToIR_lowerCode___closed__13_once, _init_l_Lean_IR_ToIR_lowerCode___closed__13);
v___x_1637_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1636_, v_a_1249_, v_a_1250_, v_a_1251_);
return v___x_1637_;
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec_ref(v_k_1622_);
lean_dec(v_n_1619_);
v_a_1638_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1623_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1623_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
default: 
{
lean_object* v_fvarId_1646_; lean_object* v_k_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1676_; 
v_fvarId_1646_ = lean_ctor_get(v_c_1248_, 0);
v_k_1647_ = lean_ctor_get(v_c_1248_, 1);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_c_1248_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1649_ = v_c_1248_;
v_isShared_1650_ = v_isSharedCheck_1676_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_k_1647_);
lean_inc(v_fvarId_1646_);
lean_dec(v_c_1248_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1676_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1646_, v_a_1249_);
lean_dec(v_fvarId_1646_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref_known(v___x_1651_, 1);
if (lean_obj_tag(v_a_1652_) == 0)
{
lean_object* v_id_1653_; lean_object* v___x_1654_; 
v_id_1653_ = lean_ctor_get(v_a_1652_, 0);
lean_inc(v_id_1653_);
lean_dec_ref_known(v_a_1652_, 1);
v___x_1654_ = l_Lean_IR_ToIR_lowerCode(v_k_1647_, v_a_1249_, v_a_1250_, v_a_1251_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1665_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1657_ = v___x_1654_;
v_isShared_1658_ = v_isSharedCheck_1665_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1665_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set_tag(v___x_1649_, 8);
lean_ctor_set(v___x_1649_, 1, v_a_1655_);
lean_ctor_set(v___x_1649_, 0, v_id_1653_);
v___x_1660_ = v___x_1649_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_id_1653_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1662_; 
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v___x_1660_);
v___x_1662_ = v___x_1657_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_dec(v_id_1653_);
lean_del_object(v___x_1649_);
return v___x_1654_;
}
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_dec(v_a_1652_);
lean_del_object(v___x_1649_);
lean_dec_ref(v_k_1647_);
v___x_1666_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__14, &l_Lean_IR_ToIR_lowerCode___closed__14_once, _init_l_Lean_IR_ToIR_lowerCode___closed__14);
v___x_1667_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1666_, v_a_1249_, v_a_1250_, v_a_1251_);
return v___x_1667_;
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_del_object(v___x_1649_);
lean_dec_ref(v_k_1647_);
v_a_1668_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1651_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1651_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object* v_decl_1677_, lean_object* v_k_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v_fvarId_1683_; lean_object* v___x_1684_; 
v_fvarId_1683_ = lean_ctor_get(v_decl_1677_, 0);
lean_inc(v_fvarId_1683_);
lean_dec_ref(v_decl_1677_);
v___x_1684_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_1683_, v_a_1679_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v___x_1685_; 
lean_dec_ref_known(v___x_1684_, 1);
v___x_1685_ = l_Lean_IR_ToIR_lowerCode(v_k_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
return v___x_1685_;
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec_ref(v_k_1678_);
v_a_1686_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1684_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1684_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg___boxed(lean_object* v_decl_1694_, lean_object* v_k_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1694_, v_k_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue___boxed(lean_object* v_decl_1701_, lean_object* v_k_1702_, lean_object* v_fvarId_1703_, lean_object* v_f_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1701_, v_k_1702_, v_fvarId_1703_, v_f_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec(v_fvarId_1703_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4___boxed(lean_object* v_sz_1710_, lean_object* v_i_1711_, lean_object* v_bs_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
size_t v_sz_boxed_1717_; size_t v_i_boxed_1718_; lean_object* v_res_1719_; 
v_sz_boxed_1717_ = lean_unbox_usize(v_sz_1710_);
lean_dec(v_sz_1710_);
v_i_boxed_1718_ = lean_unbox_usize(v_i_1711_);
lean_dec(v_i_1711_);
v_res_1719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_boxed_1717_, v_i_boxed_1718_, v_bs_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt___boxed(lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_IR_ToIR_lowerAlt(v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_a_1721_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___boxed(lean_object* v_decl_1726_, lean_object* v_k_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_IR_ToIR_lowerLet(v_decl_1726_, v_k_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode___boxed(lean_object* v_c_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_IR_ToIR_lowerCode(v_c_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec(v_a_1734_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object* v_decl_1739_, lean_object* v_k_1740_, lean_object* v_x_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1739_, v_k_1740_, v_a_1742_, v_a_1743_, v_a_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object* v_decl_1747_, lean_object* v_k_1748_, lean_object* v_x_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(v_decl_1747_, v_k_1748_, v_x_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
lean_dec(v_a_1750_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(size_t v_sz_1755_, size_t v_i_1756_, lean_object* v_bs_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1755_, v_i_1756_, v_bs_1757_, v___y_1758_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object* v_sz_1763_, lean_object* v_i_1764_, lean_object* v_bs_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
size_t v_sz_boxed_1770_; size_t v_i_boxed_1771_; lean_object* v_res_1772_; 
v_sz_boxed_1770_ = lean_unbox_usize(v_sz_1763_);
lean_dec(v_sz_1763_);
v_i_boxed_1771_ = lean_unbox_usize(v_i_1764_);
lean_dec(v_i_1764_);
v_res_1772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(v_sz_boxed_1770_, v_i_boxed_1771_, v_bs_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(size_t v_sz_1773_, size_t v_i_1774_, lean_object* v_bs_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1773_, v_i_1774_, v_bs_1775_, v___y_1776_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object* v_sz_1781_, lean_object* v_i_1782_, lean_object* v_bs_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
size_t v_sz_boxed_1788_; size_t v_i_boxed_1789_; lean_object* v_res_1790_; 
v_sz_boxed_1788_ = lean_unbox_usize(v_sz_1781_);
lean_dec(v_sz_1781_);
v_i_boxed_1789_ = lean_unbox_usize(v_i_1782_);
lean_dec(v_i_1782_);
v_res_1790_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(v_sz_boxed_1788_, v_i_boxed_1789_, v_bs_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object* v_d_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v_toSignature_1796_; lean_object* v_value_1797_; lean_object* v_name_1798_; lean_object* v_type_1799_; lean_object* v_params_1800_; size_t v_sz_1801_; size_t v___x_1802_; lean_object* v___x_1803_; 
v_toSignature_1796_ = lean_ctor_get(v_d_1791_, 0);
lean_inc_ref(v_toSignature_1796_);
v_value_1797_ = lean_ctor_get(v_d_1791_, 1);
lean_inc_ref(v_value_1797_);
lean_dec_ref(v_d_1791_);
v_name_1798_ = lean_ctor_get(v_toSignature_1796_, 0);
lean_inc(v_name_1798_);
v_type_1799_ = lean_ctor_get(v_toSignature_1796_, 2);
lean_inc_ref(v_type_1799_);
v_params_1800_ = lean_ctor_get(v_toSignature_1796_, 3);
lean_inc_ref(v_params_1800_);
lean_dec_ref(v_toSignature_1796_);
v_sz_1801_ = lean_array_size(v_params_1800_);
v___x_1802_ = ((size_t)0ULL);
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1801_, v___x_1802_, v_params_1800_, v_a_1792_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1860_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1806_ = v___x_1803_;
v_isShared_1807_ = v_isSharedCheck_1860_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1803_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1860_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Lean_IR_toIRType(v_type_1799_);
lean_dec_ref(v_type_1799_);
if (lean_obj_tag(v_value_1797_) == 0)
{
lean_object* v_code_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1835_; 
lean_del_object(v___x_1806_);
v_code_1809_ = lean_ctor_get(v_value_1797_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_value_1797_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1811_ = v_value_1797_;
v_isShared_1812_ = v_isSharedCheck_1835_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_code_1809_);
lean_dec(v_value_1797_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1835_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Lean_IR_ToIR_lowerCode(v_code_1809_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1826_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1826_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1826_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1818_ = lean_box(0);
v___x_1819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1819_, 0, v_name_1798_);
lean_ctor_set(v___x_1819_, 1, v_a_1804_);
lean_ctor_set(v___x_1819_, 2, v___x_1808_);
lean_ctor_set(v___x_1819_, 3, v_a_1814_);
lean_ctor_set(v___x_1819_, 4, v___x_1818_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set_tag(v___x_1811_, 1);
lean_ctor_set(v___x_1811_, 0, v___x_1819_);
v___x_1821_ = v___x_1811_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1823_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1821_);
v___x_1823_ = v___x_1816_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
lean_del_object(v___x_1811_);
lean_dec(v___x_1808_);
lean_dec(v_a_1804_);
lean_dec(v_name_1798_);
v_a_1827_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1813_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1813_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
}
else
{
lean_object* v_externAttrData_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1859_; 
v_externAttrData_1836_ = lean_ctor_get(v_value_1797_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_value_1797_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1838_ = v_value_1797_;
v_isShared_1839_ = v_isSharedCheck_1859_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_externAttrData_1836_);
lean_dec(v_value_1797_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1859_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
uint8_t v___x_1840_; 
v___x_1840_ = l_List_isEmpty___redArg(v_externAttrData_1836_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1841_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1841_, 0, v_name_1798_);
lean_ctor_set(v___x_1841_, 1, v_a_1804_);
lean_ctor_set(v___x_1841_, 2, v___x_1808_);
lean_ctor_set(v___x_1841_, 3, v_externAttrData_1836_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1841_);
v___x_1843_ = v___x_1838_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1845_; 
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v___x_1843_);
v___x_1845_ = v___x_1806_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1857_; 
lean_del_object(v___x_1838_);
lean_dec(v_externAttrData_1836_);
lean_del_object(v___x_1806_);
v___x_1848_ = l_Lean_IR_mkDummyExternDecl(v_name_1798_, v_a_1804_, v___x_1808_);
v___x_1849_ = l_Lean_IR_ToIR_addDecl___redArg(v___x_1848_, v_a_1794_);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1857_ == 0)
{
lean_object* v_unused_1858_; 
v_unused_1858_ = lean_ctor_get(v___x_1849_, 0);
lean_dec(v_unused_1858_);
v___x_1851_ = v___x_1849_;
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
else
{
lean_dec(v___x_1849_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1853_ = lean_box(0);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1853_);
v___x_1855_ = v___x_1851_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec_ref(v_type_1799_);
lean_dec(v_name_1798_);
lean_dec_ref(v_value_1797_);
v_a_1861_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1803_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1803_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl___boxed(lean_object* v_d_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_IR_ToIR_lowerDecl(v_d_1869_, v_a_1870_, v_a_1871_, v_a_1872_);
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1871_);
lean_dec(v_a_1870_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(lean_object* v_as_1875_, size_t v_sz_1876_, size_t v_i_1877_, lean_object* v_b_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_a_1883_; uint8_t v___x_1887_; 
v___x_1887_ = lean_usize_dec_lt(v_i_1877_, v_sz_1876_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; 
v___x_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1888_, 0, v_b_1878_);
return v___x_1888_;
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v_a_1889_ = lean_array_uget_borrowed(v_as_1875_, v_i_1877_);
lean_inc(v_a_1889_);
v___x_1890_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerDecl___boxed), 5, 1);
lean_closure_set(v___x_1890_, 0, v_a_1889_);
v___x_1891_ = l_Lean_IR_ToIR_M_run___redArg(v___x_1890_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1891_, 1);
if (lean_obj_tag(v_a_1892_) == 1)
{
lean_object* v_val_1893_; lean_object* v___x_1894_; 
v_val_1893_ = lean_ctor_get(v_a_1892_, 0);
lean_inc(v_val_1893_);
lean_dec_ref_known(v_a_1892_, 1);
v___x_1894_ = lean_array_push(v_b_1878_, v_val_1893_);
v_a_1883_ = v___x_1894_;
goto v___jp_1882_;
}
else
{
lean_dec(v_a_1892_);
v_a_1883_ = v_b_1878_;
goto v___jp_1882_;
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_dec_ref(v_b_1878_);
v_a_1895_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1891_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1891_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
v___jp_1882_:
{
size_t v___x_1884_; size_t v___x_1885_; 
v___x_1884_ = ((size_t)1ULL);
v___x_1885_ = lean_usize_add(v_i_1877_, v___x_1884_);
v_i_1877_ = v___x_1885_;
v_b_1878_ = v_a_1883_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0___boxed(lean_object* v_as_1903_, lean_object* v_sz_1904_, lean_object* v_i_1905_, lean_object* v_b_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
size_t v_sz_boxed_1910_; size_t v_i_boxed_1911_; lean_object* v_res_1912_; 
v_sz_boxed_1910_ = lean_unbox_usize(v_sz_1904_);
lean_dec(v_sz_1904_);
v_i_boxed_1911_ = lean_unbox_usize(v_i_1905_);
lean_dec(v_i_1905_);
v_res_1912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_as_1903_, v_sz_boxed_1910_, v_i_boxed_1911_, v_b_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v_as_1903_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object* v_decls_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v_irDecls_1919_; size_t v_sz_1920_; size_t v___x_1921_; lean_object* v___x_1922_; 
v_irDecls_1919_ = ((lean_object*)(l_Lean_IR_toIR___closed__0));
v_sz_1920_ = lean_array_size(v_decls_1915_);
v___x_1921_ = ((size_t)0ULL);
v___x_1922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_decls_1915_, v_sz_1920_, v___x_1921_, v_irDecls_1919_, v_a_1916_, v_a_1917_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object* v_decls_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_IR_toIR(v_decls_1923_, v_a_1924_, v_a_1925_);
lean_dec(v_a_1925_);
lean_dec_ref(v_a_1924_);
lean_dec_ref(v_decls_1923_);
return v_res_1927_;
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
