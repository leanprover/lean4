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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_IR_mkDummyExternDecl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_declMapExt;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___lam__0(lean_object*, lean_object*, lean_object*);
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
v___x_9_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v___x_8_);
lean_ctor_set(v___x_9_, 2, v___x_7_);
lean_ctor_set(v___x_9_, 3, v___x_7_);
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
lean_object* v___x_276_; lean_object* v_vars_277_; lean_object* v_joinPoints_278_; lean_object* v_nextVarId_279_; lean_object* v_nextJpId_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_293_; 
v___x_276_ = lean_st_ref_take(v_a_274_);
v_vars_277_ = lean_ctor_get(v___x_276_, 0);
v_joinPoints_278_ = lean_ctor_get(v___x_276_, 1);
v_nextVarId_279_ = lean_ctor_get(v___x_276_, 2);
v_nextJpId_280_ = lean_ctor_get(v___x_276_, 3);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_293_ == 0)
{
v___x_282_ = v___x_276_;
v_isShared_283_ = v_isSharedCheck_293_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_nextJpId_280_);
lean_inc(v_nextVarId_279_);
lean_inc(v_joinPoints_278_);
lean_inc(v_vars_277_);
lean_dec(v___x_276_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_293_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
lean_inc(v_nextVarId_279_);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v_nextVarId_279_);
v___x_285_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_277_, v_fvarId_273_, v___x_284_);
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_add(v_nextVarId_279_, v___x_286_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 2, v___x_287_);
lean_ctor_set(v___x_282_, 0, v___x_285_);
v___x_289_ = v___x_282_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_joinPoints_278_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_292_, 3, v_nextJpId_280_);
v___x_289_ = v_reuseFailAlloc_292_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_st_ref_put(v_a_274_, v___x_289_);
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v_nextVarId_279_);
return v___x_291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg___boxed(lean_object* v_fvarId_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_294_, v_a_295_);
lean_dec(v_a_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object* v_fvarId_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_298_, v_a_299_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object* v_fvarId_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_IR_ToIR_bindVar(v_fvarId_304_, v_a_305_, v_a_306_, v_a_307_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0(lean_object* v_00_u03b2_310_, lean_object* v_m_311_, lean_object* v_a_312_, lean_object* v_b_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_m_311_, v_a_312_, v_b_313_);
return v___x_314_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(lean_object* v_00_u03b2_315_, lean_object* v_a_316_, lean_object* v_x_317_){
_start:
{
uint8_t v___x_318_; 
v___x_318_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_a_316_, v_x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_319_, lean_object* v_a_320_, lean_object* v_x_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(v_00_u03b2_319_, v_a_320_, v_x_321_);
lean_dec(v_x_321_);
lean_dec(v_a_320_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1(lean_object* v_00_u03b2_324_, lean_object* v_data_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(v_data_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_327_, lean_object* v_i_328_, lean_object* v_source_329_, lean_object* v_target_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(v_i_328_, v_source_329_, v_target_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_332_, lean_object* v_x_333_, lean_object* v_x_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_333_, v_x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object* v_fvarId_336_, lean_object* v_a_337_){
_start:
{
lean_object* v___x_339_; lean_object* v_vars_340_; lean_object* v_joinPoints_341_; lean_object* v_nextVarId_342_; lean_object* v_nextJpId_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_355_; 
v___x_339_ = lean_st_ref_take(v_a_337_);
v_vars_340_ = lean_ctor_get(v___x_339_, 0);
v_joinPoints_341_ = lean_ctor_get(v___x_339_, 1);
v_nextVarId_342_ = lean_ctor_get(v___x_339_, 2);
v_nextJpId_343_ = lean_ctor_get(v___x_339_, 3);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_355_ == 0)
{
v___x_345_ = v___x_339_;
v_isShared_346_ = v_isSharedCheck_355_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_nextJpId_343_);
lean_inc(v_nextVarId_342_);
lean_inc(v_joinPoints_341_);
lean_inc(v_vars_340_);
lean_dec(v___x_339_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_355_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_351_; 
lean_inc(v_nextJpId_343_);
v___x_347_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_joinPoints_341_, v_fvarId_336_, v_nextJpId_343_);
v___x_348_ = lean_unsigned_to_nat(1u);
v___x_349_ = lean_nat_add(v_nextJpId_343_, v___x_348_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 3, v___x_349_);
lean_ctor_set(v___x_345_, 1, v___x_347_);
v___x_351_ = v___x_345_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_vars_340_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_354_, 2, v_nextVarId_342_);
lean_ctor_set(v_reuseFailAlloc_354_, 3, v___x_349_);
v___x_351_ = v_reuseFailAlloc_354_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_st_ref_put(v_a_337_, v___x_351_);
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v_nextJpId_343_);
return v___x_353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object* v_fvarId_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_356_, v_a_357_);
lean_dec(v_a_357_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object* v_fvarId_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_360_, v_a_361_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object* v_fvarId_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_IR_ToIR_bindJoinPoint(v_fvarId_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object* v_fvarId_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___x_375_; lean_object* v_vars_376_; lean_object* v_joinPoints_377_; lean_object* v_nextVarId_378_; lean_object* v_nextJpId_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_391_; 
v___x_375_ = lean_st_ref_take(v_a_373_);
v_vars_376_ = lean_ctor_get(v___x_375_, 0);
v_joinPoints_377_ = lean_ctor_get(v___x_375_, 1);
v_nextVarId_378_ = lean_ctor_get(v___x_375_, 2);
v_nextJpId_379_ = lean_ctor_get(v___x_375_, 3);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_391_ == 0)
{
v___x_381_ = v___x_375_;
v_isShared_382_ = v_isSharedCheck_391_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_nextJpId_379_);
lean_inc(v_nextVarId_378_);
lean_inc(v_joinPoints_377_);
lean_inc(v_vars_376_);
lean_dec(v___x_375_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_391_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_383_ = lean_box(0);
v___x_384_ = lean_box(1);
v___x_385_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_376_, v_fvarId_372_, v___x_384_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_385_);
v___x_387_ = v___x_381_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_joinPoints_377_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v_nextVarId_378_);
lean_ctor_set(v_reuseFailAlloc_390_, 3, v_nextJpId_379_);
v___x_387_ = v_reuseFailAlloc_390_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_st_ref_put(v_a_373_, v___x_387_);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_383_);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg___boxed(lean_object* v_fvarId_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_392_, v_a_393_);
lean_dec(v_a_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object* v_fvarId_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_396_, v_a_397_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object* v_fvarId_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_IR_ToIR_bindErased(v_fvarId_402_, v_a_403_, v_a_404_, v_a_405_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___lam__0(lean_object* v___x_408_, lean_object* v_d_409_, lean_object* v_s_410_){
_start:
{
lean_object* v_addEntryFn_411_; lean_object* v_importedEntries_412_; lean_object* v_state_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_421_; 
v_addEntryFn_411_ = lean_ctor_get(v___x_408_, 3);
lean_inc(v_addEntryFn_411_);
lean_dec_ref(v___x_408_);
v_importedEntries_412_ = lean_ctor_get(v_s_410_, 0);
v_state_413_ = lean_ctor_get(v_s_410_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v_s_410_);
if (v_isSharedCheck_421_ == 0)
{
v___x_415_ = v_s_410_;
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_state_413_);
lean_inc(v_importedEntries_412_);
lean_dec(v_s_410_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v_state_417_; lean_object* v___x_419_; 
v_state_417_ = lean_apply_2(v_addEntryFn_411_, v_state_413_, v_d_409_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v_state_417_);
v___x_419_ = v___x_415_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_importedEntries_412_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_state_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_422_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__0, &l_Lean_IR_ToIR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__1, &l_Lean_IR_ToIR_addDecl___redArg___closed__1_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object* v_d_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___x_430_; lean_object* v_env_431_; lean_object* v_nextMacroScope_432_; lean_object* v_ngen_433_; lean_object* v_auxDeclNGen_434_; lean_object* v_traceState_435_; lean_object* v_recordedDeps_436_; lean_object* v_messages_437_; lean_object* v_infoState_438_; lean_object* v_snapshotTasks_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_462_; 
v___x_430_ = lean_st_ref_take(v_a_428_);
v_env_431_ = lean_ctor_get(v___x_430_, 0);
v_nextMacroScope_432_ = lean_ctor_get(v___x_430_, 1);
v_ngen_433_ = lean_ctor_get(v___x_430_, 2);
v_auxDeclNGen_434_ = lean_ctor_get(v___x_430_, 3);
v_traceState_435_ = lean_ctor_get(v___x_430_, 4);
v_recordedDeps_436_ = lean_ctor_get(v___x_430_, 6);
v_messages_437_ = lean_ctor_get(v___x_430_, 7);
v_infoState_438_ = lean_ctor_get(v___x_430_, 8);
v_snapshotTasks_439_ = lean_ctor_get(v___x_430_, 9);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; 
v_unused_463_ = lean_ctor_get(v___x_430_, 5);
lean_dec(v_unused_463_);
v___x_441_ = v___x_430_;
v_isShared_442_ = v_isSharedCheck_462_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_snapshotTasks_439_);
lean_inc(v_infoState_438_);
lean_inc(v_messages_437_);
lean_inc(v_recordedDeps_436_);
lean_inc(v_traceState_435_);
lean_inc(v_auxDeclNGen_434_);
lean_inc(v_ngen_433_);
lean_inc(v_nextMacroScope_432_);
lean_inc(v_env_431_);
lean_dec(v___x_430_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_462_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v_toEnvExtension_444_; lean_object* v_asyncMode_445_; uint8_t v_logWrites_446_; lean_object* v___x_447_; lean_object* v___y_449_; lean_object* v___f_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_443_ = l_Lean_IR_declMapExt;
v_toEnvExtension_444_ = lean_ctor_get(v___x_443_, 0);
v_asyncMode_445_ = lean_ctor_get(v_toEnvExtension_444_, 2);
v_logWrites_446_ = lean_ctor_get_uint8(v_toEnvExtension_444_, sizeof(void*)*6);
v___x_447_ = lean_box(0);
v___f_456_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_addDecl___redArg___lam__0), 3, 2);
lean_closure_set(v___f_456_, 0, v___x_443_);
lean_closure_set(v___f_456_, 1, v_d_427_);
v___x_457_ = lean_box(0);
v___x_458_ = 1;
if (v_logWrites_446_ == 0)
{
lean_object* v___x_459_; 
lean_inc_ref(v_toEnvExtension_444_);
v___x_459_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_444_, v_env_431_, v___f_456_, v_asyncMode_445_, v___x_457_, v___x_458_);
v___y_449_ = v___x_459_;
goto v___jp_448_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; 
lean_inc_ref_n(v_toEnvExtension_444_, 2);
v___x_460_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_444_, v_env_431_);
lean_dec_ref(v_env_431_);
v___x_461_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_444_, v___x_460_, v___f_456_, v_asyncMode_445_, v___x_457_, v___x_458_);
v___y_449_ = v___x_461_;
goto v___jp_448_;
}
v___jp_448_:
{
lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_450_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__2, &l_Lean_IR_ToIR_addDecl___redArg___closed__2_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 5, v___x_450_);
lean_ctor_set(v___x_441_, 0, v___y_449_);
v___x_452_ = v___x_441_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___y_449_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_nextMacroScope_432_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_ngen_433_);
lean_ctor_set(v_reuseFailAlloc_455_, 3, v_auxDeclNGen_434_);
lean_ctor_set(v_reuseFailAlloc_455_, 4, v_traceState_435_);
lean_ctor_set(v_reuseFailAlloc_455_, 5, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_455_, 6, v_recordedDeps_436_);
lean_ctor_set(v_reuseFailAlloc_455_, 7, v_messages_437_);
lean_ctor_set(v_reuseFailAlloc_455_, 8, v_infoState_438_);
lean_ctor_set(v_reuseFailAlloc_455_, 9, v_snapshotTasks_439_);
v___x_452_ = v_reuseFailAlloc_455_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_st_ref_put(v_a_428_, v___x_452_);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_447_);
return v___x_454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object* v_d_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_464_, v_a_465_);
lean_dec(v_a_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object* v_d_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_468_, v_a_471_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object* v_d_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_IR_ToIR_addDecl(v_d_474_, v_a_475_, v_a_476_, v_a_477_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object* v_v_480_){
_start:
{
switch(lean_obj_tag(v_v_480_))
{
case 0:
{
lean_object* v_val_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_495_; 
v_val_481_ = lean_ctor_get(v_v_480_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v_v_480_);
if (v_isSharedCheck_495_ == 0)
{
v___x_483_ = v_v_480_;
v_isShared_484_ = v_isSharedCheck_495_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_val_481_);
lean_dec(v_v_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_495_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___y_486_; lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_491_ = lean_cstr_to_nat("4294967296");
v___x_492_ = lean_nat_dec_lt(v_val_481_, v___x_491_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; 
v___x_493_ = lean_box(8);
v___y_486_ = v___x_493_;
goto v___jp_485_;
}
else
{
lean_object* v___x_494_; 
v___x_494_ = lean_box(12);
v___y_486_ = v___x_494_;
goto v___jp_485_;
}
v___jp_485_:
{
lean_object* v___x_488_; 
if (v_isShared_484_ == 0)
{
v___x_488_ = v___x_483_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_val_481_);
v___x_488_ = v_reuseFailAlloc_490_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; 
lean_inc(v___y_486_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v___y_486_);
return v___x_489_;
}
}
}
}
case 1:
{
lean_object* v_val_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_505_; 
v_val_496_ = lean_ctor_get(v_v_480_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v_v_480_);
if (v_isSharedCheck_505_ == 0)
{
v___x_498_ = v_v_480_;
v_isShared_499_ = v_isSharedCheck_505_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_val_496_);
lean_dec(v_v_480_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_505_;
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
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_val_496_);
v___x_501_ = v_reuseFailAlloc_504_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_box(7);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_501_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
return v___x_503_;
}
}
}
case 2:
{
uint8_t v_val_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v_val_506_ = lean_ctor_get_uint8(v_v_480_, 0);
lean_dec_ref_known(v_v_480_, 0);
v___x_507_ = lean_uint8_to_nat(v_val_506_);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
v___x_509_ = lean_box(1);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
return v___x_510_;
}
case 3:
{
uint16_t v_val_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_val_511_ = lean_ctor_get_uint16(v_v_480_, 0);
lean_dec_ref_known(v_v_480_, 0);
v___x_512_ = lean_uint16_to_nat(v_val_511_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
v___x_514_ = lean_box(2);
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
return v___x_515_;
}
case 4:
{
uint32_t v_val_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_val_516_ = lean_ctor_get_uint32(v_v_480_, 0);
lean_dec_ref_known(v_v_480_, 0);
v___x_517_ = lean_uint32_to_nat(v_val_516_);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
v___x_519_ = lean_box(3);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
return v___x_520_;
}
case 5:
{
uint64_t v_val_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_val_521_ = lean_ctor_get_uint64(v_v_480_, 0);
lean_dec_ref_known(v_v_480_, 0);
v___x_522_ = lean_uint64_to_nat(v_val_521_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
v___x_524_ = lean_box(4);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
return v___x_525_;
}
default: 
{
uint64_t v_val_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_val_526_ = lean_ctor_get_uint64(v_v_480_, 0);
lean_dec_ref_known(v_v_480_, 0);
v___x_527_ = lean_uint64_to_nat(v_val_526_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
v___x_529_ = lean_box(5);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
if (lean_obj_tag(v_a_531_) == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_box(1);
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
else
{
lean_object* v_fvarId_536_; lean_object* v___x_537_; 
v_fvarId_536_ = lean_ctor_get(v_a_531_, 0);
v___x_537_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_536_, v_a_532_);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_538_, v_a_539_);
lean_dec(v_a_539_);
lean_dec(v_a_538_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_542_, v_a_543_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_IR_ToIR_lowerArg(v_a_548_, v_a_549_, v_a_550_, v_a_551_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec(v_a_548_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg(lean_object* v_p_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_fvarId_557_; lean_object* v_type_558_; uint8_t v_borrow_559_; lean_object* v___x_560_; lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_574_; 
v_fvarId_557_ = lean_ctor_get(v_p_554_, 0);
lean_inc(v_fvarId_557_);
v_type_558_ = lean_ctor_get(v_p_554_, 2);
lean_inc_ref(v_type_558_);
v_borrow_559_ = lean_ctor_get_uint8(v_p_554_, sizeof(void*)*3);
lean_dec_ref(v_p_554_);
v___x_560_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_557_, v_a_555_);
v_a_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_574_ == 0)
{
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_574_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_574_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; uint8_t v___y_567_; 
v___x_565_ = l_Lean_IR_toIRType(v_type_558_);
lean_dec_ref(v_type_558_);
if (v_borrow_559_ == 0)
{
v___y_567_ = v_borrow_559_;
goto v___jp_566_;
}
else
{
uint8_t v___x_572_; 
v___x_572_ = l_Lean_IR_IRType_isScalar(v___x_565_);
if (v___x_572_ == 0)
{
v___y_567_ = v_borrow_559_;
goto v___jp_566_;
}
else
{
uint8_t v___x_573_; 
v___x_573_ = 0;
v___y_567_ = v___x_573_;
goto v___jp_566_;
}
}
v___jp_566_:
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_568_, 0, v_a_561_);
lean_ctor_set(v___x_568_, 1, v___x_565_);
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*2, v___y_567_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_568_);
v___x_570_ = v___x_563_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg___boxed(lean_object* v_p_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_575_, v_a_576_);
lean_dec(v_a_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object* v_p_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_579_, v_a_580_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object* v_p_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_IR_ToIR_lowerParam(v_p_585_, v_a_586_, v_a_587_, v_a_588_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
lean_dec(v_a_586_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCtorInfo(lean_object* v_i_591_){
_start:
{
lean_object* v_name_592_; lean_object* v_cidx_593_; lean_object* v_size_594_; lean_object* v_usize_595_; lean_object* v_ssize_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
v_name_592_ = lean_ctor_get(v_i_591_, 0);
v_cidx_593_ = lean_ctor_get(v_i_591_, 1);
v_size_594_ = lean_ctor_get(v_i_591_, 2);
v_usize_595_ = lean_ctor_get(v_i_591_, 3);
v_ssize_596_ = lean_ctor_get(v_i_591_, 4);
v_isSharedCheck_603_ = !lean_is_exclusive(v_i_591_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v_i_591_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_ssize_596_);
lean_inc(v_usize_595_);
lean_inc(v_size_594_);
lean_inc(v_cidx_593_);
lean_inc(v_name_592_);
lean_dec(v_i_591_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_name_592_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_cidx_593_);
lean_ctor_set(v_reuseFailAlloc_602_, 2, v_size_594_);
lean_ctor_set(v_reuseFailAlloc_602_, 3, v_usize_595_);
lean_ctor_set(v_reuseFailAlloc_602_, 4, v_ssize_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0(void){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_instMonadEIO___redArg();
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(lean_object* v_msg_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v_toApplicative_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_646_; 
v___x_612_ = lean_obj_once(&l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0, &l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0_once, _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0);
v___x_613_ = l_StateRefT_x27_instMonad___redArg(v___x_612_);
v_toApplicative_614_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_646_ == 0)
{
lean_object* v_unused_647_; 
v_unused_647_ = lean_ctor_get(v___x_613_, 1);
lean_dec(v_unused_647_);
v___x_616_ = v___x_613_;
v_isShared_617_ = v_isSharedCheck_646_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_toApplicative_614_);
lean_dec(v___x_613_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_646_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v_toFunctor_618_; lean_object* v_toSeq_619_; lean_object* v_toSeqLeft_620_; lean_object* v_toSeqRight_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_644_; 
v_toFunctor_618_ = lean_ctor_get(v_toApplicative_614_, 0);
v_toSeq_619_ = lean_ctor_get(v_toApplicative_614_, 2);
v_toSeqLeft_620_ = lean_ctor_get(v_toApplicative_614_, 3);
v_toSeqRight_621_ = lean_ctor_get(v_toApplicative_614_, 4);
v_isSharedCheck_644_ = !lean_is_exclusive(v_toApplicative_614_);
if (v_isSharedCheck_644_ == 0)
{
lean_object* v_unused_645_; 
v_unused_645_ = lean_ctor_get(v_toApplicative_614_, 1);
lean_dec(v_unused_645_);
v___x_623_ = v_toApplicative_614_;
v_isShared_624_ = v_isSharedCheck_644_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_toSeqRight_621_);
lean_inc(v_toSeqLeft_620_);
lean_inc(v_toSeq_619_);
lean_inc(v_toFunctor_618_);
lean_dec(v_toApplicative_614_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_644_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___f_625_; lean_object* v___f_626_; lean_object* v___f_627_; lean_object* v___f_628_; lean_object* v___x_629_; lean_object* v___f_630_; lean_object* v___f_631_; lean_object* v___f_632_; lean_object* v___x_634_; 
v___f_625_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1));
v___f_626_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2));
lean_inc_ref(v_toFunctor_618_);
v___f_627_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_627_, 0, v_toFunctor_618_);
v___f_628_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_628_, 0, v_toFunctor_618_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___f_627_);
lean_ctor_set(v___x_629_, 1, v___f_628_);
v___f_630_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_630_, 0, v_toSeqRight_621_);
v___f_631_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_631_, 0, v_toSeqLeft_620_);
v___f_632_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_632_, 0, v_toSeq_619_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 4, v___f_630_);
lean_ctor_set(v___x_623_, 3, v___f_631_);
lean_ctor_set(v___x_623_, 2, v___f_632_);
lean_ctor_set(v___x_623_, 1, v___f_625_);
lean_ctor_set(v___x_623_, 0, v___x_629_);
v___x_634_ = v___x_623_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___f_625_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v___f_632_);
lean_ctor_set(v_reuseFailAlloc_643_, 3, v___f_631_);
lean_ctor_set(v_reuseFailAlloc_643_, 4, v___f_630_);
v___x_634_ = v_reuseFailAlloc_643_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_636_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 1, v___f_626_);
lean_ctor_set(v___x_616_, 0, v___x_634_);
v___x_636_ = v___x_616_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v___f_626_);
v___x_636_ = v_reuseFailAlloc_642_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_7937__overap_640_; lean_object* v___x_641_; 
v___x_637_ = l_StateRefT_x27_instMonad___redArg(v___x_636_);
v___x_638_ = l_Lean_IR_instInhabitedFnBody_default__1;
v___x_639_ = l_instInhabitedOfMonad___redArg(v___x_637_, v___x_638_);
v___x_7937__overap_640_ = lean_panic_fn_borrowed(v___x_639_, v_msg_607_);
lean_dec(v___x_639_);
lean_inc(v___y_610_);
lean_inc_ref(v___y_609_);
lean_inc(v___y_608_);
v___x_641_ = lean_apply_4(v___x_7937__overap_640_, v___y_608_, v___y_609_, v___y_610_, lean_box(0));
return v___x_641_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object* v_msg_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v_msg_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(size_t v_sz_654_, size_t v_i_655_, lean_object* v_bs_656_, lean_object* v___y_657_){
_start:
{
uint8_t v___x_659_; 
v___x_659_ = lean_usize_dec_lt(v_i_655_, v_sz_654_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v_bs_656_);
return v___x_660_;
}
else
{
lean_object* v_v_661_; lean_object* v___x_662_; lean_object* v_bs_x27_663_; lean_object* v___x_664_; 
v_v_661_ = lean_array_uget(v_bs_656_, v_i_655_);
v___x_662_ = lean_unsigned_to_nat(0u);
v_bs_x27_663_ = lean_array_uset(v_bs_656_, v_i_655_, v___x_662_);
v___x_664_ = l_Lean_IR_ToIR_lowerArg___redArg(v_v_661_, v___y_657_);
lean_dec(v_v_661_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; size_t v___x_666_; size_t v___x_667_; lean_object* v___x_668_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref_known(v___x_664_, 1);
v___x_666_ = ((size_t)1ULL);
v___x_667_ = lean_usize_add(v_i_655_, v___x_666_);
v___x_668_ = lean_array_uset(v_bs_x27_663_, v_i_655_, v_a_665_);
v_i_655_ = v___x_667_;
v_bs_656_ = v___x_668_;
goto _start;
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v_bs_x27_663_);
v_a_670_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_664_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_664_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object* v_sz_678_, lean_object* v_i_679_, lean_object* v_bs_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
size_t v_sz_boxed_683_; size_t v_i_boxed_684_; lean_object* v_res_685_; 
v_sz_boxed_683_ = lean_unbox_usize(v_sz_678_);
lean_dec(v_sz_678_);
v_i_boxed_684_ = lean_unbox_usize(v_i_679_);
lean_dec(v_i_679_);
v_res_685_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_boxed_683_, v_i_boxed_684_, v_bs_680_, v___y_681_);
lean_dec(v___y_681_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(size_t v_sz_686_, size_t v_i_687_, lean_object* v_bs_688_, lean_object* v___y_689_){
_start:
{
uint8_t v___x_691_; 
v___x_691_ = lean_usize_dec_lt(v_i_687_, v_sz_686_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; 
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v_bs_688_);
return v___x_692_;
}
else
{
lean_object* v_v_693_; lean_object* v___x_694_; lean_object* v_bs_x27_695_; lean_object* v___x_696_; 
v_v_693_ = lean_array_uget(v_bs_688_, v_i_687_);
v___x_694_ = lean_unsigned_to_nat(0u);
v_bs_x27_695_ = lean_array_uset(v_bs_688_, v_i_687_, v___x_694_);
v___x_696_ = l_Lean_IR_ToIR_lowerParam___redArg(v_v_693_, v___y_689_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; size_t v___x_698_; size_t v___x_699_; lean_object* v___x_700_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_696_, 1);
v___x_698_ = ((size_t)1ULL);
v___x_699_ = lean_usize_add(v_i_687_, v___x_698_);
v___x_700_ = lean_array_uset(v_bs_x27_695_, v_i_687_, v_a_697_);
v_i_687_ = v___x_699_;
v_bs_688_ = v___x_700_;
goto _start;
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec_ref(v_bs_x27_695_);
v_a_702_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_696_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_696_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg___boxed(lean_object* v_sz_710_, lean_object* v_i_711_, lean_object* v_bs_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
size_t v_sz_boxed_715_; size_t v_i_boxed_716_; lean_object* v_res_717_; 
v_sz_boxed_715_ = lean_unbox_usize(v_sz_710_);
lean_dec(v_sz_710_);
v_i_boxed_716_ = lean_unbox_usize(v_i_711_);
lean_dec(v_i_711_);
v_res_717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_boxed_715_, v_i_boxed_716_, v_bs_712_, v___y_713_);
lean_dec(v___y_713_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2(lean_object* v_i_718_, lean_object* v_continueLet_719_, lean_object* v_var_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_725_, 0, v_i_718_);
lean_ctor_set(v___x_725_, 1, v_var_720_);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc(v___y_721_);
v___x_726_ = lean_apply_5(v_continueLet_719_, v___x_725_, v___y_721_, v___y_722_, v___y_723_, lean_box(0));
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2___boxed(lean_object* v_i_727_, lean_object* v_continueLet_728_, lean_object* v_var_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_IR_ToIR_lowerLet___lam__2(v_i_727_, v_continueLet_728_, v_var_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4(lean_object* v_n_735_, lean_object* v_offset_736_, lean_object* v_continueLet_737_, lean_object* v_var_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_743_, 0, v_n_735_);
lean_ctor_set(v___x_743_, 1, v_offset_736_);
lean_ctor_set(v___x_743_, 2, v_var_738_);
lean_inc(v___y_741_);
lean_inc_ref(v___y_740_);
lean_inc(v___y_739_);
v___x_744_ = lean_apply_5(v_continueLet_737_, v___x_743_, v___y_739_, v___y_740_, v___y_741_, lean_box(0));
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4___boxed(lean_object* v_n_745_, lean_object* v_offset_746_, lean_object* v_continueLet_747_, lean_object* v_var_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_IR_ToIR_lowerLet___lam__4(v_n_745_, v_offset_746_, v_continueLet_747_, v_var_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5(lean_object* v_n_754_, lean_object* v_continueLet_755_, lean_object* v_var_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_761_, 0, v_n_754_);
lean_ctor_set(v___x_761_, 1, v_var_756_);
lean_inc(v___y_759_);
lean_inc_ref(v___y_758_);
lean_inc(v___y_757_);
v___x_762_ = lean_apply_5(v_continueLet_755_, v___x_761_, v___y_757_, v___y_758_, v___y_759_, lean_box(0));
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5___boxed(lean_object* v_n_763_, lean_object* v_continueLet_764_, lean_object* v_var_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_IR_ToIR_lowerLet___lam__5(v_n_763_, v_continueLet_764_, v_var_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8(lean_object* v_continueLet_771_, lean_object* v_var_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_777_, 0, v_var_772_);
lean_inc(v___y_775_);
lean_inc_ref(v___y_774_);
lean_inc(v___y_773_);
v___x_778_ = lean_apply_5(v_continueLet_771_, v___x_777_, v___y_773_, v___y_774_, v___y_775_, lean_box(0));
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8___boxed(lean_object* v_continueLet_779_, lean_object* v_var_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_IR_ToIR_lowerLet___lam__8(v_continueLet_779_, v_var_780_, v___y_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3(lean_object* v_i_786_, lean_object* v_continueLet_787_, lean_object* v_var_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_793_, 0, v_i_786_);
lean_ctor_set(v___x_793_, 1, v_var_788_);
lean_inc(v___y_791_);
lean_inc_ref(v___y_790_);
lean_inc(v___y_789_);
v___x_794_ = lean_apply_5(v_continueLet_787_, v___x_793_, v___y_789_, v___y_790_, v___y_791_, lean_box(0));
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3___boxed(lean_object* v_i_795_, lean_object* v_continueLet_796_, lean_object* v_var_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_IR_ToIR_lowerLet___lam__3(v_i_795_, v_continueLet_796_, v_var_797_, v___y_798_, v___y_799_, v___y_800_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7(lean_object* v_ty_803_, lean_object* v_continueLet_804_, lean_object* v_var_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_810_ = l_Lean_IR_toIRType(v_ty_803_);
v___x_811_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v_var_805_);
lean_inc(v___y_808_);
lean_inc_ref(v___y_807_);
lean_inc(v___y_806_);
v___x_812_ = lean_apply_5(v_continueLet_804_, v___x_811_, v___y_806_, v___y_807_, v___y_808_, lean_box(0));
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7___boxed(lean_object* v_ty_813_, lean_object* v_continueLet_814_, lean_object* v_var_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_IR_ToIR_lowerLet___lam__7(v_ty_813_, v_continueLet_814_, v_var_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v_ty_813_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6(lean_object* v_args_821_, lean_object* v_i_822_, uint8_t v_updateHeader_823_, lean_object* v_continueLet_824_, lean_object* v_var_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
size_t v_sz_830_; size_t v___x_831_; lean_object* v___x_832_; 
v_sz_830_ = lean_array_size(v_args_821_);
v___x_831_ = ((size_t)0ULL);
v___x_832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_830_, v___x_831_, v_args_821_, v___y_826_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v_name_834_; lean_object* v_cidx_835_; lean_object* v_size_836_; lean_object* v_usize_837_; lean_object* v_ssize_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_847_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_832_, 1);
v_name_834_ = lean_ctor_get(v_i_822_, 0);
v_cidx_835_ = lean_ctor_get(v_i_822_, 1);
v_size_836_ = lean_ctor_get(v_i_822_, 2);
v_usize_837_ = lean_ctor_get(v_i_822_, 3);
v_ssize_838_ = lean_ctor_get(v_i_822_, 4);
v_isSharedCheck_847_ = !lean_is_exclusive(v_i_822_);
if (v_isSharedCheck_847_ == 0)
{
v___x_840_ = v_i_822_;
v_isShared_841_ = v_isSharedCheck_847_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_ssize_838_);
lean_inc(v_usize_837_);
lean_inc(v_size_836_);
lean_inc(v_cidx_835_);
lean_inc(v_name_834_);
lean_dec(v_i_822_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_847_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_name_834_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_cidx_835_);
lean_ctor_set(v_reuseFailAlloc_846_, 2, v_size_836_);
lean_ctor_set(v_reuseFailAlloc_846_, 3, v_usize_837_);
lean_ctor_set(v_reuseFailAlloc_846_, 4, v_ssize_838_);
v___x_843_ = v_reuseFailAlloc_846_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v___x_844_, 0, v_var_825_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
lean_ctor_set(v___x_844_, 2, v_a_833_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*3, v_updateHeader_823_);
lean_inc(v___y_828_);
lean_inc_ref(v___y_827_);
lean_inc(v___y_826_);
v___x_845_ = lean_apply_5(v_continueLet_824_, v___x_844_, v___y_826_, v___y_827_, v___y_828_, lean_box(0));
return v___x_845_;
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec(v_var_825_);
lean_dec_ref(v_continueLet_824_);
lean_dec_ref(v_i_822_);
v_a_848_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_832_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_832_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6___boxed(lean_object* v_args_856_, lean_object* v_i_857_, lean_object* v_updateHeader_858_, lean_object* v_continueLet_859_, lean_object* v_var_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
uint8_t v_updateHeader_8994__boxed_865_; lean_object* v_res_866_; 
v_updateHeader_8994__boxed_865_ = lean_unbox(v_updateHeader_858_);
v_res_866_ = l_Lean_IR_ToIR_lowerLet___lam__6(v_args_856_, v_i_857_, v_updateHeader_8994__boxed_865_, v_continueLet_859_, v_var_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9(lean_object* v_continueLet_867_, lean_object* v_var_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_873_, 0, v_var_868_);
lean_inc(v___y_871_);
lean_inc_ref(v___y_870_);
lean_inc(v___y_869_);
v___x_874_ = lean_apply_5(v_continueLet_867_, v___x_873_, v___y_869_, v___y_870_, v___y_871_, lean_box(0));
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9___boxed(lean_object* v_continueLet_875_, lean_object* v_var_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_IR_ToIR_lowerLet___lam__9(v_continueLet_875_, v_var_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1(lean_object* v_args_882_, lean_object* v_continueLet_883_, lean_object* v_id_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
size_t v_sz_889_; size_t v___x_890_; lean_object* v___x_891_; 
v_sz_889_ = lean_array_size(v_args_882_);
v___x_890_ = ((size_t)0ULL);
v___x_891_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_889_, v___x_890_, v_args_882_, v___y_885_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v___x_891_, 1);
v___x_893_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_893_, 0, v_id_884_);
lean_ctor_set(v___x_893_, 1, v_a_892_);
lean_inc(v___y_887_);
lean_inc_ref(v___y_886_);
lean_inc(v___y_885_);
v___x_894_ = lean_apply_5(v_continueLet_883_, v___x_893_, v___y_885_, v___y_886_, v___y_887_, lean_box(0));
return v___x_894_;
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec(v_id_884_);
lean_dec_ref(v_continueLet_883_);
v_a_895_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_891_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_891_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1___boxed(lean_object* v_args_903_, lean_object* v_continueLet_904_, lean_object* v_id_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_IR_ToIR_lowerLet___lam__1(v_args_903_, v_continueLet_904_, v_id_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0(lean_object* v_fvarId_911_, lean_object* v_k_912_, lean_object* v_type_913_, lean_object* v_e_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_911_, v___y_915_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_921_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
lean_dec_ref_known(v___x_919_, 1);
v___x_921_ = l_Lean_IR_ToIR_lowerCode(v_k_912_, v___y_915_, v___y_916_, v___y_917_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_930_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_930_ == 0)
{
v___x_924_ = v___x_921_;
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_926_, 0, v_a_920_);
lean_ctor_set(v___x_926_, 1, v_type_913_);
lean_ctor_set(v___x_926_, 2, v_e_914_);
lean_ctor_set(v___x_926_, 3, v_a_922_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_926_);
v___x_928_ = v___x_924_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
else
{
lean_dec(v_a_920_);
lean_dec_ref(v_e_914_);
lean_dec(v_type_913_);
return v___x_921_;
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_dec_ref(v_e_914_);
lean_dec(v_type_913_);
lean_dec_ref(v_k_912_);
v_a_931_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_919_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_919_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object* v_fvarId_939_, lean_object* v_k_940_, lean_object* v_type_941_, lean_object* v_e_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_939_, v_k_940_, v_type_941_, v_e_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(lean_object* v_decl_948_, lean_object* v_k_949_, lean_object* v_fvarId_950_, lean_object* v_f_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_950_, v_a_952_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_956_, 1);
if (lean_obj_tag(v_a_957_) == 0)
{
lean_object* v_id_958_; lean_object* v___x_959_; 
lean_dec_ref(v_k_949_);
lean_dec_ref(v_decl_948_);
v_id_958_ = lean_ctor_get(v_a_957_, 0);
lean_inc(v_id_958_);
lean_dec_ref_known(v_a_957_, 1);
lean_inc(v_a_954_);
lean_inc_ref(v_a_953_);
lean_inc(v_a_952_);
v___x_959_ = lean_apply_5(v_f_951_, v_id_958_, v_a_952_, v_a_953_, v_a_954_, lean_box(0));
return v___x_959_;
}
else
{
lean_object* v___x_960_; 
lean_dec_ref(v_f_951_);
v___x_960_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_948_, v_k_949_, v_a_952_, v_a_953_, v_a_954_);
return v___x_960_;
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
lean_dec_ref(v_f_951_);
lean_dec_ref(v_k_949_);
lean_dec_ref(v_decl_948_);
v_a_961_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_956_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_956_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object* v_decl_969_, lean_object* v_k_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v_fvarId_975_; lean_object* v_type_976_; lean_object* v_value_977_; lean_object* v_type_978_; lean_object* v_continueLet_979_; 
v_fvarId_975_ = lean_ctor_get(v_decl_969_, 0);
v_type_976_ = lean_ctor_get(v_decl_969_, 2);
v_value_977_ = lean_ctor_get(v_decl_969_, 3);
lean_inc(v_value_977_);
v_type_978_ = l_Lean_IR_toIRType(v_type_976_);
lean_inc(v_type_978_);
lean_inc_ref(v_k_970_);
lean_inc(v_fvarId_975_);
v_continueLet_979_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 8, 3);
lean_closure_set(v_continueLet_979_, 0, v_fvarId_975_);
lean_closure_set(v_continueLet_979_, 1, v_k_970_);
lean_closure_set(v_continueLet_979_, 2, v_type_978_);
switch(lean_obj_tag(v_value_977_))
{
case 0:
{
lean_object* v_value_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_990_; 
lean_inc(v_fvarId_975_);
lean_dec_ref(v_continueLet_979_);
lean_dec_ref(v_decl_969_);
v_value_980_ = lean_ctor_get(v_value_977_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v_value_977_);
if (v_isSharedCheck_990_ == 0)
{
v___x_982_ = v_value_977_;
v_isShared_983_ = v_isSharedCheck_990_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_value_980_);
lean_dec(v_value_977_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_990_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v_fst_985_; lean_object* v___x_987_; 
v___x_984_ = l_Lean_IR_ToIR_lowerLitValue(v_value_980_);
v_fst_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_fst_985_);
lean_dec_ref(v___x_984_);
if (v_isShared_983_ == 0)
{
lean_ctor_set_tag(v___x_982_, 11);
lean_ctor_set(v___x_982_, 0, v_fst_985_);
v___x_987_ = v___x_982_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_fst_985_);
v___x_987_ = v_reuseFailAlloc_989_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_975_, v_k_970_, v_type_978_, v___x_987_, v_a_971_, v_a_972_, v_a_973_);
return v___x_988_;
}
}
}
case 1:
{
lean_object* v___x_991_; 
lean_dec_ref(v_continueLet_979_);
lean_dec(v_type_978_);
v___x_991_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_969_, v_k_970_, v_a_971_, v_a_972_, v_a_973_);
return v___x_991_;
}
case 4:
{
lean_object* v_fvarId_992_; lean_object* v_args_993_; lean_object* v___f_994_; lean_object* v___x_995_; 
lean_dec(v_type_978_);
v_fvarId_992_ = lean_ctor_get(v_value_977_, 0);
lean_inc(v_fvarId_992_);
v_args_993_ = lean_ctor_get(v_value_977_, 1);
lean_inc_ref(v_args_993_);
lean_dec_ref_known(v_value_977_, 2);
v___f_994_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__1___boxed), 7, 2);
lean_closure_set(v___f_994_, 0, v_args_993_);
lean_closure_set(v___f_994_, 1, v_continueLet_979_);
v___x_995_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_969_, v_k_970_, v_fvarId_992_, v___f_994_, v_a_971_, v_a_972_, v_a_973_);
lean_dec(v_fvarId_992_);
return v___x_995_;
}
case 5:
{
lean_object* v_i_996_; lean_object* v_args_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1029_; 
lean_inc(v_fvarId_975_);
lean_dec_ref(v_continueLet_979_);
lean_dec_ref(v_decl_969_);
v_i_996_ = lean_ctor_get(v_value_977_, 0);
v_args_997_ = lean_ctor_get(v_value_977_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_value_977_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_999_ = v_value_977_;
v_isShared_1000_ = v_isSharedCheck_1029_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_args_997_);
lean_inc(v_i_996_);
lean_dec(v_value_977_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1029_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
size_t v_sz_1001_; size_t v___x_1002_; lean_object* v___x_1003_; 
v_sz_1001_ = lean_array_size(v_args_997_);
v___x_1002_ = ((size_t)0ULL);
v___x_1003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1001_, v___x_1002_, v_args_997_, v_a_971_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v_name_1005_; lean_object* v_cidx_1006_; lean_object* v_size_1007_; lean_object* v_usize_1008_; lean_object* v_ssize_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1020_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v_name_1005_ = lean_ctor_get(v_i_996_, 0);
v_cidx_1006_ = lean_ctor_get(v_i_996_, 1);
v_size_1007_ = lean_ctor_get(v_i_996_, 2);
v_usize_1008_ = lean_ctor_get(v_i_996_, 3);
v_ssize_1009_ = lean_ctor_get(v_i_996_, 4);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_i_996_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1011_ = v_i_996_;
v_isShared_1012_ = v_isSharedCheck_1020_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_ssize_1009_);
lean_inc(v_usize_1008_);
lean_inc(v_size_1007_);
lean_inc(v_cidx_1006_);
lean_inc(v_name_1005_);
lean_dec(v_i_996_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1020_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_name_1005_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_cidx_1006_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_size_1007_);
lean_ctor_set(v_reuseFailAlloc_1019_, 3, v_usize_1008_);
lean_ctor_set(v_reuseFailAlloc_1019_, 4, v_ssize_1009_);
v___x_1014_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1016_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set_tag(v___x_999_, 0);
lean_ctor_set(v___x_999_, 1, v_a_1004_);
lean_ctor_set(v___x_999_, 0, v___x_1014_);
v___x_1016_ = v___x_999_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_a_1004_);
v___x_1016_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_975_, v_k_970_, v_type_978_, v___x_1016_, v_a_971_, v_a_972_, v_a_973_);
return v___x_1017_;
}
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_del_object(v___x_999_);
lean_dec_ref(v_i_996_);
lean_dec(v_type_978_);
lean_dec(v_fvarId_975_);
lean_dec_ref(v_k_970_);
v_a_1021_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1003_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1003_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
case 6:
{
lean_object* v_i_1030_; lean_object* v_var_1031_; lean_object* v___f_1032_; lean_object* v___x_1033_; 
lean_dec(v_type_978_);
v_i_1030_ = lean_ctor_get(v_value_977_, 0);
lean_inc(v_i_1030_);
v_var_1031_ = lean_ctor_get(v_value_977_, 1);
lean_inc(v_var_1031_);
lean_dec_ref_known(v_value_977_, 2);
v___f_1032_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__2___boxed), 7, 2);
lean_closure_set(v___f_1032_, 0, v_i_1030_);
lean_closure_set(v___f_1032_, 1, v_continueLet_979_);
v___x_1033_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_969_, v_k_970_, v_var_1031_, v___f_1032_, v_a_971_, v_a_972_, v_a_973_);
lean_dec(v_var_1031_);
return v___x_1033_;
}
case 7:
{
lean_object* v_i_1034_; lean_object* v_var_1035_; lean_object* v___f_1036_; lean_object* v___x_1037_; 
lean_dec(v_type_978_);
v_i_1034_ = lean_ctor_get(v_value_977_, 0);
lean_inc(v_i_1034_);
v_var_1035_ = lean_ctor_get(v_value_977_, 1);
lean_inc(v_var_1035_);
lean_dec_ref_known(v_value_977_, 2);
v___f_1036_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__3___boxed), 7, 2);
lean_closure_set(v___f_1036_, 0, v_i_1034_);
lean_closure_set(v___f_1036_, 1, v_continueLet_979_);
v___x_1037_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_969_, v_k_970_, v_var_1035_, v___f_1036_, v_a_971_, v_a_972_, v_a_973_);
lean_dec(v_var_1035_);
return v___x_1037_;
}
case 8:
{
lean_object* v_n_1038_; lean_object* v_offset_1039_; lean_object* v_var_1040_; lean_object* v___f_1041_; lean_object* v___x_1042_; 
lean_dec(v_type_978_);
v_n_1038_ = lean_ctor_get(v_value_977_, 0);
lean_inc(v_n_1038_);
v_offset_1039_ = lean_ctor_get(v_value_977_, 1);
lean_inc(v_offset_1039_);
v_var_1040_ = lean_ctor_get(v_value_977_, 2);
lean_inc(v_var_1040_);
lean_dec_ref_known(v_value_977_, 3);
v___f_1041_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__4___boxed), 8, 3);
lean_closure_set(v___f_1041_, 0, v_n_1038_);
lean_closure_set(v___f_1041_, 1, v_offset_1039_);
lean_closure_set(v___f_1041_, 2, v_continueLet_979_);
v___x_1042_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_969_, v_k_970_, v_var_1040_, v___f_1041_, v_a_971_, v_a_972_, v_a_973_);
lean_dec(v_var_1040_);
return v___x_1042_;
}
case 9:
{
lean_object* v_fn_1043_; lean_object* v_args_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1064_; 
lean_inc(v_fvarId_975_);
lean_dec_ref(v_continueLet_979_);
lean_dec_ref(v_decl_969_);
v_fn_1043_ = lean_ctor_get(v_value_977_, 0);
v_args_1044_ = lean_ctor_get(v_value_977_, 1);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_value_977_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1046_ = v_value_977_;
v_isShared_1047_ = v_isSharedCheck_1064_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_args_1044_);
lean_inc(v_fn_1043_);
lean_dec(v_value_977_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1064_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
size_t v_sz_1048_; size_t v___x_1049_; lean_object* v___x_1050_; 
v_sz_1048_ = lean_array_size(v_args_1044_);
v___x_1049_ = ((size_t)0ULL);
v___x_1050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1048_, v___x_1049_, v_args_1044_, v_a_971_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1053_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 1);
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 6);
lean_ctor_set(v___x_1046_, 1, v_a_1051_);
v___x_1053_ = v___x_1046_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_fn_1043_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_a_1051_);
v___x_1053_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_975_, v_k_970_, v_type_978_, v___x_1053_, v_a_971_, v_a_972_, v_a_973_);
return v___x_1054_;
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_del_object(v___x_1046_);
lean_dec(v_fn_1043_);
lean_dec(v_type_978_);
lean_dec(v_fvarId_975_);
lean_dec_ref(v_k_970_);
v_a_1056_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1050_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1050_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
case 10:
{
lean_object* v_fn_1065_; lean_object* v_args_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1086_; 
lean_inc(v_fvarId_975_);
lean_dec_ref(v_continueLet_979_);
lean_dec_ref(v_decl_969_);
v_fn_1065_ = lean_ctor_get(v_value_977_, 0);
v_args_1066_ = lean_ctor_get(v_value_977_, 1);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_value_977_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1068_ = v_value_977_;
v_isShared_1069_ = v_isSharedCheck_1086_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_args_1066_);
lean_inc(v_fn_1065_);
lean_dec(v_value_977_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1086_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
size_t v_sz_1070_; size_t v___x_1071_; lean_object* v___x_1072_; 
v_sz_1070_ = lean_array_size(v_args_1066_);
v___x_1071_ = ((size_t)0ULL);
v___x_1072_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1070_, v___x_1071_, v_args_1066_, v_a_971_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1075_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
if (v_isShared_1069_ == 0)
{
lean_ctor_set_tag(v___x_1068_, 7);
lean_ctor_set(v___x_1068_, 1, v_a_1073_);
v___x_1075_ = v___x_1068_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_fn_1065_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_a_1073_);
v___x_1075_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_975_, v_k_970_, v_type_978_, v___x_1075_, v_a_971_, v_a_972_, v_a_973_);
return v___x_1076_;
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_del_object(v___x_1068_);
lean_dec(v_fn_1065_);
lean_dec(v_type_978_);
lean_dec(v_fvarId_975_);
lean_dec_ref(v_k_970_);
v_a_1078_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1072_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1072_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
case 11:
{
lean_object* v_n_1087_; lean_object* v_var_1088_; lean_object* v___f_1089_; lean_object* v___x_1090_; 
lean_dec(v_type_978_);
v_n_1087_ = lean_ctor_get(v_value_977_, 0);
lean_inc(v_n_1087_);
v_var_1088_ = lean_ctor_get(v_value_977_, 1);
lean_inc(v_var_1088_);
lean_dec_ref_known(v_value_977_, 2);
v___f_1089_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__5___boxed), 7, 2);
lean_closure_set(v___f_1089_, 0, v_n_1087_);
lean_closure_set(v___f_1089_, 1, v_continueLet_979_);
v___x_1090_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_969_, v_k_970_, v_var_1088_, v___f_1089_, v_a_971_, v_a_972_, v_a_973_);
lean_dec(v_var_1088_);
return v___x_1090_;
}
case 12:
{
lean_object* v_var_1091_; lean_object* v_i_1092_; uint8_t v_updateHeader_1093_; lean_object* v_args_1094_; lean_object* v___x_1095_; lean_object* v___f_1096_; lean_object* v___x_1097_; 
lean_dec(v_type_978_);
v_var_1091_ = lean_ctor_get(v_value_977_, 0);
lean_inc(v_var_1091_);
v_i_1092_ = lean_ctor_get(v_value_977_, 1);
lean_inc_ref(v_i_1092_);
v_updateHeader_1093_ = lean_ctor_get_uint8(v_value_977_, sizeof(void*)*3);
v_args_1094_ = lean_ctor_get(v_value_977_, 2);
lean_inc_ref(v_args_1094_);
lean_dec_ref_known(v_value_977_, 3);
v___x_1095_ = lean_box(v_updateHeader_1093_);
v___f_1096_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 9, 4);
lean_closure_set(v___f_1096_, 0, v_args_1094_);
lean_closure_set(v___f_1096_, 1, v_i_1092_);
lean_closure_set(v___f_1096_, 2, v___x_1095_);
lean_closure_set(v___f_1096_, 3, v_continueLet_979_);
v___x_1097_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_969_, v_k_970_, v_var_1091_, v___f_1096_, v_a_971_, v_a_972_, v_a_973_);
lean_dec(v_var_1091_);
return v___x_1097_;
}
case 13:
{
lean_object* v_ty_1098_; lean_object* v_fvarId_1099_; lean_object* v___f_1100_; lean_object* v___x_1101_; 
lean_dec(v_type_978_);
v_ty_1098_ = lean_ctor_get(v_value_977_, 0);
lean_inc_ref(v_ty_1098_);
v_fvarId_1099_ = lean_ctor_get(v_value_977_, 1);
lean_inc(v_fvarId_1099_);
lean_dec_ref_known(v_value_977_, 2);
v___f_1100_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__7___boxed), 7, 2);
lean_closure_set(v___f_1100_, 0, v_ty_1098_);
lean_closure_set(v___f_1100_, 1, v_continueLet_979_);
v___x_1101_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_969_, v_k_970_, v_fvarId_1099_, v___f_1100_, v_a_971_, v_a_972_, v_a_973_);
lean_dec(v_fvarId_1099_);
return v___x_1101_;
}
case 14:
{
lean_object* v_fvarId_1102_; lean_object* v___f_1103_; lean_object* v___x_1104_; 
lean_dec(v_type_978_);
v_fvarId_1102_ = lean_ctor_get(v_value_977_, 0);
lean_inc(v_fvarId_1102_);
lean_dec_ref_known(v_value_977_, 1);
v___f_1103_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__8___boxed), 6, 1);
lean_closure_set(v___f_1103_, 0, v_continueLet_979_);
v___x_1104_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_969_, v_k_970_, v_fvarId_1102_, v___f_1103_, v_a_971_, v_a_972_, v_a_973_);
lean_dec(v_fvarId_1102_);
return v___x_1104_;
}
default: 
{
lean_object* v_fvarId_1105_; lean_object* v___f_1106_; lean_object* v___x_1107_; 
lean_dec(v_type_978_);
v_fvarId_1105_ = lean_ctor_get(v_value_977_, 0);
lean_inc(v_fvarId_1105_);
lean_dec_ref_known(v_value_977_, 1);
v___f_1106_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__9___boxed), 6, 1);
lean_closure_set(v___f_1106_, 0, v_continueLet_979_);
v___x_1107_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_969_, v_k_970_, v_fvarId_1105_, v___f_1106_, v_a_971_, v_a_972_, v_a_973_);
lean_dec(v_fvarId_1105_);
return v___x_1107_;
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__3(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1111_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__2));
v___x_1112_ = lean_unsigned_to_nat(15u);
v___x_1113_ = lean_unsigned_to_nat(129u);
v___x_1114_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1115_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1116_ = l_mkPanicMessageWithDecl(v___x_1115_, v___x_1114_, v___x_1113_, v___x_1112_, v___x_1111_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
if (lean_obj_tag(v_a_1117_) == 1)
{
lean_object* v_info_1122_; lean_object* v_code_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1159_; 
v_info_1122_ = lean_ctor_get(v_a_1117_, 0);
v_code_1123_ = lean_ctor_get(v_a_1117_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_a_1117_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1125_ = v_a_1117_;
v_isShared_1126_ = v_isSharedCheck_1159_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_code_1123_);
lean_inc(v_info_1122_);
lean_dec(v_a_1117_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1159_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_IR_ToIR_lowerCode(v_code_1123_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1150_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1150_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1150_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v_name_1132_; lean_object* v_cidx_1133_; lean_object* v_size_1134_; lean_object* v_usize_1135_; lean_object* v_ssize_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1149_; 
v_name_1132_ = lean_ctor_get(v_info_1122_, 0);
v_cidx_1133_ = lean_ctor_get(v_info_1122_, 1);
v_size_1134_ = lean_ctor_get(v_info_1122_, 2);
v_usize_1135_ = lean_ctor_get(v_info_1122_, 3);
v_ssize_1136_ = lean_ctor_get(v_info_1122_, 4);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_info_1122_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1138_ = v_info_1122_;
v_isShared_1139_ = v_isSharedCheck_1149_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_ssize_1136_);
lean_inc(v_usize_1135_);
lean_inc(v_size_1134_);
lean_inc(v_cidx_1133_);
lean_inc(v_name_1132_);
lean_dec(v_info_1122_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1149_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_name_1132_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_cidx_1133_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_size_1134_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_usize_1135_);
lean_ctor_set(v_reuseFailAlloc_1148_, 4, v_ssize_1136_);
v___x_1141_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1143_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 0);
lean_ctor_set(v___x_1125_, 1, v_a_1128_);
lean_ctor_set(v___x_1125_, 0, v___x_1141_);
v___x_1143_ = v___x_1125_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_a_1128_);
v___x_1143_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1145_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1143_);
v___x_1145_ = v___x_1130_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_del_object(v___x_1125_);
lean_dec_ref(v_info_1122_);
v_a_1151_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1127_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1127_);
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
else
{
lean_object* v_code_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1184_; 
v_code_1160_ = lean_ctor_get(v_a_1117_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_a_1117_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1162_ = v_a_1117_;
v_isShared_1163_ = v_isSharedCheck_1184_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_code_1160_);
lean_dec(v_a_1117_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1184_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_IR_ToIR_lowerCode(v_code_1160_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1175_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1175_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1175_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set_tag(v___x_1162_, 1);
lean_ctor_set(v___x_1162_, 0, v_a_1165_);
v___x_1170_ = v___x_1162_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1172_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1170_);
v___x_1172_ = v___x_1167_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_del_object(v___x_1162_);
v_a_1176_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1164_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1164_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(size_t v_sz_1185_, size_t v_i_1186_, lean_object* v_bs_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
uint8_t v___x_1192_; 
v___x_1192_ = lean_usize_dec_lt(v_i_1186_, v_sz_1185_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; 
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v_bs_1187_);
return v___x_1193_;
}
else
{
lean_object* v_v_1194_; lean_object* v___x_1195_; lean_object* v_bs_x27_1196_; lean_object* v___x_1197_; 
v_v_1194_ = lean_array_uget(v_bs_1187_, v_i_1186_);
v___x_1195_ = lean_unsigned_to_nat(0u);
v_bs_x27_1196_ = lean_array_uset(v_bs_1187_, v_i_1186_, v___x_1195_);
v___x_1197_ = l_Lean_IR_ToIR_lowerAlt(v_v_1194_, v___y_1188_, v___y_1189_, v___y_1190_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; size_t v___x_1199_; size_t v___x_1200_; lean_object* v___x_1201_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1198_);
lean_dec_ref_known(v___x_1197_, 1);
v___x_1199_ = ((size_t)1ULL);
v___x_1200_ = lean_usize_add(v_i_1186_, v___x_1199_);
v___x_1201_ = lean_array_uset(v_bs_x27_1196_, v_i_1186_, v_a_1198_);
v_i_1186_ = v___x_1200_;
v_bs_1187_ = v___x_1201_;
goto _start;
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec_ref(v_bs_x27_1196_);
v_a_1203_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1197_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1197_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__5(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1212_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1213_ = lean_unsigned_to_nat(53u);
v___x_1214_ = lean_unsigned_to_nat(96u);
v___x_1215_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1216_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1217_ = l_mkPanicMessageWithDecl(v___x_1216_, v___x_1215_, v___x_1214_, v___x_1213_, v___x_1212_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__6(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1218_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1219_ = lean_unsigned_to_nat(44u);
v___x_1220_ = lean_unsigned_to_nat(107u);
v___x_1221_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1222_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1223_ = l_mkPanicMessageWithDecl(v___x_1222_, v___x_1221_, v___x_1220_, v___x_1219_, v___x_1218_);
return v___x_1223_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__7(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1224_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1225_ = lean_unsigned_to_nat(44u);
v___x_1226_ = lean_unsigned_to_nat(115u);
v___x_1227_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1228_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1229_ = l_mkPanicMessageWithDecl(v___x_1228_, v___x_1227_, v___x_1226_, v___x_1225_, v___x_1224_);
return v___x_1229_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__8(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1230_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1231_ = lean_unsigned_to_nat(34u);
v___x_1232_ = lean_unsigned_to_nat(114u);
v___x_1233_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1234_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1235_ = l_mkPanicMessageWithDecl(v___x_1234_, v___x_1233_, v___x_1232_, v___x_1231_, v___x_1230_);
return v___x_1235_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__9(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1236_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1237_ = lean_unsigned_to_nat(44u);
v___x_1238_ = lean_unsigned_to_nat(111u);
v___x_1239_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1240_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1241_ = l_mkPanicMessageWithDecl(v___x_1240_, v___x_1239_, v___x_1238_, v___x_1237_, v___x_1236_);
return v___x_1241_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__10(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1242_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1243_ = lean_unsigned_to_nat(34u);
v___x_1244_ = lean_unsigned_to_nat(110u);
v___x_1245_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1246_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1247_ = l_mkPanicMessageWithDecl(v___x_1246_, v___x_1245_, v___x_1244_, v___x_1243_, v___x_1242_);
return v___x_1247_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__11(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1248_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1249_ = lean_unsigned_to_nat(41u);
v___x_1250_ = lean_unsigned_to_nat(118u);
v___x_1251_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1252_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1253_ = l_mkPanicMessageWithDecl(v___x_1252_, v___x_1251_, v___x_1250_, v___x_1249_, v___x_1248_);
return v___x_1253_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__12(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1254_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1255_ = lean_unsigned_to_nat(41u);
v___x_1256_ = lean_unsigned_to_nat(121u);
v___x_1257_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1258_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1259_ = l_mkPanicMessageWithDecl(v___x_1258_, v___x_1257_, v___x_1256_, v___x_1255_, v___x_1254_);
return v___x_1259_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__13(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1260_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1261_ = lean_unsigned_to_nat(41u);
v___x_1262_ = lean_unsigned_to_nat(124u);
v___x_1263_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1264_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1265_ = l_mkPanicMessageWithDecl(v___x_1264_, v___x_1263_, v___x_1262_, v___x_1261_, v___x_1260_);
return v___x_1265_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__14(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1266_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1267_ = lean_unsigned_to_nat(41u);
v___x_1268_ = lean_unsigned_to_nat(127u);
v___x_1269_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1270_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1271_ = l_mkPanicMessageWithDecl(v___x_1270_, v___x_1269_, v___x_1268_, v___x_1267_, v___x_1266_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object* v_c_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
switch(lean_obj_tag(v_c_1272_))
{
case 0:
{
lean_object* v_decl_1277_; lean_object* v_k_1278_; lean_object* v___x_1279_; 
v_decl_1277_ = lean_ctor_get(v_c_1272_, 0);
lean_inc_ref(v_decl_1277_);
v_k_1278_ = lean_ctor_get(v_c_1272_, 1);
lean_inc_ref(v_k_1278_);
lean_dec_ref_known(v_c_1272_, 2);
v___x_1279_ = l_Lean_IR_ToIR_lowerLet(v_decl_1277_, v_k_1278_, v_a_1273_, v_a_1274_, v_a_1275_);
return v___x_1279_;
}
case 1:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec_ref_known(v_c_1272_, 2);
v___x_1280_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__3, &l_Lean_IR_ToIR_lowerCode___closed__3_once, _init_l_Lean_IR_ToIR_lowerCode___closed__3);
v___x_1281_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1280_, v_a_1273_, v_a_1274_, v_a_1275_);
return v___x_1281_;
}
case 2:
{
lean_object* v_decl_1282_; lean_object* v_k_1283_; lean_object* v_fvarId_1284_; lean_object* v_params_1285_; lean_object* v_value_1286_; lean_object* v___x_1287_; 
v_decl_1282_ = lean_ctor_get(v_c_1272_, 0);
lean_inc_ref(v_decl_1282_);
v_k_1283_ = lean_ctor_get(v_c_1272_, 1);
lean_inc_ref(v_k_1283_);
lean_dec_ref_known(v_c_1272_, 2);
v_fvarId_1284_ = lean_ctor_get(v_decl_1282_, 0);
lean_inc(v_fvarId_1284_);
v_params_1285_ = lean_ctor_get(v_decl_1282_, 2);
lean_inc_ref(v_params_1285_);
v_value_1286_ = lean_ctor_get(v_decl_1282_, 4);
lean_inc_ref(v_value_1286_);
lean_dec_ref(v_decl_1282_);
v___x_1287_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_1284_, v_a_1273_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; size_t v_sz_1289_; size_t v___x_1290_; lean_object* v___x_1291_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
v_sz_1289_ = lean_array_size(v_params_1285_);
v___x_1290_ = ((size_t)0ULL);
v___x_1291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1289_, v___x_1290_, v_params_1285_, v_a_1273_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1293_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_a_1292_);
lean_dec_ref_known(v___x_1291_, 1);
v___x_1293_ = l_Lean_IR_ToIR_lowerCode(v_value_1286_, v_a_1273_, v_a_1274_, v_a_1275_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1295_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1293_, 1);
v___x_1295_ = l_Lean_IR_ToIR_lowerCode(v_k_1283_, v_a_1273_, v_a_1274_, v_a_1275_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1304_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1304_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1304_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; lean_object* v___x_1302_; 
v___x_1300_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1300_, 0, v_a_1288_);
lean_ctor_set(v___x_1300_, 1, v_a_1292_);
lean_ctor_set(v___x_1300_, 2, v_a_1294_);
lean_ctor_set(v___x_1300_, 3, v_a_1296_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1300_);
v___x_1302_ = v___x_1298_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
else
{
lean_dec(v_a_1294_);
lean_dec(v_a_1292_);
lean_dec(v_a_1288_);
return v___x_1295_;
}
}
else
{
lean_dec(v_a_1292_);
lean_dec(v_a_1288_);
lean_dec_ref(v_k_1283_);
return v___x_1293_;
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_dec(v_a_1288_);
lean_dec_ref(v_value_1286_);
lean_dec_ref(v_k_1283_);
v_a_1305_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1291_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1291_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec_ref(v_value_1286_);
lean_dec_ref(v_params_1285_);
lean_dec_ref(v_k_1283_);
v_a_1313_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1287_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1287_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_1321_; lean_object* v_args_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1358_; 
v_fvarId_1321_ = lean_ctor_get(v_c_1272_, 0);
v_args_1322_ = lean_ctor_get(v_c_1272_, 1);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_c_1272_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1324_ = v_c_1272_;
v_isShared_1325_ = v_isSharedCheck_1358_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_args_1322_);
lean_inc(v_fvarId_1321_);
lean_dec(v_c_1272_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1358_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_1321_, v_a_1273_);
lean_dec(v_fvarId_1321_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; size_t v_sz_1328_; size_t v___x_1329_; lean_object* v___x_1330_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1326_, 1);
v_sz_1328_ = lean_array_size(v_args_1322_);
v___x_1329_ = ((size_t)0ULL);
v___x_1330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1328_, v___x_1329_, v_args_1322_, v_a_1273_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1341_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1341_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1341_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1325_ == 0)
{
lean_ctor_set_tag(v___x_1324_, 11);
lean_ctor_set(v___x_1324_, 1, v_a_1331_);
lean_ctor_set(v___x_1324_, 0, v_a_1327_);
v___x_1336_ = v___x_1324_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1327_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1338_; 
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1336_);
v___x_1338_ = v___x_1333_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec(v_a_1327_);
lean_del_object(v___x_1324_);
v_a_1342_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1330_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1330_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_del_object(v___x_1324_);
lean_dec_ref(v_args_1322_);
v_a_1350_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1326_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1326_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
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
}
case 4:
{
lean_object* v_cases_1359_; lean_object* v_typeName_1360_; lean_object* v_discr_1361_; lean_object* v_alts_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1402_; 
v_cases_1359_ = lean_ctor_get(v_c_1272_, 0);
lean_inc_ref(v_cases_1359_);
lean_dec_ref_known(v_c_1272_, 1);
v_typeName_1360_ = lean_ctor_get(v_cases_1359_, 0);
v_discr_1361_ = lean_ctor_get(v_cases_1359_, 2);
v_alts_1362_ = lean_ctor_get(v_cases_1359_, 3);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_cases_1359_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; 
v_unused_1403_ = lean_ctor_get(v_cases_1359_, 1);
lean_dec(v_unused_1403_);
v___x_1364_ = v_cases_1359_;
v_isShared_1365_ = v_isSharedCheck_1402_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_alts_1362_);
lean_inc(v_discr_1361_);
lean_inc(v_typeName_1360_);
lean_dec(v_cases_1359_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1402_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_discr_1361_, v_a_1273_);
lean_dec(v_discr_1361_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1366_, 1);
if (lean_obj_tag(v_a_1367_) == 0)
{
lean_object* v_id_1368_; size_t v_sz_1369_; size_t v___x_1370_; lean_object* v___x_1371_; 
v_id_1368_ = lean_ctor_get(v_a_1367_, 0);
lean_inc(v_id_1368_);
lean_dec_ref_known(v_a_1367_, 1);
v_sz_1369_ = lean_array_size(v_alts_1362_);
v___x_1370_ = ((size_t)0ULL);
v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_1369_, v___x_1370_, v_alts_1362_, v_a_1273_, v_a_1274_, v_a_1275_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1383_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1374_ = v___x_1371_;
v_isShared_1375_ = v_isSharedCheck_1383_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1371_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1383_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1376_ = l_Lean_IR_nameToIRType(v_typeName_1360_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set_tag(v___x_1364_, 9);
lean_ctor_set(v___x_1364_, 3, v_a_1372_);
lean_ctor_set(v___x_1364_, 2, v___x_1376_);
lean_ctor_set(v___x_1364_, 1, v_id_1368_);
v___x_1378_ = v___x_1364_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_typeName_1360_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_id_1368_);
lean_ctor_set(v_reuseFailAlloc_1382_, 2, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1382_, 3, v_a_1372_);
v___x_1378_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_object* v___x_1380_; 
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v___x_1378_);
v___x_1380_ = v___x_1374_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec(v_id_1368_);
lean_del_object(v___x_1364_);
lean_dec(v_typeName_1360_);
v_a_1384_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1371_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1371_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_dec(v_a_1367_);
lean_del_object(v___x_1364_);
lean_dec_ref(v_alts_1362_);
lean_dec(v_typeName_1360_);
v___x_1392_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__5, &l_Lean_IR_ToIR_lowerCode___closed__5_once, _init_l_Lean_IR_ToIR_lowerCode___closed__5);
v___x_1393_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1392_, v_a_1273_, v_a_1274_, v_a_1275_);
return v___x_1393_;
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_del_object(v___x_1364_);
lean_dec_ref(v_alts_1362_);
lean_dec(v_typeName_1360_);
v_a_1394_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1366_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1366_);
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
case 5:
{
lean_object* v_fvarId_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1428_; 
v_fvarId_1404_ = lean_ctor_get(v_c_1272_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_c_1272_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1406_ = v_c_1272_;
v_isShared_1407_ = v_isSharedCheck_1428_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_fvarId_1404_);
lean_dec(v_c_1272_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1428_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1404_, v_a_1273_);
lean_dec(v_fvarId_1404_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1419_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1419_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1419_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1407_ == 0)
{
lean_ctor_set_tag(v___x_1406_, 10);
lean_ctor_set(v___x_1406_, 0, v_a_1409_);
v___x_1414_ = v___x_1406_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1416_; 
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v___x_1414_);
v___x_1416_ = v___x_1411_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_del_object(v___x_1406_);
v_a_1420_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1408_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1408_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
case 6:
{
lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1436_; 
v_isSharedCheck_1436_ = !lean_is_exclusive(v_c_1272_);
if (v_isSharedCheck_1436_ == 0)
{
lean_object* v_unused_1437_; 
v_unused_1437_ = lean_ctor_get(v_c_1272_, 0);
lean_dec(v_unused_1437_);
v___x_1430_ = v_c_1272_;
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
else
{
lean_dec(v_c_1272_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = lean_box(12);
if (v_isShared_1431_ == 0)
{
lean_ctor_set_tag(v___x_1430_, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1432_);
v___x_1434_ = v___x_1430_;
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
case 7:
{
lean_object* v_fvarId_1438_; lean_object* v_i_1439_; lean_object* v_y_1440_; lean_object* v_k_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1480_; 
v_fvarId_1438_ = lean_ctor_get(v_c_1272_, 0);
v_i_1439_ = lean_ctor_get(v_c_1272_, 1);
v_y_1440_ = lean_ctor_get(v_c_1272_, 2);
v_k_1441_ = lean_ctor_get(v_c_1272_, 3);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_c_1272_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1443_ = v_c_1272_;
v_isShared_1444_ = v_isSharedCheck_1480_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_k_1441_);
lean_inc(v_y_1440_);
lean_inc(v_i_1439_);
lean_inc(v_fvarId_1438_);
lean_dec(v_c_1272_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1480_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_IR_ToIR_lowerArg___redArg(v_y_1440_, v_a_1273_);
lean_dec(v_y_1440_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v___x_1447_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
lean_dec_ref_known(v___x_1445_, 1);
v___x_1447_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1438_, v_a_1273_);
lean_dec(v_fvarId_1438_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1447_, 1);
if (lean_obj_tag(v_a_1448_) == 0)
{
lean_object* v_id_1449_; lean_object* v___x_1450_; 
v_id_1449_ = lean_ctor_get(v_a_1448_, 0);
lean_inc(v_id_1449_);
lean_dec_ref_known(v_a_1448_, 1);
v___x_1450_ = l_Lean_IR_ToIR_lowerCode(v_k_1441_, v_a_1273_, v_a_1274_, v_a_1275_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1461_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1461_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1461_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set_tag(v___x_1443_, 2);
lean_ctor_set(v___x_1443_, 3, v_a_1451_);
lean_ctor_set(v___x_1443_, 2, v_a_1446_);
lean_ctor_set(v___x_1443_, 0, v_id_1449_);
v___x_1456_ = v___x_1443_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_id_1449_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_i_1439_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v_a_1446_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1458_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1456_);
v___x_1458_ = v___x_1453_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
else
{
lean_dec(v_id_1449_);
lean_dec(v_a_1446_);
lean_del_object(v___x_1443_);
lean_dec(v_i_1439_);
return v___x_1450_;
}
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_dec(v_a_1448_);
lean_dec(v_a_1446_);
lean_del_object(v___x_1443_);
lean_dec_ref(v_k_1441_);
lean_dec(v_i_1439_);
v___x_1462_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__6, &l_Lean_IR_ToIR_lowerCode___closed__6_once, _init_l_Lean_IR_ToIR_lowerCode___closed__6);
v___x_1463_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1462_, v_a_1273_, v_a_1274_, v_a_1275_);
return v___x_1463_;
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec(v_a_1446_);
lean_del_object(v___x_1443_);
lean_dec_ref(v_k_1441_);
lean_dec(v_i_1439_);
v_a_1464_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1447_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1447_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_del_object(v___x_1443_);
lean_dec_ref(v_k_1441_);
lean_dec(v_i_1439_);
lean_dec(v_fvarId_1438_);
v_a_1472_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1445_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1445_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
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
}
case 8:
{
lean_object* v_fvarId_1481_; lean_object* v_i_1482_; lean_object* v_y_1483_; lean_object* v_k_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1526_; 
v_fvarId_1481_ = lean_ctor_get(v_c_1272_, 0);
v_i_1482_ = lean_ctor_get(v_c_1272_, 1);
v_y_1483_ = lean_ctor_get(v_c_1272_, 2);
v_k_1484_ = lean_ctor_get(v_c_1272_, 3);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_c_1272_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1486_ = v_c_1272_;
v_isShared_1487_ = v_isSharedCheck_1526_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_k_1484_);
lean_inc(v_y_1483_);
lean_inc(v_i_1482_);
lean_inc(v_fvarId_1481_);
lean_dec(v_c_1272_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1526_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1483_, v_a_1273_);
lean_dec(v_y_1483_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v___x_1488_, 1);
if (lean_obj_tag(v_a_1489_) == 0)
{
lean_object* v_id_1490_; lean_object* v___x_1491_; 
v_id_1490_ = lean_ctor_get(v_a_1489_, 0);
lean_inc(v_id_1490_);
lean_dec_ref_known(v_a_1489_, 1);
v___x_1491_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1481_, v_a_1273_);
lean_dec(v_fvarId_1481_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1491_, 1);
if (lean_obj_tag(v_a_1492_) == 0)
{
lean_object* v_id_1493_; lean_object* v___x_1494_; 
v_id_1493_ = lean_ctor_get(v_a_1492_, 0);
lean_inc(v_id_1493_);
lean_dec_ref_known(v_a_1492_, 1);
v___x_1494_ = l_Lean_IR_ToIR_lowerCode(v_k_1484_, v_a_1273_, v_a_1274_, v_a_1275_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1505_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1497_ = v___x_1494_;
v_isShared_1498_ = v_isSharedCheck_1505_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1505_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set_tag(v___x_1486_, 4);
lean_ctor_set(v___x_1486_, 3, v_a_1495_);
lean_ctor_set(v___x_1486_, 2, v_id_1490_);
lean_ctor_set(v___x_1486_, 0, v_id_1493_);
v___x_1500_ = v___x_1486_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_id_1493_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_i_1482_);
lean_ctor_set(v_reuseFailAlloc_1504_, 2, v_id_1490_);
lean_ctor_set(v_reuseFailAlloc_1504_, 3, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1502_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1500_);
v___x_1502_ = v___x_1497_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
else
{
lean_dec(v_id_1493_);
lean_dec(v_id_1490_);
lean_del_object(v___x_1486_);
lean_dec(v_i_1482_);
return v___x_1494_;
}
}
else
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec(v_a_1492_);
lean_dec(v_id_1490_);
lean_del_object(v___x_1486_);
lean_dec_ref(v_k_1484_);
lean_dec(v_i_1482_);
v___x_1506_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__7, &l_Lean_IR_ToIR_lowerCode___closed__7_once, _init_l_Lean_IR_ToIR_lowerCode___closed__7);
v___x_1507_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1506_, v_a_1273_, v_a_1274_, v_a_1275_);
return v___x_1507_;
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec(v_id_1490_);
lean_del_object(v___x_1486_);
lean_dec_ref(v_k_1484_);
lean_dec(v_i_1482_);
v_a_1508_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1491_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1491_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
else
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_dec(v_a_1489_);
lean_del_object(v___x_1486_);
lean_dec_ref(v_k_1484_);
lean_dec(v_i_1482_);
lean_dec(v_fvarId_1481_);
v___x_1516_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__8, &l_Lean_IR_ToIR_lowerCode___closed__8_once, _init_l_Lean_IR_ToIR_lowerCode___closed__8);
v___x_1517_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1516_, v_a_1273_, v_a_1274_, v_a_1275_);
return v___x_1517_;
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
lean_del_object(v___x_1486_);
lean_dec_ref(v_k_1484_);
lean_dec(v_i_1482_);
lean_dec(v_fvarId_1481_);
v_a_1518_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1488_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1488_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
case 9:
{
lean_object* v_fvarId_1527_; lean_object* v_i_1528_; lean_object* v_offset_1529_; lean_object* v_y_1530_; lean_object* v_ty_1531_; lean_object* v_k_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1575_; 
v_fvarId_1527_ = lean_ctor_get(v_c_1272_, 0);
v_i_1528_ = lean_ctor_get(v_c_1272_, 1);
v_offset_1529_ = lean_ctor_get(v_c_1272_, 2);
v_y_1530_ = lean_ctor_get(v_c_1272_, 3);
v_ty_1531_ = lean_ctor_get(v_c_1272_, 4);
v_k_1532_ = lean_ctor_get(v_c_1272_, 5);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_c_1272_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1534_ = v_c_1272_;
v_isShared_1535_ = v_isSharedCheck_1575_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_k_1532_);
lean_inc(v_ty_1531_);
lean_inc(v_y_1530_);
lean_inc(v_offset_1529_);
lean_inc(v_i_1528_);
lean_inc(v_fvarId_1527_);
lean_dec(v_c_1272_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1575_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1530_, v_a_1273_);
lean_dec(v_y_1530_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1536_, 1);
if (lean_obj_tag(v_a_1537_) == 0)
{
lean_object* v_id_1538_; lean_object* v___x_1539_; 
v_id_1538_ = lean_ctor_get(v_a_1537_, 0);
lean_inc(v_id_1538_);
lean_dec_ref_known(v_a_1537_, 1);
v___x_1539_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1527_, v_a_1273_);
lean_dec(v_fvarId_1527_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___x_1539_, 1);
if (lean_obj_tag(v_a_1540_) == 0)
{
lean_object* v_id_1541_; lean_object* v___x_1542_; 
v_id_1541_ = lean_ctor_get(v_a_1540_, 0);
lean_inc(v_id_1541_);
lean_dec_ref_known(v_a_1540_, 1);
v___x_1542_ = l_Lean_IR_ToIR_lowerCode(v_k_1532_, v_a_1273_, v_a_1274_, v_a_1275_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1554_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1554_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1554_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1547_ = l_Lean_IR_toIRType(v_ty_1531_);
lean_dec_ref(v_ty_1531_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set_tag(v___x_1534_, 5);
lean_ctor_set(v___x_1534_, 5, v_a_1543_);
lean_ctor_set(v___x_1534_, 4, v___x_1547_);
lean_ctor_set(v___x_1534_, 3, v_id_1538_);
lean_ctor_set(v___x_1534_, 0, v_id_1541_);
v___x_1549_ = v___x_1534_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_id_1541_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_i_1528_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_offset_1529_);
lean_ctor_set(v_reuseFailAlloc_1553_, 3, v_id_1538_);
lean_ctor_set(v_reuseFailAlloc_1553_, 4, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1553_, 5, v_a_1543_);
v___x_1549_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1551_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1549_);
v___x_1551_ = v___x_1545_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
else
{
lean_dec(v_id_1541_);
lean_dec(v_id_1538_);
lean_del_object(v___x_1534_);
lean_dec_ref(v_ty_1531_);
lean_dec(v_offset_1529_);
lean_dec(v_i_1528_);
return v___x_1542_;
}
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
lean_dec(v_a_1540_);
lean_dec(v_id_1538_);
lean_del_object(v___x_1534_);
lean_dec_ref(v_k_1532_);
lean_dec_ref(v_ty_1531_);
lean_dec(v_offset_1529_);
lean_dec(v_i_1528_);
v___x_1555_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__9, &l_Lean_IR_ToIR_lowerCode___closed__9_once, _init_l_Lean_IR_ToIR_lowerCode___closed__9);
v___x_1556_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1555_, v_a_1273_, v_a_1274_, v_a_1275_);
return v___x_1556_;
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec(v_id_1538_);
lean_del_object(v___x_1534_);
lean_dec_ref(v_k_1532_);
lean_dec_ref(v_ty_1531_);
lean_dec(v_offset_1529_);
lean_dec(v_i_1528_);
v_a_1557_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1539_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1539_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_dec(v_a_1537_);
lean_del_object(v___x_1534_);
lean_dec_ref(v_k_1532_);
lean_dec_ref(v_ty_1531_);
lean_dec(v_offset_1529_);
lean_dec(v_i_1528_);
lean_dec(v_fvarId_1527_);
v___x_1565_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__10, &l_Lean_IR_ToIR_lowerCode___closed__10_once, _init_l_Lean_IR_ToIR_lowerCode___closed__10);
v___x_1566_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1565_, v_a_1273_, v_a_1274_, v_a_1275_);
return v___x_1566_;
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_del_object(v___x_1534_);
lean_dec_ref(v_k_1532_);
lean_dec_ref(v_ty_1531_);
lean_dec(v_offset_1529_);
lean_dec(v_i_1528_);
lean_dec(v_fvarId_1527_);
v_a_1567_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1536_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1536_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
}
case 10:
{
lean_object* v_fvarId_1576_; lean_object* v_cidx_1577_; lean_object* v_k_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1607_; 
v_fvarId_1576_ = lean_ctor_get(v_c_1272_, 0);
v_cidx_1577_ = lean_ctor_get(v_c_1272_, 1);
v_k_1578_ = lean_ctor_get(v_c_1272_, 2);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_c_1272_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1580_ = v_c_1272_;
v_isShared_1581_ = v_isSharedCheck_1607_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_k_1578_);
lean_inc(v_cidx_1577_);
lean_inc(v_fvarId_1576_);
lean_dec(v_c_1272_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1607_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1576_, v_a_1273_);
lean_dec(v_fvarId_1576_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
if (lean_obj_tag(v_a_1583_) == 0)
{
lean_object* v_id_1584_; lean_object* v___x_1585_; 
v_id_1584_ = lean_ctor_get(v_a_1583_, 0);
lean_inc(v_id_1584_);
lean_dec_ref_known(v_a_1583_, 1);
v___x_1585_ = l_Lean_IR_ToIR_lowerCode(v_k_1578_, v_a_1273_, v_a_1274_, v_a_1275_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1596_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1588_ = v___x_1585_;
v_isShared_1589_ = v_isSharedCheck_1596_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1596_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1581_ == 0)
{
lean_ctor_set_tag(v___x_1580_, 3);
lean_ctor_set(v___x_1580_, 2, v_a_1586_);
lean_ctor_set(v___x_1580_, 0, v_id_1584_);
v___x_1591_ = v___x_1580_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_id_1584_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_cidx_1577_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1593_; 
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v___x_1591_);
v___x_1593_ = v___x_1588_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
else
{
lean_dec(v_id_1584_);
lean_del_object(v___x_1580_);
lean_dec(v_cidx_1577_);
return v___x_1585_;
}
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_dec(v_a_1583_);
lean_del_object(v___x_1580_);
lean_dec_ref(v_k_1578_);
lean_dec(v_cidx_1577_);
v___x_1597_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__11, &l_Lean_IR_ToIR_lowerCode___closed__11_once, _init_l_Lean_IR_ToIR_lowerCode___closed__11);
v___x_1598_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1597_, v_a_1273_, v_a_1274_, v_a_1275_);
return v___x_1598_;
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_del_object(v___x_1580_);
lean_dec_ref(v_k_1578_);
lean_dec(v_cidx_1577_);
v_a_1599_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1582_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1582_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
case 11:
{
lean_object* v_fvarId_1608_; lean_object* v_n_1609_; uint8_t v_check_1610_; uint8_t v_persistent_1611_; lean_object* v_k_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1641_; 
v_fvarId_1608_ = lean_ctor_get(v_c_1272_, 0);
v_n_1609_ = lean_ctor_get(v_c_1272_, 1);
v_check_1610_ = lean_ctor_get_uint8(v_c_1272_, sizeof(void*)*3);
v_persistent_1611_ = lean_ctor_get_uint8(v_c_1272_, sizeof(void*)*3 + 1);
v_k_1612_ = lean_ctor_get(v_c_1272_, 2);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_c_1272_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1614_ = v_c_1272_;
v_isShared_1615_ = v_isSharedCheck_1641_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_k_1612_);
lean_inc(v_n_1609_);
lean_inc(v_fvarId_1608_);
lean_dec(v_c_1272_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1641_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1608_, v_a_1273_);
lean_dec(v_fvarId_1608_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1616_, 1);
if (lean_obj_tag(v_a_1617_) == 0)
{
lean_object* v_id_1618_; lean_object* v___x_1619_; 
v_id_1618_ = lean_ctor_get(v_a_1617_, 0);
lean_inc(v_id_1618_);
lean_dec_ref_known(v_a_1617_, 1);
v___x_1619_ = l_Lean_IR_ToIR_lowerCode(v_k_1612_, v_a_1273_, v_a_1274_, v_a_1275_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1630_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1622_ = v___x_1619_;
v_isShared_1623_ = v_isSharedCheck_1630_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1619_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1630_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1615_ == 0)
{
lean_ctor_set_tag(v___x_1614_, 6);
lean_ctor_set(v___x_1614_, 2, v_a_1620_);
lean_ctor_set(v___x_1614_, 0, v_id_1618_);
v___x_1625_ = v___x_1614_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_id_1618_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_n_1609_);
lean_ctor_set(v_reuseFailAlloc_1629_, 2, v_a_1620_);
lean_ctor_set_uint8(v_reuseFailAlloc_1629_, sizeof(void*)*3, v_check_1610_);
lean_ctor_set_uint8(v_reuseFailAlloc_1629_, sizeof(void*)*3 + 1, v_persistent_1611_);
v___x_1625_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1627_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v___x_1625_);
v___x_1627_ = v___x_1622_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_dec(v_id_1618_);
lean_del_object(v___x_1614_);
lean_dec(v_n_1609_);
return v___x_1619_;
}
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
lean_dec(v_a_1617_);
lean_del_object(v___x_1614_);
lean_dec_ref(v_k_1612_);
lean_dec(v_n_1609_);
v___x_1631_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__12, &l_Lean_IR_ToIR_lowerCode___closed__12_once, _init_l_Lean_IR_ToIR_lowerCode___closed__12);
v___x_1632_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1631_, v_a_1273_, v_a_1274_, v_a_1275_);
return v___x_1632_;
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_del_object(v___x_1614_);
lean_dec_ref(v_k_1612_);
lean_dec(v_n_1609_);
v_a_1633_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1616_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1616_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
case 12:
{
lean_object* v_fvarId_1642_; lean_object* v_n_1643_; uint8_t v_check_1644_; uint8_t v_persistent_1645_; lean_object* v_k_1646_; lean_object* v___x_1647_; 
v_fvarId_1642_ = lean_ctor_get(v_c_1272_, 0);
lean_inc(v_fvarId_1642_);
v_n_1643_ = lean_ctor_get(v_c_1272_, 1);
lean_inc(v_n_1643_);
v_check_1644_ = lean_ctor_get_uint8(v_c_1272_, sizeof(void*)*4);
v_persistent_1645_ = lean_ctor_get_uint8(v_c_1272_, sizeof(void*)*4 + 1);
v_k_1646_ = lean_ctor_get(v_c_1272_, 3);
lean_inc_ref(v_k_1646_);
lean_dec_ref_known(v_c_1272_, 4);
v___x_1647_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1642_, v_a_1273_);
lean_dec(v_fvarId_1642_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
if (lean_obj_tag(v_a_1648_) == 0)
{
lean_object* v_id_1649_; lean_object* v___x_1650_; 
v_id_1649_ = lean_ctor_get(v_a_1648_, 0);
lean_inc(v_id_1649_);
lean_dec_ref_known(v_a_1648_, 1);
v___x_1650_ = l_Lean_IR_ToIR_lowerCode(v_k_1646_, v_a_1273_, v_a_1274_, v_a_1275_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1659_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1659_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1659_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1655_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v___x_1655_, 0, v_id_1649_);
lean_ctor_set(v___x_1655_, 1, v_n_1643_);
lean_ctor_set(v___x_1655_, 2, v_a_1651_);
lean_ctor_set_uint8(v___x_1655_, sizeof(void*)*3, v_check_1644_);
lean_ctor_set_uint8(v___x_1655_, sizeof(void*)*3 + 1, v_persistent_1645_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1655_);
v___x_1657_ = v___x_1653_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
else
{
lean_dec(v_id_1649_);
lean_dec(v_n_1643_);
return v___x_1650_;
}
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
lean_dec(v_a_1648_);
lean_dec_ref(v_k_1646_);
lean_dec(v_n_1643_);
v___x_1660_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__13, &l_Lean_IR_ToIR_lowerCode___closed__13_once, _init_l_Lean_IR_ToIR_lowerCode___closed__13);
v___x_1661_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1660_, v_a_1273_, v_a_1274_, v_a_1275_);
return v___x_1661_;
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec_ref(v_k_1646_);
lean_dec(v_n_1643_);
v_a_1662_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1647_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1647_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
default: 
{
lean_object* v_fvarId_1670_; lean_object* v_k_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1700_; 
v_fvarId_1670_ = lean_ctor_get(v_c_1272_, 0);
v_k_1671_ = lean_ctor_get(v_c_1272_, 1);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_c_1272_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1673_ = v_c_1272_;
v_isShared_1674_ = v_isSharedCheck_1700_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_k_1671_);
lean_inc(v_fvarId_1670_);
lean_dec(v_c_1272_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1700_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1670_, v_a_1273_);
lean_dec(v_fvarId_1670_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref_known(v___x_1675_, 1);
if (lean_obj_tag(v_a_1676_) == 0)
{
lean_object* v_id_1677_; lean_object* v___x_1678_; 
v_id_1677_ = lean_ctor_get(v_a_1676_, 0);
lean_inc(v_id_1677_);
lean_dec_ref_known(v_a_1676_, 1);
v___x_1678_ = l_Lean_IR_ToIR_lowerCode(v_k_1671_, v_a_1273_, v_a_1274_, v_a_1275_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1689_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1689_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1689_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1674_ == 0)
{
lean_ctor_set_tag(v___x_1673_, 8);
lean_ctor_set(v___x_1673_, 1, v_a_1679_);
lean_ctor_set(v___x_1673_, 0, v_id_1677_);
v___x_1684_ = v___x_1673_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_id_1677_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1686_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v___x_1684_);
v___x_1686_ = v___x_1681_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
else
{
lean_dec(v_id_1677_);
lean_del_object(v___x_1673_);
return v___x_1678_;
}
}
else
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec(v_a_1676_);
lean_del_object(v___x_1673_);
lean_dec_ref(v_k_1671_);
v___x_1690_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__14, &l_Lean_IR_ToIR_lowerCode___closed__14_once, _init_l_Lean_IR_ToIR_lowerCode___closed__14);
v___x_1691_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1690_, v_a_1273_, v_a_1274_, v_a_1275_);
return v___x_1691_;
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_del_object(v___x_1673_);
lean_dec_ref(v_k_1671_);
v_a_1692_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1675_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1675_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object* v_decl_1701_, lean_object* v_k_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v_fvarId_1707_; lean_object* v___x_1708_; 
v_fvarId_1707_ = lean_ctor_get(v_decl_1701_, 0);
lean_inc(v_fvarId_1707_);
lean_dec_ref(v_decl_1701_);
v___x_1708_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_1707_, v_a_1703_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v___x_1709_; 
lean_dec_ref_known(v___x_1708_, 1);
v___x_1709_ = l_Lean_IR_ToIR_lowerCode(v_k_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
return v___x_1709_;
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec_ref(v_k_1702_);
v_a_1710_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1708_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1708_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg___boxed(lean_object* v_decl_1718_, lean_object* v_k_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1718_, v_k_1719_, v_a_1720_, v_a_1721_, v_a_1722_);
lean_dec(v_a_1722_);
lean_dec_ref(v_a_1721_);
lean_dec(v_a_1720_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue___boxed(lean_object* v_decl_1725_, lean_object* v_k_1726_, lean_object* v_fvarId_1727_, lean_object* v_f_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1725_, v_k_1726_, v_fvarId_1727_, v_f_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
lean_dec(v_fvarId_1727_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4___boxed(lean_object* v_sz_1734_, lean_object* v_i_1735_, lean_object* v_bs_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
size_t v_sz_boxed_1741_; size_t v_i_boxed_1742_; lean_object* v_res_1743_; 
v_sz_boxed_1741_ = lean_unbox_usize(v_sz_1734_);
lean_dec(v_sz_1734_);
v_i_boxed_1742_ = lean_unbox_usize(v_i_1735_);
lean_dec(v_i_1735_);
v_res_1743_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_boxed_1741_, v_i_boxed_1742_, v_bs_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt___boxed(lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_IR_ToIR_lowerAlt(v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___boxed(lean_object* v_decl_1750_, lean_object* v_k_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_IR_ToIR_lowerLet(v_decl_1750_, v_k_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
lean_dec(v_a_1752_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode___boxed(lean_object* v_c_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_IR_ToIR_lowerCode(v_c_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
lean_dec(v_a_1760_);
lean_dec_ref(v_a_1759_);
lean_dec(v_a_1758_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object* v_decl_1763_, lean_object* v_k_1764_, lean_object* v_x_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1763_, v_k_1764_, v_a_1766_, v_a_1767_, v_a_1768_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object* v_decl_1771_, lean_object* v_k_1772_, lean_object* v_x_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(v_decl_1771_, v_k_1772_, v_x_1773_, v_a_1774_, v_a_1775_, v_a_1776_);
lean_dec(v_a_1776_);
lean_dec_ref(v_a_1775_);
lean_dec(v_a_1774_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(size_t v_sz_1779_, size_t v_i_1780_, lean_object* v_bs_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1779_, v_i_1780_, v_bs_1781_, v___y_1782_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object* v_sz_1787_, lean_object* v_i_1788_, lean_object* v_bs_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
size_t v_sz_boxed_1794_; size_t v_i_boxed_1795_; lean_object* v_res_1796_; 
v_sz_boxed_1794_ = lean_unbox_usize(v_sz_1787_);
lean_dec(v_sz_1787_);
v_i_boxed_1795_ = lean_unbox_usize(v_i_1788_);
lean_dec(v_i_1788_);
v_res_1796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(v_sz_boxed_1794_, v_i_boxed_1795_, v_bs_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(size_t v_sz_1797_, size_t v_i_1798_, lean_object* v_bs_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1797_, v_i_1798_, v_bs_1799_, v___y_1800_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object* v_sz_1805_, lean_object* v_i_1806_, lean_object* v_bs_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
size_t v_sz_boxed_1812_; size_t v_i_boxed_1813_; lean_object* v_res_1814_; 
v_sz_boxed_1812_ = lean_unbox_usize(v_sz_1805_);
lean_dec(v_sz_1805_);
v_i_boxed_1813_ = lean_unbox_usize(v_i_1806_);
lean_dec(v_i_1806_);
v_res_1814_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(v_sz_boxed_1812_, v_i_boxed_1813_, v_bs_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object* v_d_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v_toSignature_1820_; lean_object* v_value_1821_; lean_object* v_name_1822_; lean_object* v_type_1823_; lean_object* v_params_1824_; size_t v_sz_1825_; size_t v___x_1826_; lean_object* v___x_1827_; 
v_toSignature_1820_ = lean_ctor_get(v_d_1815_, 0);
lean_inc_ref(v_toSignature_1820_);
v_value_1821_ = lean_ctor_get(v_d_1815_, 1);
lean_inc_ref(v_value_1821_);
lean_dec_ref(v_d_1815_);
v_name_1822_ = lean_ctor_get(v_toSignature_1820_, 0);
lean_inc(v_name_1822_);
v_type_1823_ = lean_ctor_get(v_toSignature_1820_, 2);
lean_inc_ref(v_type_1823_);
v_params_1824_ = lean_ctor_get(v_toSignature_1820_, 3);
lean_inc_ref(v_params_1824_);
lean_dec_ref(v_toSignature_1820_);
v_sz_1825_ = lean_array_size(v_params_1824_);
v___x_1826_ = ((size_t)0ULL);
v___x_1827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1825_, v___x_1826_, v_params_1824_, v_a_1816_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1892_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1830_ = v___x_1827_;
v_isShared_1831_ = v_isSharedCheck_1892_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1892_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_IR_toIRType(v_type_1823_);
lean_dec_ref(v_type_1823_);
if (lean_obj_tag(v_value_1821_) == 0)
{
lean_object* v_code_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1867_; 
lean_del_object(v___x_1830_);
v_code_1833_ = lean_ctor_get(v_value_1821_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_value_1821_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1835_ = v_value_1821_;
v_isShared_1836_ = v_isSharedCheck_1867_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_code_1833_);
lean_dec(v_value_1821_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1867_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Lean_IR_ToIR_lowerCode(v_code_1833_, v_a_1816_, v_a_1817_, v_a_1818_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1858_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1858_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1858_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v_nextJpId_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v_nextVarId_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1842_ = lean_st_ref_get(v_a_1816_);
v_nextJpId_1843_ = lean_ctor_get(v___x_1842_, 3);
lean_inc(v_nextJpId_1843_);
lean_dec(v___x_1842_);
v___x_1844_ = lean_unsigned_to_nat(1u);
v___x_1845_ = lean_nat_sub(v_nextJpId_1843_, v___x_1844_);
lean_dec(v_nextJpId_1843_);
v___x_1846_ = lean_st_ref_get(v_a_1816_);
v_nextVarId_1847_ = lean_ctor_get(v___x_1846_, 2);
lean_inc(v_nextVarId_1847_);
lean_dec(v___x_1846_);
v___x_1848_ = lean_nat_sub(v_nextVarId_1847_, v___x_1844_);
lean_dec(v_nextVarId_1847_);
v___x_1849_ = lean_box(0);
v___x_1850_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set(v___x_1850_, 1, v___x_1845_);
lean_ctor_set(v___x_1850_, 2, v___x_1848_);
v___x_1851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1851_, 0, v_name_1822_);
lean_ctor_set(v___x_1851_, 1, v_a_1828_);
lean_ctor_set(v___x_1851_, 2, v___x_1832_);
lean_ctor_set(v___x_1851_, 3, v_a_1838_);
lean_ctor_set(v___x_1851_, 4, v___x_1850_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set_tag(v___x_1835_, 1);
lean_ctor_set(v___x_1835_, 0, v___x_1851_);
v___x_1853_ = v___x_1835_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1855_; 
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1853_);
v___x_1855_ = v___x_1840_;
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
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_del_object(v___x_1835_);
lean_dec(v___x_1832_);
lean_dec(v_a_1828_);
lean_dec(v_name_1822_);
v_a_1859_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1837_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1837_);
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
else
{
lean_object* v_externAttrData_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1891_; 
v_externAttrData_1868_ = lean_ctor_get(v_value_1821_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_value_1821_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1870_ = v_value_1821_;
v_isShared_1871_ = v_isSharedCheck_1891_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_externAttrData_1868_);
lean_dec(v_value_1821_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1891_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
uint8_t v___x_1872_; 
v___x_1872_ = l_List_isEmpty___redArg(v_externAttrData_1868_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1873_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1873_, 0, v_name_1822_);
lean_ctor_set(v___x_1873_, 1, v_a_1828_);
lean_ctor_set(v___x_1873_, 2, v___x_1832_);
lean_ctor_set(v___x_1873_, 3, v_externAttrData_1868_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v___x_1873_);
v___x_1875_ = v___x_1870_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1877_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1875_);
v___x_1877_ = v___x_1830_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1889_; 
lean_del_object(v___x_1870_);
lean_dec(v_externAttrData_1868_);
lean_del_object(v___x_1830_);
v___x_1880_ = l_Lean_IR_mkDummyExternDecl(v_name_1822_, v_a_1828_, v___x_1832_);
v___x_1881_ = l_Lean_IR_ToIR_addDecl___redArg(v___x_1880_, v_a_1818_);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1889_ == 0)
{
lean_object* v_unused_1890_; 
v_unused_1890_ = lean_ctor_get(v___x_1881_, 0);
lean_dec(v_unused_1890_);
v___x_1883_ = v___x_1881_;
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
else
{
lean_dec(v___x_1881_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1885_ = lean_box(0);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1885_);
v___x_1887_ = v___x_1883_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec_ref(v_type_1823_);
lean_dec(v_name_1822_);
lean_dec_ref(v_value_1821_);
v_a_1893_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1827_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1827_);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl___boxed(lean_object* v_d_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_IR_ToIR_lowerDecl(v_d_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(lean_object* v_as_1907_, size_t v_sz_1908_, size_t v_i_1909_, lean_object* v_b_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_a_1915_; uint8_t v___x_1919_; 
v___x_1919_ = lean_usize_dec_lt(v_i_1909_, v_sz_1908_);
if (v___x_1919_ == 0)
{
lean_object* v___x_1920_; 
v___x_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1920_, 0, v_b_1910_);
return v___x_1920_;
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_a_1921_ = lean_array_uget_borrowed(v_as_1907_, v_i_1909_);
lean_inc(v_a_1921_);
v___x_1922_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerDecl___boxed), 5, 1);
lean_closure_set(v___x_1922_, 0, v_a_1921_);
v___x_1923_ = l_Lean_IR_ToIR_M_run___redArg(v___x_1922_, v___y_1911_, v___y_1912_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
if (lean_obj_tag(v_a_1924_) == 1)
{
lean_object* v_val_1925_; lean_object* v___x_1926_; 
v_val_1925_ = lean_ctor_get(v_a_1924_, 0);
lean_inc(v_val_1925_);
lean_dec_ref_known(v_a_1924_, 1);
v___x_1926_ = lean_array_push(v_b_1910_, v_val_1925_);
v_a_1915_ = v___x_1926_;
goto v___jp_1914_;
}
else
{
lean_dec(v_a_1924_);
v_a_1915_ = v_b_1910_;
goto v___jp_1914_;
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec_ref(v_b_1910_);
v_a_1927_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1923_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1923_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
v___jp_1914_:
{
size_t v___x_1916_; size_t v___x_1917_; 
v___x_1916_ = ((size_t)1ULL);
v___x_1917_ = lean_usize_add(v_i_1909_, v___x_1916_);
v_i_1909_ = v___x_1917_;
v_b_1910_ = v_a_1915_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0___boxed(lean_object* v_as_1935_, lean_object* v_sz_1936_, lean_object* v_i_1937_, lean_object* v_b_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
size_t v_sz_boxed_1942_; size_t v_i_boxed_1943_; lean_object* v_res_1944_; 
v_sz_boxed_1942_ = lean_unbox_usize(v_sz_1936_);
lean_dec(v_sz_1936_);
v_i_boxed_1943_ = lean_unbox_usize(v_i_1937_);
lean_dec(v_i_1937_);
v_res_1944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_as_1935_, v_sz_boxed_1942_, v_i_boxed_1943_, v_b_1938_, v___y_1939_, v___y_1940_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec_ref(v_as_1935_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object* v_decls_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v_irDecls_1951_; size_t v_sz_1952_; size_t v___x_1953_; lean_object* v___x_1954_; 
v_irDecls_1951_ = ((lean_object*)(l_Lean_IR_toIR___closed__0));
v_sz_1952_ = lean_array_size(v_decls_1947_);
v___x_1953_ = ((size_t)0ULL);
v___x_1954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_decls_1947_, v_sz_1952_, v___x_1953_, v_irDecls_1951_, v_a_1948_, v_a_1949_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object* v_decls_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_IR_toIR(v_decls_1955_, v_a_1956_, v_a_1957_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
lean_dec_ref(v_decls_1955_);
return v_res_1959_;
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
