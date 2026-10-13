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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___lam__0(lean_object* v___x_405_, lean_object* v_d_406_, lean_object* v_s_407_){
_start:
{
lean_object* v_addEntryFn_408_; lean_object* v_importedEntries_409_; lean_object* v_state_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_418_; 
v_addEntryFn_408_ = lean_ctor_get(v___x_405_, 3);
lean_inc(v_addEntryFn_408_);
lean_dec_ref(v___x_405_);
v_importedEntries_409_ = lean_ctor_get(v_s_407_, 0);
v_state_410_ = lean_ctor_get(v_s_407_, 1);
v_isSharedCheck_418_ = !lean_is_exclusive(v_s_407_);
if (v_isSharedCheck_418_ == 0)
{
v___x_412_ = v_s_407_;
v_isShared_413_ = v_isSharedCheck_418_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_state_410_);
lean_inc(v_importedEntries_409_);
lean_dec(v_s_407_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_418_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v_state_414_; lean_object* v___x_416_; 
v_state_414_ = lean_apply_2(v_addEntryFn_408_, v_state_410_, v_d_406_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v_state_414_);
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_importedEntries_409_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_state_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_419_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__0, &l_Lean_IR_ToIR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__1, &l_Lean_IR_ToIR_addDecl___redArg___closed__1_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object* v_d_424_, lean_object* v_a_425_){
_start:
{
lean_object* v___x_427_; lean_object* v_env_428_; lean_object* v_nextMacroScope_429_; lean_object* v_ngen_430_; lean_object* v_auxDeclNGen_431_; lean_object* v_traceState_432_; lean_object* v_recordedDeps_433_; lean_object* v_messages_434_; lean_object* v_infoState_435_; lean_object* v_snapshotTasks_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_459_; 
v___x_427_ = lean_st_ref_take(v_a_425_);
v_env_428_ = lean_ctor_get(v___x_427_, 0);
v_nextMacroScope_429_ = lean_ctor_get(v___x_427_, 1);
v_ngen_430_ = lean_ctor_get(v___x_427_, 2);
v_auxDeclNGen_431_ = lean_ctor_get(v___x_427_, 3);
v_traceState_432_ = lean_ctor_get(v___x_427_, 4);
v_recordedDeps_433_ = lean_ctor_get(v___x_427_, 6);
v_messages_434_ = lean_ctor_get(v___x_427_, 7);
v_infoState_435_ = lean_ctor_get(v___x_427_, 8);
v_snapshotTasks_436_ = lean_ctor_get(v___x_427_, 9);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_459_ == 0)
{
lean_object* v_unused_460_; 
v_unused_460_ = lean_ctor_get(v___x_427_, 5);
lean_dec(v_unused_460_);
v___x_438_ = v___x_427_;
v_isShared_439_ = v_isSharedCheck_459_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_snapshotTasks_436_);
lean_inc(v_infoState_435_);
lean_inc(v_messages_434_);
lean_inc(v_recordedDeps_433_);
lean_inc(v_traceState_432_);
lean_inc(v_auxDeclNGen_431_);
lean_inc(v_ngen_430_);
lean_inc(v_nextMacroScope_429_);
lean_inc(v_env_428_);
lean_dec(v___x_427_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_459_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v_toEnvExtension_441_; lean_object* v_asyncMode_442_; uint8_t v_logWrites_443_; lean_object* v___x_444_; lean_object* v___y_446_; lean_object* v___f_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_440_ = l_Lean_IR_declMapExt;
v_toEnvExtension_441_ = lean_ctor_get(v___x_440_, 0);
v_asyncMode_442_ = lean_ctor_get(v_toEnvExtension_441_, 2);
v_logWrites_443_ = lean_ctor_get_uint8(v_toEnvExtension_441_, sizeof(void*)*6);
v___x_444_ = lean_box(0);
v___f_453_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_addDecl___redArg___lam__0), 3, 2);
lean_closure_set(v___f_453_, 0, v___x_440_);
lean_closure_set(v___f_453_, 1, v_d_424_);
v___x_454_ = lean_box(0);
v___x_455_ = 1;
if (v_logWrites_443_ == 0)
{
lean_object* v___x_456_; 
lean_inc_ref(v_toEnvExtension_441_);
v___x_456_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_441_, v_env_428_, v___f_453_, v_asyncMode_442_, v___x_454_, v___x_455_);
v___y_446_ = v___x_456_;
goto v___jp_445_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; 
lean_inc_ref_n(v_toEnvExtension_441_, 2);
v___x_457_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_441_, v_env_428_);
lean_dec_ref(v_env_428_);
v___x_458_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_441_, v___x_457_, v___f_453_, v_asyncMode_442_, v___x_454_, v___x_455_);
v___y_446_ = v___x_458_;
goto v___jp_445_;
}
v___jp_445_:
{
lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_447_ = lean_obj_once(&l_Lean_IR_ToIR_addDecl___redArg___closed__2, &l_Lean_IR_ToIR_addDecl___redArg___closed__2_once, _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 5, v___x_447_);
lean_ctor_set(v___x_438_, 0, v___y_446_);
v___x_449_ = v___x_438_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___y_446_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_nextMacroScope_429_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v_ngen_430_);
lean_ctor_set(v_reuseFailAlloc_452_, 3, v_auxDeclNGen_431_);
lean_ctor_set(v_reuseFailAlloc_452_, 4, v_traceState_432_);
lean_ctor_set(v_reuseFailAlloc_452_, 5, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_452_, 6, v_recordedDeps_433_);
lean_ctor_set(v_reuseFailAlloc_452_, 7, v_messages_434_);
lean_ctor_set(v_reuseFailAlloc_452_, 8, v_infoState_435_);
lean_ctor_set(v_reuseFailAlloc_452_, 9, v_snapshotTasks_436_);
v___x_449_ = v_reuseFailAlloc_452_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_st_ref_put(v_a_425_, v___x_449_);
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_444_);
return v___x_451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object* v_d_461_, lean_object* v_a_462_, lean_object* v_a_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_461_, v_a_462_);
lean_dec(v_a_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object* v_d_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_465_, v_a_468_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object* v_d_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_IR_ToIR_addDecl(v_d_471_, v_a_472_, v_a_473_, v_a_474_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object* v_v_477_){
_start:
{
switch(lean_obj_tag(v_v_477_))
{
case 0:
{
lean_object* v_val_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_492_; 
v_val_478_ = lean_ctor_get(v_v_477_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v_v_477_);
if (v_isSharedCheck_492_ == 0)
{
v___x_480_ = v_v_477_;
v_isShared_481_ = v_isSharedCheck_492_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_val_478_);
lean_dec(v_v_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_492_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___y_483_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = lean_cstr_to_nat("4294967296");
v___x_489_ = lean_nat_dec_lt(v_val_478_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; 
v___x_490_ = lean_box(8);
v___y_483_ = v___x_490_;
goto v___jp_482_;
}
else
{
lean_object* v___x_491_; 
v___x_491_ = lean_box(12);
v___y_483_ = v___x_491_;
goto v___jp_482_;
}
v___jp_482_:
{
lean_object* v___x_485_; 
if (v_isShared_481_ == 0)
{
v___x_485_ = v___x_480_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_val_478_);
v___x_485_ = v_reuseFailAlloc_487_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_486_; 
lean_inc(v___y_483_);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___y_483_);
return v___x_486_;
}
}
}
}
case 1:
{
lean_object* v_val_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_502_; 
v_val_493_ = lean_ctor_get(v_v_477_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v_v_477_);
if (v_isSharedCheck_502_ == 0)
{
v___x_495_ = v_v_477_;
v_isShared_496_ = v_isSharedCheck_502_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_val_493_);
lean_dec(v_v_477_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_502_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_val_493_);
v___x_498_ = v_reuseFailAlloc_501_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_box(7);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
return v___x_500_;
}
}
}
case 2:
{
uint8_t v_val_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_val_503_ = lean_ctor_get_uint8(v_v_477_, 0);
lean_dec_ref_known(v_v_477_, 0);
v___x_504_ = lean_uint8_to_nat(v_val_503_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
v___x_506_ = lean_box(1);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_505_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
return v___x_507_;
}
case 3:
{
uint16_t v_val_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v_val_508_ = lean_ctor_get_uint16(v_v_477_, 0);
lean_dec_ref_known(v_v_477_, 0);
v___x_509_ = lean_uint16_to_nat(v_val_508_);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
v___x_511_ = lean_box(2);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
return v___x_512_;
}
case 4:
{
uint32_t v_val_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_val_513_ = lean_ctor_get_uint32(v_v_477_, 0);
lean_dec_ref_known(v_v_477_, 0);
v___x_514_ = lean_uint32_to_nat(v_val_513_);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
v___x_516_ = lean_box(3);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
return v___x_517_;
}
case 5:
{
uint64_t v_val_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_val_518_ = lean_ctor_get_uint64(v_v_477_, 0);
lean_dec_ref_known(v_v_477_, 0);
v___x_519_ = lean_uint64_to_nat(v_val_518_);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
v___x_521_ = lean_box(4);
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
return v___x_522_;
}
default: 
{
uint64_t v_val_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v_val_523_ = lean_ctor_get_uint64(v_v_477_, 0);
lean_dec_ref_known(v_v_477_, 0);
v___x_524_ = lean_uint64_to_nat(v_val_523_);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
v___x_526_ = lean_box(5);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
return v___x_527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
if (lean_obj_tag(v_a_528_) == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_box(1);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
else
{
lean_object* v_fvarId_533_; lean_object* v___x_534_; 
v_fvarId_533_ = lean_ctor_get(v_a_528_, 0);
v___x_534_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_533_, v_a_529_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_535_, v_a_536_);
lean_dec(v_a_536_);
lean_dec(v_a_535_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_539_, v_a_540_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_IR_ToIR_lowerArg(v_a_545_, v_a_546_, v_a_547_, v_a_548_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec(v_a_545_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg(lean_object* v_p_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_fvarId_554_; lean_object* v_type_555_; uint8_t v_borrow_556_; lean_object* v___x_557_; lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_571_; 
v_fvarId_554_ = lean_ctor_get(v_p_551_, 0);
lean_inc(v_fvarId_554_);
v_type_555_ = lean_ctor_get(v_p_551_, 2);
lean_inc_ref(v_type_555_);
v_borrow_556_ = lean_ctor_get_uint8(v_p_551_, sizeof(void*)*3);
lean_dec_ref(v_p_551_);
v___x_557_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_554_, v_a_552_);
v_a_558_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_571_ == 0)
{
v___x_560_ = v___x_557_;
v_isShared_561_ = v_isSharedCheck_571_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_557_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_571_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; uint8_t v___y_564_; 
v___x_562_ = l_Lean_IR_toIRType(v_type_555_);
lean_dec_ref(v_type_555_);
if (v_borrow_556_ == 0)
{
v___y_564_ = v_borrow_556_;
goto v___jp_563_;
}
else
{
uint8_t v___x_569_; 
v___x_569_ = l_Lean_IR_IRType_isScalar(v___x_562_);
if (v___x_569_ == 0)
{
v___y_564_ = v_borrow_556_;
goto v___jp_563_;
}
else
{
uint8_t v___x_570_; 
v___x_570_ = 0;
v___y_564_ = v___x_570_;
goto v___jp_563_;
}
}
v___jp_563_:
{
lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_565_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_565_, 0, v_a_558_);
lean_ctor_set(v___x_565_, 1, v___x_562_);
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*2, v___y_564_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v___x_565_);
v___x_567_ = v___x_560_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___redArg___boxed(lean_object* v_p_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_572_, v_a_573_);
lean_dec(v_a_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object* v_p_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_576_, v_a_577_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object* v_p_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_IR_ToIR_lowerParam(v_p_582_, v_a_583_, v_a_584_, v_a_585_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec(v_a_583_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCtorInfo(lean_object* v_i_588_){
_start:
{
lean_object* v_name_589_; lean_object* v_cidx_590_; lean_object* v_size_591_; lean_object* v_usize_592_; lean_object* v_ssize_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
v_name_589_ = lean_ctor_get(v_i_588_, 0);
v_cidx_590_ = lean_ctor_get(v_i_588_, 1);
v_size_591_ = lean_ctor_get(v_i_588_, 2);
v_usize_592_ = lean_ctor_get(v_i_588_, 3);
v_ssize_593_ = lean_ctor_get(v_i_588_, 4);
v_isSharedCheck_600_ = !lean_is_exclusive(v_i_588_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v_i_588_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_ssize_593_);
lean_inc(v_usize_592_);
lean_inc(v_size_591_);
lean_inc(v_cidx_590_);
lean_inc(v_name_589_);
lean_dec(v_i_588_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_name_589_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_cidx_590_);
lean_ctor_set(v_reuseFailAlloc_599_, 2, v_size_591_);
lean_ctor_set(v_reuseFailAlloc_599_, 3, v_usize_592_);
lean_ctor_set(v_reuseFailAlloc_599_, 4, v_ssize_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0(void){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_instMonadEIO___redArg();
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(lean_object* v_msg_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v_toApplicative_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_643_; 
v___x_609_ = lean_obj_once(&l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0, &l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0_once, _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0);
v___x_610_ = l_StateRefT_x27_instMonad___redArg(v___x_609_);
v_toApplicative_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; 
v_unused_644_ = lean_ctor_get(v___x_610_, 1);
lean_dec(v_unused_644_);
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_643_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_toApplicative_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_643_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_toFunctor_615_; lean_object* v_toSeq_616_; lean_object* v_toSeqLeft_617_; lean_object* v_toSeqRight_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_641_; 
v_toFunctor_615_ = lean_ctor_get(v_toApplicative_611_, 0);
v_toSeq_616_ = lean_ctor_get(v_toApplicative_611_, 2);
v_toSeqLeft_617_ = lean_ctor_get(v_toApplicative_611_, 3);
v_toSeqRight_618_ = lean_ctor_get(v_toApplicative_611_, 4);
v_isSharedCheck_641_ = !lean_is_exclusive(v_toApplicative_611_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; 
v_unused_642_ = lean_ctor_get(v_toApplicative_611_, 1);
lean_dec(v_unused_642_);
v___x_620_ = v_toApplicative_611_;
v_isShared_621_ = v_isSharedCheck_641_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_toSeqRight_618_);
lean_inc(v_toSeqLeft_617_);
lean_inc(v_toSeq_616_);
lean_inc(v_toFunctor_615_);
lean_dec(v_toApplicative_611_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_641_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___f_622_; lean_object* v___f_623_; lean_object* v___f_624_; lean_object* v___f_625_; lean_object* v___x_626_; lean_object* v___f_627_; lean_object* v___f_628_; lean_object* v___f_629_; lean_object* v___x_631_; 
v___f_622_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1));
v___f_623_ = ((lean_object*)(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2));
lean_inc_ref(v_toFunctor_615_);
v___f_624_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_624_, 0, v_toFunctor_615_);
v___f_625_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_625_, 0, v_toFunctor_615_);
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v___f_624_);
lean_ctor_set(v___x_626_, 1, v___f_625_);
v___f_627_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_627_, 0, v_toSeqRight_618_);
v___f_628_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_628_, 0, v_toSeqLeft_617_);
v___f_629_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_629_, 0, v_toSeq_616_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 4, v___f_627_);
lean_ctor_set(v___x_620_, 3, v___f_628_);
lean_ctor_set(v___x_620_, 2, v___f_629_);
lean_ctor_set(v___x_620_, 1, v___f_622_);
lean_ctor_set(v___x_620_, 0, v___x_626_);
v___x_631_ = v___x_620_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v___f_622_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v___f_629_);
lean_ctor_set(v_reuseFailAlloc_640_, 3, v___f_628_);
lean_ctor_set(v_reuseFailAlloc_640_, 4, v___f_627_);
v___x_631_ = v_reuseFailAlloc_640_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v___f_623_);
lean_ctor_set(v___x_613_, 0, v___x_631_);
v___x_633_ = v___x_613_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___f_623_);
v___x_633_ = v_reuseFailAlloc_639_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_7937__overap_637_; lean_object* v___x_638_; 
v___x_634_ = l_StateRefT_x27_instMonad___redArg(v___x_633_);
v___x_635_ = l_Lean_IR_instInhabitedFnBody_default__1;
v___x_636_ = l_instInhabitedOfMonad___redArg(v___x_634_, v___x_635_);
v___x_7937__overap_637_ = lean_panic_fn_borrowed(v___x_636_, v_msg_604_);
lean_dec(v___x_636_);
lean_inc(v___y_607_);
lean_inc_ref(v___y_606_);
lean_inc(v___y_605_);
v___x_638_ = lean_apply_4(v___x_7937__overap_637_, v___y_605_, v___y_606_, v___y_607_, lean_box(0));
return v___x_638_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object* v_msg_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v_msg_645_, v___y_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(size_t v_sz_651_, size_t v_i_652_, lean_object* v_bs_653_, lean_object* v___y_654_){
_start:
{
uint8_t v___x_656_; 
v___x_656_ = lean_usize_dec_lt(v_i_652_, v_sz_651_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v_bs_653_);
return v___x_657_;
}
else
{
lean_object* v_v_658_; lean_object* v___x_659_; lean_object* v_bs_x27_660_; lean_object* v___x_661_; 
v_v_658_ = lean_array_uget(v_bs_653_, v_i_652_);
v___x_659_ = lean_unsigned_to_nat(0u);
v_bs_x27_660_ = lean_array_uset(v_bs_653_, v_i_652_, v___x_659_);
v___x_661_ = l_Lean_IR_ToIR_lowerArg___redArg(v_v_658_, v___y_654_);
lean_dec(v_v_658_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
v___x_663_ = ((size_t)1ULL);
v___x_664_ = lean_usize_add(v_i_652_, v___x_663_);
v___x_665_ = lean_array_uset(v_bs_x27_660_, v_i_652_, v_a_662_);
v_i_652_ = v___x_664_;
v_bs_653_ = v___x_665_;
goto _start;
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec_ref(v_bs_x27_660_);
v_a_667_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_661_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_661_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object* v_sz_675_, lean_object* v_i_676_, lean_object* v_bs_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
size_t v_sz_boxed_680_; size_t v_i_boxed_681_; lean_object* v_res_682_; 
v_sz_boxed_680_ = lean_unbox_usize(v_sz_675_);
lean_dec(v_sz_675_);
v_i_boxed_681_ = lean_unbox_usize(v_i_676_);
lean_dec(v_i_676_);
v_res_682_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_boxed_680_, v_i_boxed_681_, v_bs_677_, v___y_678_);
lean_dec(v___y_678_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(size_t v_sz_683_, size_t v_i_684_, lean_object* v_bs_685_, lean_object* v___y_686_){
_start:
{
uint8_t v___x_688_; 
v___x_688_ = lean_usize_dec_lt(v_i_684_, v_sz_683_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v_bs_685_);
return v___x_689_;
}
else
{
lean_object* v_v_690_; lean_object* v___x_691_; lean_object* v_bs_x27_692_; lean_object* v___x_693_; 
v_v_690_ = lean_array_uget(v_bs_685_, v_i_684_);
v___x_691_ = lean_unsigned_to_nat(0u);
v_bs_x27_692_ = lean_array_uset(v_bs_685_, v_i_684_, v___x_691_);
v___x_693_ = l_Lean_IR_ToIR_lowerParam___redArg(v_v_690_, v___y_686_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; size_t v___x_695_; size_t v___x_696_; lean_object* v___x_697_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_693_, 1);
v___x_695_ = ((size_t)1ULL);
v___x_696_ = lean_usize_add(v_i_684_, v___x_695_);
v___x_697_ = lean_array_uset(v_bs_x27_692_, v_i_684_, v_a_694_);
v_i_684_ = v___x_696_;
v_bs_685_ = v___x_697_;
goto _start;
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec_ref(v_bs_x27_692_);
v_a_699_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_693_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_693_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg___boxed(lean_object* v_sz_707_, lean_object* v_i_708_, lean_object* v_bs_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
size_t v_sz_boxed_712_; size_t v_i_boxed_713_; lean_object* v_res_714_; 
v_sz_boxed_712_ = lean_unbox_usize(v_sz_707_);
lean_dec(v_sz_707_);
v_i_boxed_713_ = lean_unbox_usize(v_i_708_);
lean_dec(v_i_708_);
v_res_714_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_boxed_712_, v_i_boxed_713_, v_bs_709_, v___y_710_);
lean_dec(v___y_710_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2(lean_object* v_i_715_, lean_object* v_continueLet_716_, lean_object* v_var_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_722_, 0, v_i_715_);
lean_ctor_set(v___x_722_, 1, v_var_717_);
lean_inc(v___y_720_);
lean_inc_ref(v___y_719_);
lean_inc(v___y_718_);
v___x_723_ = lean_apply_5(v_continueLet_716_, v___x_722_, v___y_718_, v___y_719_, v___y_720_, lean_box(0));
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2___boxed(lean_object* v_i_724_, lean_object* v_continueLet_725_, lean_object* v_var_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_IR_ToIR_lowerLet___lam__2(v_i_724_, v_continueLet_725_, v_var_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4(lean_object* v_n_732_, lean_object* v_offset_733_, lean_object* v_continueLet_734_, lean_object* v_var_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_740_, 0, v_n_732_);
lean_ctor_set(v___x_740_, 1, v_offset_733_);
lean_ctor_set(v___x_740_, 2, v_var_735_);
lean_inc(v___y_738_);
lean_inc_ref(v___y_737_);
lean_inc(v___y_736_);
v___x_741_ = lean_apply_5(v_continueLet_734_, v___x_740_, v___y_736_, v___y_737_, v___y_738_, lean_box(0));
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4___boxed(lean_object* v_n_742_, lean_object* v_offset_743_, lean_object* v_continueLet_744_, lean_object* v_var_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_IR_ToIR_lowerLet___lam__4(v_n_742_, v_offset_743_, v_continueLet_744_, v_var_745_, v___y_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5(lean_object* v_n_751_, lean_object* v_continueLet_752_, lean_object* v_var_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_758_, 0, v_n_751_);
lean_ctor_set(v___x_758_, 1, v_var_753_);
lean_inc(v___y_756_);
lean_inc_ref(v___y_755_);
lean_inc(v___y_754_);
v___x_759_ = lean_apply_5(v_continueLet_752_, v___x_758_, v___y_754_, v___y_755_, v___y_756_, lean_box(0));
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5___boxed(lean_object* v_n_760_, lean_object* v_continueLet_761_, lean_object* v_var_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_IR_ToIR_lowerLet___lam__5(v_n_760_, v_continueLet_761_, v_var_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8(lean_object* v_continueLet_768_, lean_object* v_var_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_774_, 0, v_var_769_);
lean_inc(v___y_772_);
lean_inc_ref(v___y_771_);
lean_inc(v___y_770_);
v___x_775_ = lean_apply_5(v_continueLet_768_, v___x_774_, v___y_770_, v___y_771_, v___y_772_, lean_box(0));
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8___boxed(lean_object* v_continueLet_776_, lean_object* v_var_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_IR_ToIR_lowerLet___lam__8(v_continueLet_776_, v_var_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3(lean_object* v_i_783_, lean_object* v_continueLet_784_, lean_object* v_var_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_790_, 0, v_i_783_);
lean_ctor_set(v___x_790_, 1, v_var_785_);
lean_inc(v___y_788_);
lean_inc_ref(v___y_787_);
lean_inc(v___y_786_);
v___x_791_ = lean_apply_5(v_continueLet_784_, v___x_790_, v___y_786_, v___y_787_, v___y_788_, lean_box(0));
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3___boxed(lean_object* v_i_792_, lean_object* v_continueLet_793_, lean_object* v_var_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_IR_ToIR_lowerLet___lam__3(v_i_792_, v_continueLet_793_, v_var_794_, v___y_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7(lean_object* v_ty_800_, lean_object* v_continueLet_801_, lean_object* v_var_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_807_ = l_Lean_IR_toIRType(v_ty_800_);
v___x_808_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v_var_802_);
lean_inc(v___y_805_);
lean_inc_ref(v___y_804_);
lean_inc(v___y_803_);
v___x_809_ = lean_apply_5(v_continueLet_801_, v___x_808_, v___y_803_, v___y_804_, v___y_805_, lean_box(0));
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__7___boxed(lean_object* v_ty_810_, lean_object* v_continueLet_811_, lean_object* v_var_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_IR_ToIR_lowerLet___lam__7(v_ty_810_, v_continueLet_811_, v_var_812_, v___y_813_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v_ty_810_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6(lean_object* v_args_818_, lean_object* v_i_819_, uint8_t v_updateHeader_820_, lean_object* v_continueLet_821_, lean_object* v_var_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
size_t v_sz_827_; size_t v___x_828_; lean_object* v___x_829_; 
v_sz_827_ = lean_array_size(v_args_818_);
v___x_828_ = ((size_t)0ULL);
v___x_829_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_827_, v___x_828_, v_args_818_, v___y_823_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v_name_831_; lean_object* v_cidx_832_; lean_object* v_size_833_; lean_object* v_usize_834_; lean_object* v_ssize_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_844_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref_known(v___x_829_, 1);
v_name_831_ = lean_ctor_get(v_i_819_, 0);
v_cidx_832_ = lean_ctor_get(v_i_819_, 1);
v_size_833_ = lean_ctor_get(v_i_819_, 2);
v_usize_834_ = lean_ctor_get(v_i_819_, 3);
v_ssize_835_ = lean_ctor_get(v_i_819_, 4);
v_isSharedCheck_844_ = !lean_is_exclusive(v_i_819_);
if (v_isSharedCheck_844_ == 0)
{
v___x_837_ = v_i_819_;
v_isShared_838_ = v_isSharedCheck_844_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_ssize_835_);
lean_inc(v_usize_834_);
lean_inc(v_size_833_);
lean_inc(v_cidx_832_);
lean_inc(v_name_831_);
lean_dec(v_i_819_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_844_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_name_831_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_cidx_832_);
lean_ctor_set(v_reuseFailAlloc_843_, 2, v_size_833_);
lean_ctor_set(v_reuseFailAlloc_843_, 3, v_usize_834_);
lean_ctor_set(v_reuseFailAlloc_843_, 4, v_ssize_835_);
v___x_840_ = v_reuseFailAlloc_843_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v___x_841_, 0, v_var_822_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
lean_ctor_set(v___x_841_, 2, v_a_830_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*3, v_updateHeader_820_);
lean_inc(v___y_825_);
lean_inc_ref(v___y_824_);
lean_inc(v___y_823_);
v___x_842_ = lean_apply_5(v_continueLet_821_, v___x_841_, v___y_823_, v___y_824_, v___y_825_, lean_box(0));
return v___x_842_;
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
lean_dec(v_var_822_);
lean_dec_ref(v_continueLet_821_);
lean_dec_ref(v_i_819_);
v_a_845_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_829_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_829_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6___boxed(lean_object* v_args_853_, lean_object* v_i_854_, lean_object* v_updateHeader_855_, lean_object* v_continueLet_856_, lean_object* v_var_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
uint8_t v_updateHeader_8994__boxed_862_; lean_object* v_res_863_; 
v_updateHeader_8994__boxed_862_ = lean_unbox(v_updateHeader_855_);
v_res_863_ = l_Lean_IR_ToIR_lowerLet___lam__6(v_args_853_, v_i_854_, v_updateHeader_8994__boxed_862_, v_continueLet_856_, v_var_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9(lean_object* v_continueLet_864_, lean_object* v_var_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_870_, 0, v_var_865_);
lean_inc(v___y_868_);
lean_inc_ref(v___y_867_);
lean_inc(v___y_866_);
v___x_871_ = lean_apply_5(v_continueLet_864_, v___x_870_, v___y_866_, v___y_867_, v___y_868_, lean_box(0));
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__9___boxed(lean_object* v_continueLet_872_, lean_object* v_var_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_IR_ToIR_lowerLet___lam__9(v_continueLet_872_, v_var_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1(lean_object* v_args_879_, lean_object* v_continueLet_880_, lean_object* v_id_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
size_t v_sz_886_; size_t v___x_887_; lean_object* v___x_888_; 
v_sz_886_ = lean_array_size(v_args_879_);
v___x_887_ = ((size_t)0ULL);
v___x_888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_886_, v___x_887_, v_args_879_, v___y_882_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref_known(v___x_888_, 1);
v___x_890_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_890_, 0, v_id_881_);
lean_ctor_set(v___x_890_, 1, v_a_889_);
lean_inc(v___y_884_);
lean_inc_ref(v___y_883_);
lean_inc(v___y_882_);
v___x_891_ = lean_apply_5(v_continueLet_880_, v___x_890_, v___y_882_, v___y_883_, v___y_884_, lean_box(0));
return v___x_891_;
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec(v_id_881_);
lean_dec_ref(v_continueLet_880_);
v_a_892_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_888_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_888_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1___boxed(lean_object* v_args_900_, lean_object* v_continueLet_901_, lean_object* v_id_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_IR_ToIR_lowerLet___lam__1(v_args_900_, v_continueLet_901_, v_id_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0(lean_object* v_fvarId_908_, lean_object* v_k_909_, lean_object* v_type_910_, lean_object* v_e_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_908_, v___y_912_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_918_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
v___x_918_ = l_Lean_IR_ToIR_lowerCode(v_k_909_, v___y_912_, v___y_913_, v___y_914_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_927_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_927_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_927_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_927_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_923_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_923_, 0, v_a_917_);
lean_ctor_set(v___x_923_, 1, v_type_910_);
lean_ctor_set(v___x_923_, 2, v_e_911_);
lean_ctor_set(v___x_923_, 3, v_a_919_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_923_);
v___x_925_ = v___x_921_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
else
{
lean_dec(v_a_917_);
lean_dec_ref(v_e_911_);
lean_dec(v_type_910_);
return v___x_918_;
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec_ref(v_e_911_);
lean_dec(v_type_910_);
lean_dec_ref(v_k_909_);
v_a_928_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_916_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_916_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object* v_fvarId_936_, lean_object* v_k_937_, lean_object* v_type_938_, lean_object* v_e_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_936_, v_k_937_, v_type_938_, v_e_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(lean_object* v_decl_945_, lean_object* v_k_946_, lean_object* v_fvarId_947_, lean_object* v_f_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_947_, v_a_949_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
if (lean_obj_tag(v_a_954_) == 0)
{
lean_object* v_id_955_; lean_object* v___x_956_; 
lean_dec_ref(v_k_946_);
lean_dec_ref(v_decl_945_);
v_id_955_ = lean_ctor_get(v_a_954_, 0);
lean_inc(v_id_955_);
lean_dec_ref_known(v_a_954_, 1);
lean_inc(v_a_951_);
lean_inc_ref(v_a_950_);
lean_inc(v_a_949_);
v___x_956_ = lean_apply_5(v_f_948_, v_id_955_, v_a_949_, v_a_950_, v_a_951_, lean_box(0));
return v___x_956_;
}
else
{
lean_object* v___x_957_; 
lean_dec_ref(v_f_948_);
v___x_957_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_945_, v_k_946_, v_a_949_, v_a_950_, v_a_951_);
return v___x_957_;
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec_ref(v_f_948_);
lean_dec_ref(v_k_946_);
lean_dec_ref(v_decl_945_);
v_a_958_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_953_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_953_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object* v_decl_966_, lean_object* v_k_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_fvarId_972_; lean_object* v_type_973_; lean_object* v_value_974_; lean_object* v_type_975_; lean_object* v_continueLet_976_; 
v_fvarId_972_ = lean_ctor_get(v_decl_966_, 0);
v_type_973_ = lean_ctor_get(v_decl_966_, 2);
v_value_974_ = lean_ctor_get(v_decl_966_, 3);
lean_inc(v_value_974_);
v_type_975_ = l_Lean_IR_toIRType(v_type_973_);
lean_inc(v_type_975_);
lean_inc_ref(v_k_967_);
lean_inc(v_fvarId_972_);
v_continueLet_976_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 8, 3);
lean_closure_set(v_continueLet_976_, 0, v_fvarId_972_);
lean_closure_set(v_continueLet_976_, 1, v_k_967_);
lean_closure_set(v_continueLet_976_, 2, v_type_975_);
switch(lean_obj_tag(v_value_974_))
{
case 0:
{
lean_object* v_value_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_987_; 
lean_inc(v_fvarId_972_);
lean_dec_ref(v_continueLet_976_);
lean_dec_ref(v_decl_966_);
v_value_977_ = lean_ctor_get(v_value_974_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v_value_974_);
if (v_isSharedCheck_987_ == 0)
{
v___x_979_ = v_value_974_;
v_isShared_980_ = v_isSharedCheck_987_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_value_977_);
lean_dec(v_value_974_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_987_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; lean_object* v_fst_982_; lean_object* v___x_984_; 
v___x_981_ = l_Lean_IR_ToIR_lowerLitValue(v_value_977_);
v_fst_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_fst_982_);
lean_dec_ref(v___x_981_);
if (v_isShared_980_ == 0)
{
lean_ctor_set_tag(v___x_979_, 11);
lean_ctor_set(v___x_979_, 0, v_fst_982_);
v___x_984_ = v___x_979_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_fst_982_);
v___x_984_ = v_reuseFailAlloc_986_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_972_, v_k_967_, v_type_975_, v___x_984_, v_a_968_, v_a_969_, v_a_970_);
return v___x_985_;
}
}
}
case 1:
{
lean_object* v___x_988_; 
lean_dec_ref(v_continueLet_976_);
lean_dec(v_type_975_);
v___x_988_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_966_, v_k_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_988_;
}
case 4:
{
lean_object* v_fvarId_989_; lean_object* v_args_990_; lean_object* v___f_991_; lean_object* v___x_992_; 
lean_dec(v_type_975_);
v_fvarId_989_ = lean_ctor_get(v_value_974_, 0);
lean_inc(v_fvarId_989_);
v_args_990_ = lean_ctor_get(v_value_974_, 1);
lean_inc_ref(v_args_990_);
lean_dec_ref_known(v_value_974_, 2);
v___f_991_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__1___boxed), 7, 2);
lean_closure_set(v___f_991_, 0, v_args_990_);
lean_closure_set(v___f_991_, 1, v_continueLet_976_);
v___x_992_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_966_, v_k_967_, v_fvarId_989_, v___f_991_, v_a_968_, v_a_969_, v_a_970_);
lean_dec(v_fvarId_989_);
return v___x_992_;
}
case 5:
{
lean_object* v_i_993_; lean_object* v_args_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1026_; 
lean_inc(v_fvarId_972_);
lean_dec_ref(v_continueLet_976_);
lean_dec_ref(v_decl_966_);
v_i_993_ = lean_ctor_get(v_value_974_, 0);
v_args_994_ = lean_ctor_get(v_value_974_, 1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_value_974_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_996_ = v_value_974_;
v_isShared_997_ = v_isSharedCheck_1026_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_args_994_);
lean_inc(v_i_993_);
lean_dec(v_value_974_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1026_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
size_t v_sz_998_; size_t v___x_999_; lean_object* v___x_1000_; 
v_sz_998_ = lean_array_size(v_args_994_);
v___x_999_ = ((size_t)0ULL);
v___x_1000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_998_, v___x_999_, v_args_994_, v_a_968_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v_name_1002_; lean_object* v_cidx_1003_; lean_object* v_size_1004_; lean_object* v_usize_1005_; lean_object* v_ssize_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1017_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v_name_1002_ = lean_ctor_get(v_i_993_, 0);
v_cidx_1003_ = lean_ctor_get(v_i_993_, 1);
v_size_1004_ = lean_ctor_get(v_i_993_, 2);
v_usize_1005_ = lean_ctor_get(v_i_993_, 3);
v_ssize_1006_ = lean_ctor_get(v_i_993_, 4);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_i_993_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1008_ = v_i_993_;
v_isShared_1009_ = v_isSharedCheck_1017_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_ssize_1006_);
lean_inc(v_usize_1005_);
lean_inc(v_size_1004_);
lean_inc(v_cidx_1003_);
lean_inc(v_name_1002_);
lean_dec(v_i_993_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1017_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_name_1002_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_cidx_1003_);
lean_ctor_set(v_reuseFailAlloc_1016_, 2, v_size_1004_);
lean_ctor_set(v_reuseFailAlloc_1016_, 3, v_usize_1005_);
lean_ctor_set(v_reuseFailAlloc_1016_, 4, v_ssize_1006_);
v___x_1011_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1013_; 
if (v_isShared_997_ == 0)
{
lean_ctor_set_tag(v___x_996_, 0);
lean_ctor_set(v___x_996_, 1, v_a_1001_);
lean_ctor_set(v___x_996_, 0, v___x_1011_);
v___x_1013_ = v___x_996_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_a_1001_);
v___x_1013_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_972_, v_k_967_, v_type_975_, v___x_1013_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1014_;
}
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_del_object(v___x_996_);
lean_dec_ref(v_i_993_);
lean_dec(v_type_975_);
lean_dec(v_fvarId_972_);
lean_dec_ref(v_k_967_);
v_a_1018_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1000_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1000_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
case 6:
{
lean_object* v_i_1027_; lean_object* v_var_1028_; lean_object* v___f_1029_; lean_object* v___x_1030_; 
lean_dec(v_type_975_);
v_i_1027_ = lean_ctor_get(v_value_974_, 0);
lean_inc(v_i_1027_);
v_var_1028_ = lean_ctor_get(v_value_974_, 1);
lean_inc(v_var_1028_);
lean_dec_ref_known(v_value_974_, 2);
v___f_1029_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__2___boxed), 7, 2);
lean_closure_set(v___f_1029_, 0, v_i_1027_);
lean_closure_set(v___f_1029_, 1, v_continueLet_976_);
v___x_1030_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_966_, v_k_967_, v_var_1028_, v___f_1029_, v_a_968_, v_a_969_, v_a_970_);
lean_dec(v_var_1028_);
return v___x_1030_;
}
case 7:
{
lean_object* v_i_1031_; lean_object* v_var_1032_; lean_object* v___f_1033_; lean_object* v___x_1034_; 
lean_dec(v_type_975_);
v_i_1031_ = lean_ctor_get(v_value_974_, 0);
lean_inc(v_i_1031_);
v_var_1032_ = lean_ctor_get(v_value_974_, 1);
lean_inc(v_var_1032_);
lean_dec_ref_known(v_value_974_, 2);
v___f_1033_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__3___boxed), 7, 2);
lean_closure_set(v___f_1033_, 0, v_i_1031_);
lean_closure_set(v___f_1033_, 1, v_continueLet_976_);
v___x_1034_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_966_, v_k_967_, v_var_1032_, v___f_1033_, v_a_968_, v_a_969_, v_a_970_);
lean_dec(v_var_1032_);
return v___x_1034_;
}
case 8:
{
lean_object* v_n_1035_; lean_object* v_offset_1036_; lean_object* v_var_1037_; lean_object* v___f_1038_; lean_object* v___x_1039_; 
lean_dec(v_type_975_);
v_n_1035_ = lean_ctor_get(v_value_974_, 0);
lean_inc(v_n_1035_);
v_offset_1036_ = lean_ctor_get(v_value_974_, 1);
lean_inc(v_offset_1036_);
v_var_1037_ = lean_ctor_get(v_value_974_, 2);
lean_inc(v_var_1037_);
lean_dec_ref_known(v_value_974_, 3);
v___f_1038_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__4___boxed), 8, 3);
lean_closure_set(v___f_1038_, 0, v_n_1035_);
lean_closure_set(v___f_1038_, 1, v_offset_1036_);
lean_closure_set(v___f_1038_, 2, v_continueLet_976_);
v___x_1039_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_966_, v_k_967_, v_var_1037_, v___f_1038_, v_a_968_, v_a_969_, v_a_970_);
lean_dec(v_var_1037_);
return v___x_1039_;
}
case 9:
{
lean_object* v_fn_1040_; lean_object* v_args_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1061_; 
lean_inc(v_fvarId_972_);
lean_dec_ref(v_continueLet_976_);
lean_dec_ref(v_decl_966_);
v_fn_1040_ = lean_ctor_get(v_value_974_, 0);
v_args_1041_ = lean_ctor_get(v_value_974_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_value_974_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1043_ = v_value_974_;
v_isShared_1044_ = v_isSharedCheck_1061_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_args_1041_);
lean_inc(v_fn_1040_);
lean_dec(v_value_974_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1061_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
size_t v_sz_1045_; size_t v___x_1046_; lean_object* v___x_1047_; 
v_sz_1045_ = lean_array_size(v_args_1041_);
v___x_1046_ = ((size_t)0ULL);
v___x_1047_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1045_, v___x_1046_, v_args_1041_, v_a_968_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1050_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1047_, 1);
if (v_isShared_1044_ == 0)
{
lean_ctor_set_tag(v___x_1043_, 6);
lean_ctor_set(v___x_1043_, 1, v_a_1048_);
v___x_1050_ = v___x_1043_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_fn_1040_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_a_1048_);
v___x_1050_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_972_, v_k_967_, v_type_975_, v___x_1050_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1051_;
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_del_object(v___x_1043_);
lean_dec(v_fn_1040_);
lean_dec(v_type_975_);
lean_dec(v_fvarId_972_);
lean_dec_ref(v_k_967_);
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
case 10:
{
lean_object* v_fn_1062_; lean_object* v_args_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1083_; 
lean_inc(v_fvarId_972_);
lean_dec_ref(v_continueLet_976_);
lean_dec_ref(v_decl_966_);
v_fn_1062_ = lean_ctor_get(v_value_974_, 0);
v_args_1063_ = lean_ctor_get(v_value_974_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_value_974_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1065_ = v_value_974_;
v_isShared_1066_ = v_isSharedCheck_1083_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_args_1063_);
lean_inc(v_fn_1062_);
lean_dec(v_value_974_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1083_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
size_t v_sz_1067_; size_t v___x_1068_; lean_object* v___x_1069_; 
v_sz_1067_ = lean_array_size(v_args_1063_);
v___x_1068_ = ((size_t)0ULL);
v___x_1069_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1067_, v___x_1068_, v_args_1063_, v_a_968_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1069_, 1);
if (v_isShared_1066_ == 0)
{
lean_ctor_set_tag(v___x_1065_, 7);
lean_ctor_set(v___x_1065_, 1, v_a_1070_);
v___x_1072_ = v___x_1065_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_fn_1062_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_a_1070_);
v___x_1072_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_IR_ToIR_lowerLet___lam__0(v_fvarId_972_, v_k_967_, v_type_975_, v___x_1072_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1073_;
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_del_object(v___x_1065_);
lean_dec(v_fn_1062_);
lean_dec(v_type_975_);
lean_dec(v_fvarId_972_);
lean_dec_ref(v_k_967_);
v_a_1075_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1069_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1069_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
case 11:
{
lean_object* v_n_1084_; lean_object* v_var_1085_; lean_object* v___f_1086_; lean_object* v___x_1087_; 
lean_dec(v_type_975_);
v_n_1084_ = lean_ctor_get(v_value_974_, 0);
lean_inc(v_n_1084_);
v_var_1085_ = lean_ctor_get(v_value_974_, 1);
lean_inc(v_var_1085_);
lean_dec_ref_known(v_value_974_, 2);
v___f_1086_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__5___boxed), 7, 2);
lean_closure_set(v___f_1086_, 0, v_n_1084_);
lean_closure_set(v___f_1086_, 1, v_continueLet_976_);
v___x_1087_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_966_, v_k_967_, v_var_1085_, v___f_1086_, v_a_968_, v_a_969_, v_a_970_);
lean_dec(v_var_1085_);
return v___x_1087_;
}
case 12:
{
lean_object* v_var_1088_; lean_object* v_i_1089_; uint8_t v_updateHeader_1090_; lean_object* v_args_1091_; lean_object* v___x_1092_; lean_object* v___f_1093_; lean_object* v___x_1094_; 
lean_dec(v_type_975_);
v_var_1088_ = lean_ctor_get(v_value_974_, 0);
lean_inc(v_var_1088_);
v_i_1089_ = lean_ctor_get(v_value_974_, 1);
lean_inc_ref(v_i_1089_);
v_updateHeader_1090_ = lean_ctor_get_uint8(v_value_974_, sizeof(void*)*3);
v_args_1091_ = lean_ctor_get(v_value_974_, 2);
lean_inc_ref(v_args_1091_);
lean_dec_ref_known(v_value_974_, 3);
v___x_1092_ = lean_box(v_updateHeader_1090_);
v___f_1093_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 9, 4);
lean_closure_set(v___f_1093_, 0, v_args_1091_);
lean_closure_set(v___f_1093_, 1, v_i_1089_);
lean_closure_set(v___f_1093_, 2, v___x_1092_);
lean_closure_set(v___f_1093_, 3, v_continueLet_976_);
v___x_1094_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_966_, v_k_967_, v_var_1088_, v___f_1093_, v_a_968_, v_a_969_, v_a_970_);
lean_dec(v_var_1088_);
return v___x_1094_;
}
case 13:
{
lean_object* v_ty_1095_; lean_object* v_fvarId_1096_; lean_object* v___f_1097_; lean_object* v___x_1098_; 
lean_dec(v_type_975_);
v_ty_1095_ = lean_ctor_get(v_value_974_, 0);
lean_inc_ref(v_ty_1095_);
v_fvarId_1096_ = lean_ctor_get(v_value_974_, 1);
lean_inc(v_fvarId_1096_);
lean_dec_ref_known(v_value_974_, 2);
v___f_1097_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__7___boxed), 7, 2);
lean_closure_set(v___f_1097_, 0, v_ty_1095_);
lean_closure_set(v___f_1097_, 1, v_continueLet_976_);
v___x_1098_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_966_, v_k_967_, v_fvarId_1096_, v___f_1097_, v_a_968_, v_a_969_, v_a_970_);
lean_dec(v_fvarId_1096_);
return v___x_1098_;
}
case 14:
{
lean_object* v_fvarId_1099_; lean_object* v___f_1100_; lean_object* v___x_1101_; 
lean_dec(v_type_975_);
v_fvarId_1099_ = lean_ctor_get(v_value_974_, 0);
lean_inc(v_fvarId_1099_);
lean_dec_ref_known(v_value_974_, 1);
v___f_1100_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__8___boxed), 6, 1);
lean_closure_set(v___f_1100_, 0, v_continueLet_976_);
v___x_1101_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_966_, v_k_967_, v_fvarId_1099_, v___f_1100_, v_a_968_, v_a_969_, v_a_970_);
lean_dec(v_fvarId_1099_);
return v___x_1101_;
}
default: 
{
lean_object* v_fvarId_1102_; lean_object* v___f_1103_; lean_object* v___x_1104_; 
lean_dec(v_type_975_);
v_fvarId_1102_ = lean_ctor_get(v_value_974_, 0);
lean_inc(v_fvarId_1102_);
lean_dec_ref_known(v_value_974_, 1);
v___f_1103_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__9___boxed), 6, 1);
lean_closure_set(v___f_1103_, 0, v_continueLet_976_);
v___x_1104_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_966_, v_k_967_, v_fvarId_1102_, v___f_1103_, v_a_968_, v_a_969_, v_a_970_);
lean_dec(v_fvarId_1102_);
return v___x_1104_;
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__3(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1108_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__2));
v___x_1109_ = lean_unsigned_to_nat(15u);
v___x_1110_ = lean_unsigned_to_nat(128u);
v___x_1111_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1112_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1113_ = l_mkPanicMessageWithDecl(v___x_1112_, v___x_1111_, v___x_1110_, v___x_1109_, v___x_1108_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
if (lean_obj_tag(v_a_1114_) == 1)
{
lean_object* v_info_1119_; lean_object* v_code_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1156_; 
v_info_1119_ = lean_ctor_get(v_a_1114_, 0);
v_code_1120_ = lean_ctor_get(v_a_1114_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_a_1114_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1122_ = v_a_1114_;
v_isShared_1123_ = v_isSharedCheck_1156_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_code_1120_);
lean_inc(v_info_1119_);
lean_dec(v_a_1114_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1156_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_IR_ToIR_lowerCode(v_code_1120_, v_a_1115_, v_a_1116_, v_a_1117_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1147_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1147_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1147_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v_name_1129_; lean_object* v_cidx_1130_; lean_object* v_size_1131_; lean_object* v_usize_1132_; lean_object* v_ssize_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1146_; 
v_name_1129_ = lean_ctor_get(v_info_1119_, 0);
v_cidx_1130_ = lean_ctor_get(v_info_1119_, 1);
v_size_1131_ = lean_ctor_get(v_info_1119_, 2);
v_usize_1132_ = lean_ctor_get(v_info_1119_, 3);
v_ssize_1133_ = lean_ctor_get(v_info_1119_, 4);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_info_1119_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1135_ = v_info_1119_;
v_isShared_1136_ = v_isSharedCheck_1146_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_ssize_1133_);
lean_inc(v_usize_1132_);
lean_inc(v_size_1131_);
lean_inc(v_cidx_1130_);
lean_inc(v_name_1129_);
lean_dec(v_info_1119_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1146_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_name_1129_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_cidx_1130_);
lean_ctor_set(v_reuseFailAlloc_1145_, 2, v_size_1131_);
lean_ctor_set(v_reuseFailAlloc_1145_, 3, v_usize_1132_);
lean_ctor_set(v_reuseFailAlloc_1145_, 4, v_ssize_1133_);
v___x_1138_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1140_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set_tag(v___x_1122_, 0);
lean_ctor_set(v___x_1122_, 1, v_a_1125_);
lean_ctor_set(v___x_1122_, 0, v___x_1138_);
v___x_1140_ = v___x_1122_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_a_1125_);
v___x_1140_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1142_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1140_);
v___x_1142_ = v___x_1127_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_del_object(v___x_1122_);
lean_dec_ref(v_info_1119_);
v_a_1148_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1124_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1124_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
else
{
lean_object* v_code_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1181_; 
v_code_1157_ = lean_ctor_get(v_a_1114_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_a_1114_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1159_ = v_a_1114_;
v_isShared_1160_ = v_isSharedCheck_1181_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_code_1157_);
lean_dec(v_a_1114_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1181_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_IR_ToIR_lowerCode(v_code_1157_, v_a_1115_, v_a_1116_, v_a_1117_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1172_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1164_ = v___x_1161_;
v_isShared_1165_ = v_isSharedCheck_1172_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1161_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1172_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set_tag(v___x_1159_, 1);
lean_ctor_set(v___x_1159_, 0, v_a_1162_);
v___x_1167_ = v___x_1159_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1169_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1167_);
v___x_1169_ = v___x_1164_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_del_object(v___x_1159_);
v_a_1173_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1161_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1161_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(size_t v_sz_1182_, size_t v_i_1183_, lean_object* v_bs_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_usize_dec_lt(v_i_1183_, v_sz_1182_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v_bs_1184_);
return v___x_1190_;
}
else
{
lean_object* v_v_1191_; lean_object* v___x_1192_; lean_object* v_bs_x27_1193_; lean_object* v___x_1194_; 
v_v_1191_ = lean_array_uget(v_bs_1184_, v_i_1183_);
v___x_1192_ = lean_unsigned_to_nat(0u);
v_bs_x27_1193_ = lean_array_uset(v_bs_1184_, v_i_1183_, v___x_1192_);
v___x_1194_ = l_Lean_IR_ToIR_lowerAlt(v_v_1191_, v___y_1185_, v___y_1186_, v___y_1187_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; size_t v___x_1196_; size_t v___x_1197_; lean_object* v___x_1198_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v___x_1196_ = ((size_t)1ULL);
v___x_1197_ = lean_usize_add(v_i_1183_, v___x_1196_);
v___x_1198_ = lean_array_uset(v_bs_x27_1193_, v_i_1183_, v_a_1195_);
v_i_1183_ = v___x_1197_;
v_bs_1184_ = v___x_1198_;
goto _start;
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v_bs_x27_1193_);
v_a_1200_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1194_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1194_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__5(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1209_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1210_ = lean_unsigned_to_nat(53u);
v___x_1211_ = lean_unsigned_to_nat(95u);
v___x_1212_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1213_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1214_ = l_mkPanicMessageWithDecl(v___x_1213_, v___x_1212_, v___x_1211_, v___x_1210_, v___x_1209_);
return v___x_1214_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__6(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1215_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1216_ = lean_unsigned_to_nat(44u);
v___x_1217_ = lean_unsigned_to_nat(106u);
v___x_1218_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1219_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1220_ = l_mkPanicMessageWithDecl(v___x_1219_, v___x_1218_, v___x_1217_, v___x_1216_, v___x_1215_);
return v___x_1220_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__7(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1221_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1222_ = lean_unsigned_to_nat(44u);
v___x_1223_ = lean_unsigned_to_nat(114u);
v___x_1224_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1225_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1226_ = l_mkPanicMessageWithDecl(v___x_1225_, v___x_1224_, v___x_1223_, v___x_1222_, v___x_1221_);
return v___x_1226_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__8(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1227_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1228_ = lean_unsigned_to_nat(34u);
v___x_1229_ = lean_unsigned_to_nat(113u);
v___x_1230_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1231_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1232_ = l_mkPanicMessageWithDecl(v___x_1231_, v___x_1230_, v___x_1229_, v___x_1228_, v___x_1227_);
return v___x_1232_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__9(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1233_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1234_ = lean_unsigned_to_nat(44u);
v___x_1235_ = lean_unsigned_to_nat(110u);
v___x_1236_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1237_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1238_ = l_mkPanicMessageWithDecl(v___x_1237_, v___x_1236_, v___x_1235_, v___x_1234_, v___x_1233_);
return v___x_1238_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__10(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1239_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1240_ = lean_unsigned_to_nat(34u);
v___x_1241_ = lean_unsigned_to_nat(109u);
v___x_1242_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1243_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1244_ = l_mkPanicMessageWithDecl(v___x_1243_, v___x_1242_, v___x_1241_, v___x_1240_, v___x_1239_);
return v___x_1244_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__11(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1245_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1246_ = lean_unsigned_to_nat(41u);
v___x_1247_ = lean_unsigned_to_nat(117u);
v___x_1248_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1249_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1250_ = l_mkPanicMessageWithDecl(v___x_1249_, v___x_1248_, v___x_1247_, v___x_1246_, v___x_1245_);
return v___x_1250_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__12(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1251_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1252_ = lean_unsigned_to_nat(41u);
v___x_1253_ = lean_unsigned_to_nat(120u);
v___x_1254_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1255_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1256_ = l_mkPanicMessageWithDecl(v___x_1255_, v___x_1254_, v___x_1253_, v___x_1252_, v___x_1251_);
return v___x_1256_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__13(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1257_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1258_ = lean_unsigned_to_nat(41u);
v___x_1259_ = lean_unsigned_to_nat(123u);
v___x_1260_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1261_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1262_ = l_mkPanicMessageWithDecl(v___x_1261_, v___x_1260_, v___x_1259_, v___x_1258_, v___x_1257_);
return v___x_1262_;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__14(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1263_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__4));
v___x_1264_ = lean_unsigned_to_nat(41u);
v___x_1265_ = lean_unsigned_to_nat(126u);
v___x_1266_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__1));
v___x_1267_ = ((lean_object*)(l_Lean_IR_ToIR_lowerCode___closed__0));
v___x_1268_ = l_mkPanicMessageWithDecl(v___x_1267_, v___x_1266_, v___x_1265_, v___x_1264_, v___x_1263_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object* v_c_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
switch(lean_obj_tag(v_c_1269_))
{
case 0:
{
lean_object* v_decl_1274_; lean_object* v_k_1275_; lean_object* v___x_1276_; 
v_decl_1274_ = lean_ctor_get(v_c_1269_, 0);
lean_inc_ref(v_decl_1274_);
v_k_1275_ = lean_ctor_get(v_c_1269_, 1);
lean_inc_ref(v_k_1275_);
lean_dec_ref_known(v_c_1269_, 2);
v___x_1276_ = l_Lean_IR_ToIR_lowerLet(v_decl_1274_, v_k_1275_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1276_;
}
case 1:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec_ref_known(v_c_1269_, 2);
v___x_1277_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__3, &l_Lean_IR_ToIR_lowerCode___closed__3_once, _init_l_Lean_IR_ToIR_lowerCode___closed__3);
v___x_1278_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1277_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1278_;
}
case 2:
{
lean_object* v_decl_1279_; lean_object* v_k_1280_; lean_object* v_fvarId_1281_; lean_object* v_params_1282_; lean_object* v_value_1283_; lean_object* v___x_1284_; 
v_decl_1279_ = lean_ctor_get(v_c_1269_, 0);
lean_inc_ref(v_decl_1279_);
v_k_1280_ = lean_ctor_get(v_c_1269_, 1);
lean_inc_ref(v_k_1280_);
lean_dec_ref_known(v_c_1269_, 2);
v_fvarId_1281_ = lean_ctor_get(v_decl_1279_, 0);
lean_inc(v_fvarId_1281_);
v_params_1282_ = lean_ctor_get(v_decl_1279_, 2);
lean_inc_ref(v_params_1282_);
v_value_1283_ = lean_ctor_get(v_decl_1279_, 4);
lean_inc_ref(v_value_1283_);
lean_dec_ref(v_decl_1279_);
v___x_1284_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_1281_, v_a_1270_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; size_t v_sz_1286_; size_t v___x_1287_; lean_object* v___x_1288_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v_sz_1286_ = lean_array_size(v_params_1282_);
v___x_1287_ = ((size_t)0ULL);
v___x_1288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1286_, v___x_1287_, v_params_1282_, v_a_1270_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v___x_1290_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___x_1288_, 1);
v___x_1290_ = l_Lean_IR_ToIR_lowerCode(v_value_1283_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1292_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1290_, 1);
v___x_1292_ = l_Lean_IR_ToIR_lowerCode(v_k_1280_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1301_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1301_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1301_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1297_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1297_, 0, v_a_1285_);
lean_ctor_set(v___x_1297_, 1, v_a_1289_);
lean_ctor_set(v___x_1297_, 2, v_a_1291_);
lean_ctor_set(v___x_1297_, 3, v_a_1293_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1297_);
v___x_1299_ = v___x_1295_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
else
{
lean_dec(v_a_1291_);
lean_dec(v_a_1289_);
lean_dec(v_a_1285_);
return v___x_1292_;
}
}
else
{
lean_dec(v_a_1289_);
lean_dec(v_a_1285_);
lean_dec_ref(v_k_1280_);
return v___x_1290_;
}
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec(v_a_1285_);
lean_dec_ref(v_value_1283_);
lean_dec_ref(v_k_1280_);
v_a_1302_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1288_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1288_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec_ref(v_value_1283_);
lean_dec_ref(v_params_1282_);
lean_dec_ref(v_k_1280_);
v_a_1310_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1284_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1284_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_1318_; lean_object* v_args_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1355_; 
v_fvarId_1318_ = lean_ctor_get(v_c_1269_, 0);
v_args_1319_ = lean_ctor_get(v_c_1269_, 1);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_c_1269_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1321_ = v_c_1269_;
v_isShared_1322_ = v_isSharedCheck_1355_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_args_1319_);
lean_inc(v_fvarId_1318_);
lean_dec(v_c_1269_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1355_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_1318_, v_a_1270_);
lean_dec(v_fvarId_1318_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; size_t v_sz_1325_; size_t v___x_1326_; lean_object* v___x_1327_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
lean_dec_ref_known(v___x_1323_, 1);
v_sz_1325_ = lean_array_size(v_args_1319_);
v___x_1326_ = ((size_t)0ULL);
v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1325_, v___x_1326_, v_args_1319_, v_a_1270_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1338_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1338_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1338_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1322_ == 0)
{
lean_ctor_set_tag(v___x_1321_, 11);
lean_ctor_set(v___x_1321_, 1, v_a_1328_);
lean_ctor_set(v___x_1321_, 0, v_a_1324_);
v___x_1333_ = v___x_1321_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1324_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1335_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v___x_1333_);
v___x_1335_ = v___x_1330_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec(v_a_1324_);
lean_del_object(v___x_1321_);
v_a_1339_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1327_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1327_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
lean_del_object(v___x_1321_);
lean_dec_ref(v_args_1319_);
v_a_1347_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1323_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1323_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
case 4:
{
lean_object* v_cases_1356_; lean_object* v_typeName_1357_; lean_object* v_discr_1358_; lean_object* v_alts_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1399_; 
v_cases_1356_ = lean_ctor_get(v_c_1269_, 0);
lean_inc_ref(v_cases_1356_);
lean_dec_ref_known(v_c_1269_, 1);
v_typeName_1357_ = lean_ctor_get(v_cases_1356_, 0);
v_discr_1358_ = lean_ctor_get(v_cases_1356_, 2);
v_alts_1359_ = lean_ctor_get(v_cases_1356_, 3);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_cases_1356_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; 
v_unused_1400_ = lean_ctor_get(v_cases_1356_, 1);
lean_dec(v_unused_1400_);
v___x_1361_ = v_cases_1356_;
v_isShared_1362_ = v_isSharedCheck_1399_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_alts_1359_);
lean_inc(v_discr_1358_);
lean_inc(v_typeName_1357_);
lean_dec(v_cases_1356_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1399_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_discr_1358_, v_a_1270_);
lean_dec(v_discr_1358_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v___x_1363_, 1);
if (lean_obj_tag(v_a_1364_) == 0)
{
lean_object* v_id_1365_; size_t v_sz_1366_; size_t v___x_1367_; lean_object* v___x_1368_; 
v_id_1365_ = lean_ctor_get(v_a_1364_, 0);
lean_inc(v_id_1365_);
lean_dec_ref_known(v_a_1364_, 1);
v_sz_1366_ = lean_array_size(v_alts_1359_);
v___x_1367_ = ((size_t)0ULL);
v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_1366_, v___x_1367_, v_alts_1359_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1380_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1380_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1380_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1373_ = l_Lean_IR_nameToIRType(v_typeName_1357_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set_tag(v___x_1361_, 9);
lean_ctor_set(v___x_1361_, 3, v_a_1369_);
lean_ctor_set(v___x_1361_, 2, v___x_1373_);
lean_ctor_set(v___x_1361_, 1, v_id_1365_);
v___x_1375_ = v___x_1361_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_typeName_1357_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_id_1365_);
lean_ctor_set(v_reuseFailAlloc_1379_, 2, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1379_, 3, v_a_1369_);
v___x_1375_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1377_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1375_);
v___x_1377_ = v___x_1371_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec(v_id_1365_);
lean_del_object(v___x_1361_);
lean_dec(v_typeName_1357_);
v_a_1381_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1368_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1368_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_dec(v_a_1364_);
lean_del_object(v___x_1361_);
lean_dec_ref(v_alts_1359_);
lean_dec(v_typeName_1357_);
v___x_1389_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__5, &l_Lean_IR_ToIR_lowerCode___closed__5_once, _init_l_Lean_IR_ToIR_lowerCode___closed__5);
v___x_1390_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1389_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1390_;
}
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_del_object(v___x_1361_);
lean_dec_ref(v_alts_1359_);
lean_dec(v_typeName_1357_);
v_a_1391_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1363_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1363_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1425_; 
v_fvarId_1401_ = lean_ctor_get(v_c_1269_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_c_1269_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1403_ = v_c_1269_;
v_isShared_1404_ = v_isSharedCheck_1425_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_fvarId_1401_);
lean_dec(v_c_1269_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1425_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1401_, v_a_1270_);
lean_dec(v_fvarId_1401_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1416_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1416_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1416_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1404_ == 0)
{
lean_ctor_set_tag(v___x_1403_, 10);
lean_ctor_set(v___x_1403_, 0, v_a_1406_);
v___x_1411_ = v___x_1403_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1413_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1411_);
v___x_1413_ = v___x_1408_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_del_object(v___x_1403_);
v_a_1417_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1405_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1405_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
case 6:
{
lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1433_; 
v_isSharedCheck_1433_ = !lean_is_exclusive(v_c_1269_);
if (v_isSharedCheck_1433_ == 0)
{
lean_object* v_unused_1434_; 
v_unused_1434_ = lean_ctor_get(v_c_1269_, 0);
lean_dec(v_unused_1434_);
v___x_1427_ = v_c_1269_;
v_isShared_1428_ = v_isSharedCheck_1433_;
goto v_resetjp_1426_;
}
else
{
lean_dec(v_c_1269_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1433_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1429_ = lean_box(12);
if (v_isShared_1428_ == 0)
{
lean_ctor_set_tag(v___x_1427_, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1429_);
v___x_1431_ = v___x_1427_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
case 7:
{
lean_object* v_fvarId_1435_; lean_object* v_i_1436_; lean_object* v_y_1437_; lean_object* v_k_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1477_; 
v_fvarId_1435_ = lean_ctor_get(v_c_1269_, 0);
v_i_1436_ = lean_ctor_get(v_c_1269_, 1);
v_y_1437_ = lean_ctor_get(v_c_1269_, 2);
v_k_1438_ = lean_ctor_get(v_c_1269_, 3);
v_isSharedCheck_1477_ = !lean_is_exclusive(v_c_1269_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1440_ = v_c_1269_;
v_isShared_1441_ = v_isSharedCheck_1477_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_k_1438_);
lean_inc(v_y_1437_);
lean_inc(v_i_1436_);
lean_inc(v_fvarId_1435_);
lean_dec(v_c_1269_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1477_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_IR_ToIR_lowerArg___redArg(v_y_1437_, v_a_1270_);
lean_dec(v_y_1437_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1444_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
lean_dec_ref_known(v___x_1442_, 1);
v___x_1444_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1435_, v_a_1270_);
lean_dec(v_fvarId_1435_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
if (lean_obj_tag(v_a_1445_) == 0)
{
lean_object* v_id_1446_; lean_object* v___x_1447_; 
v_id_1446_ = lean_ctor_get(v_a_1445_, 0);
lean_inc(v_id_1446_);
lean_dec_ref_known(v_a_1445_, 1);
v___x_1447_ = l_Lean_IR_ToIR_lowerCode(v_k_1438_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1458_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1458_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1458_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set_tag(v___x_1440_, 2);
lean_ctor_set(v___x_1440_, 3, v_a_1448_);
lean_ctor_set(v___x_1440_, 2, v_a_1443_);
lean_ctor_set(v___x_1440_, 0, v_id_1446_);
v___x_1453_ = v___x_1440_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_id_1446_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_i_1436_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_a_1443_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1455_; 
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1453_);
v___x_1455_ = v___x_1450_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
else
{
lean_dec(v_id_1446_);
lean_dec(v_a_1443_);
lean_del_object(v___x_1440_);
lean_dec(v_i_1436_);
return v___x_1447_;
}
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
lean_dec(v_a_1445_);
lean_dec(v_a_1443_);
lean_del_object(v___x_1440_);
lean_dec_ref(v_k_1438_);
lean_dec(v_i_1436_);
v___x_1459_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__6, &l_Lean_IR_ToIR_lowerCode___closed__6_once, _init_l_Lean_IR_ToIR_lowerCode___closed__6);
v___x_1460_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1459_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1460_;
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec(v_a_1443_);
lean_del_object(v___x_1440_);
lean_dec_ref(v_k_1438_);
lean_dec(v_i_1436_);
v_a_1461_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1444_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1444_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_del_object(v___x_1440_);
lean_dec_ref(v_k_1438_);
lean_dec(v_i_1436_);
lean_dec(v_fvarId_1435_);
v_a_1469_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1442_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1442_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
case 8:
{
lean_object* v_fvarId_1478_; lean_object* v_i_1479_; lean_object* v_y_1480_; lean_object* v_k_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1523_; 
v_fvarId_1478_ = lean_ctor_get(v_c_1269_, 0);
v_i_1479_ = lean_ctor_get(v_c_1269_, 1);
v_y_1480_ = lean_ctor_get(v_c_1269_, 2);
v_k_1481_ = lean_ctor_get(v_c_1269_, 3);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_c_1269_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1483_ = v_c_1269_;
v_isShared_1484_ = v_isSharedCheck_1523_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_k_1481_);
lean_inc(v_y_1480_);
lean_inc(v_i_1479_);
lean_inc(v_fvarId_1478_);
lean_dec(v_c_1269_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1523_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1480_, v_a_1270_);
lean_dec(v_y_1480_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___x_1485_, 1);
if (lean_obj_tag(v_a_1486_) == 0)
{
lean_object* v_id_1487_; lean_object* v___x_1488_; 
v_id_1487_ = lean_ctor_get(v_a_1486_, 0);
lean_inc(v_id_1487_);
lean_dec_ref_known(v_a_1486_, 1);
v___x_1488_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1478_, v_a_1270_);
lean_dec(v_fvarId_1478_);
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
v___x_1491_ = l_Lean_IR_ToIR_lowerCode(v_k_1481_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1502_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1494_ = v___x_1491_;
v_isShared_1495_ = v_isSharedCheck_1502_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1502_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set_tag(v___x_1483_, 4);
lean_ctor_set(v___x_1483_, 3, v_a_1492_);
lean_ctor_set(v___x_1483_, 2, v_id_1487_);
lean_ctor_set(v___x_1483_, 0, v_id_1490_);
v___x_1497_ = v___x_1483_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_id_1490_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_i_1479_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_id_1487_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1499_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v___x_1497_);
v___x_1499_ = v___x_1494_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1497_);
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
else
{
lean_dec(v_id_1490_);
lean_dec(v_id_1487_);
lean_del_object(v___x_1483_);
lean_dec(v_i_1479_);
return v___x_1491_;
}
}
else
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec(v_a_1489_);
lean_dec(v_id_1487_);
lean_del_object(v___x_1483_);
lean_dec_ref(v_k_1481_);
lean_dec(v_i_1479_);
v___x_1503_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__7, &l_Lean_IR_ToIR_lowerCode___closed__7_once, _init_l_Lean_IR_ToIR_lowerCode___closed__7);
v___x_1504_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1503_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1504_;
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec(v_id_1487_);
lean_del_object(v___x_1483_);
lean_dec_ref(v_k_1481_);
lean_dec(v_i_1479_);
v_a_1505_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1488_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1488_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
else
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec(v_a_1486_);
lean_del_object(v___x_1483_);
lean_dec_ref(v_k_1481_);
lean_dec(v_i_1479_);
lean_dec(v_fvarId_1478_);
v___x_1513_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__8, &l_Lean_IR_ToIR_lowerCode___closed__8_once, _init_l_Lean_IR_ToIR_lowerCode___closed__8);
v___x_1514_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1513_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1514_;
}
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_del_object(v___x_1483_);
lean_dec_ref(v_k_1481_);
lean_dec(v_i_1479_);
lean_dec(v_fvarId_1478_);
v_a_1515_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1485_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1485_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
case 9:
{
lean_object* v_fvarId_1524_; lean_object* v_i_1525_; lean_object* v_offset_1526_; lean_object* v_y_1527_; lean_object* v_ty_1528_; lean_object* v_k_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1572_; 
v_fvarId_1524_ = lean_ctor_get(v_c_1269_, 0);
v_i_1525_ = lean_ctor_get(v_c_1269_, 1);
v_offset_1526_ = lean_ctor_get(v_c_1269_, 2);
v_y_1527_ = lean_ctor_get(v_c_1269_, 3);
v_ty_1528_ = lean_ctor_get(v_c_1269_, 4);
v_k_1529_ = lean_ctor_get(v_c_1269_, 5);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_c_1269_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1531_ = v_c_1269_;
v_isShared_1532_ = v_isSharedCheck_1572_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_k_1529_);
lean_inc(v_ty_1528_);
lean_inc(v_y_1527_);
lean_inc(v_offset_1526_);
lean_inc(v_i_1525_);
lean_inc(v_fvarId_1524_);
lean_dec(v_c_1269_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1572_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_1527_, v_a_1270_);
lean_dec(v_y_1527_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1533_, 1);
if (lean_obj_tag(v_a_1534_) == 0)
{
lean_object* v_id_1535_; lean_object* v___x_1536_; 
v_id_1535_ = lean_ctor_get(v_a_1534_, 0);
lean_inc(v_id_1535_);
lean_dec_ref_known(v_a_1534_, 1);
v___x_1536_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1524_, v_a_1270_);
lean_dec(v_fvarId_1524_);
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
v___x_1539_ = l_Lean_IR_ToIR_lowerCode(v_k_1529_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1551_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1551_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1551_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1544_ = l_Lean_IR_toIRType(v_ty_1528_);
lean_dec_ref(v_ty_1528_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set_tag(v___x_1531_, 5);
lean_ctor_set(v___x_1531_, 5, v_a_1540_);
lean_ctor_set(v___x_1531_, 4, v___x_1544_);
lean_ctor_set(v___x_1531_, 3, v_id_1535_);
lean_ctor_set(v___x_1531_, 0, v_id_1538_);
v___x_1546_ = v___x_1531_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_id_1538_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_i_1525_);
lean_ctor_set(v_reuseFailAlloc_1550_, 2, v_offset_1526_);
lean_ctor_set(v_reuseFailAlloc_1550_, 3, v_id_1535_);
lean_ctor_set(v_reuseFailAlloc_1550_, 4, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1550_, 5, v_a_1540_);
v___x_1546_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1548_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1546_);
v___x_1548_ = v___x_1542_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1546_);
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
else
{
lean_dec(v_id_1538_);
lean_dec(v_id_1535_);
lean_del_object(v___x_1531_);
lean_dec_ref(v_ty_1528_);
lean_dec(v_offset_1526_);
lean_dec(v_i_1525_);
return v___x_1539_;
}
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
lean_dec(v_a_1537_);
lean_dec(v_id_1535_);
lean_del_object(v___x_1531_);
lean_dec_ref(v_k_1529_);
lean_dec_ref(v_ty_1528_);
lean_dec(v_offset_1526_);
lean_dec(v_i_1525_);
v___x_1552_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__9, &l_Lean_IR_ToIR_lowerCode___closed__9_once, _init_l_Lean_IR_ToIR_lowerCode___closed__9);
v___x_1553_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1552_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1553_;
}
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_dec(v_id_1535_);
lean_del_object(v___x_1531_);
lean_dec_ref(v_k_1529_);
lean_dec_ref(v_ty_1528_);
lean_dec(v_offset_1526_);
lean_dec(v_i_1525_);
v_a_1554_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1536_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1536_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec(v_a_1534_);
lean_del_object(v___x_1531_);
lean_dec_ref(v_k_1529_);
lean_dec_ref(v_ty_1528_);
lean_dec(v_offset_1526_);
lean_dec(v_i_1525_);
lean_dec(v_fvarId_1524_);
v___x_1562_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__10, &l_Lean_IR_ToIR_lowerCode___closed__10_once, _init_l_Lean_IR_ToIR_lowerCode___closed__10);
v___x_1563_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1562_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1563_;
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_del_object(v___x_1531_);
lean_dec_ref(v_k_1529_);
lean_dec_ref(v_ty_1528_);
lean_dec(v_offset_1526_);
lean_dec(v_i_1525_);
lean_dec(v_fvarId_1524_);
v_a_1564_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1533_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1533_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
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
}
case 10:
{
lean_object* v_fvarId_1573_; lean_object* v_cidx_1574_; lean_object* v_k_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1604_; 
v_fvarId_1573_ = lean_ctor_get(v_c_1269_, 0);
v_cidx_1574_ = lean_ctor_get(v_c_1269_, 1);
v_k_1575_ = lean_ctor_get(v_c_1269_, 2);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_c_1269_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1577_ = v_c_1269_;
v_isShared_1578_ = v_isSharedCheck_1604_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_k_1575_);
lean_inc(v_cidx_1574_);
lean_inc(v_fvarId_1573_);
lean_dec(v_c_1269_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1604_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1573_, v_a_1270_);
lean_dec(v_fvarId_1573_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
if (lean_obj_tag(v_a_1580_) == 0)
{
lean_object* v_id_1581_; lean_object* v___x_1582_; 
v_id_1581_ = lean_ctor_get(v_a_1580_, 0);
lean_inc(v_id_1581_);
lean_dec_ref_known(v_a_1580_, 1);
v___x_1582_ = l_Lean_IR_ToIR_lowerCode(v_k_1575_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1593_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1593_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1593_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1578_ == 0)
{
lean_ctor_set_tag(v___x_1577_, 3);
lean_ctor_set(v___x_1577_, 2, v_a_1583_);
lean_ctor_set(v___x_1577_, 0, v_id_1581_);
v___x_1588_ = v___x_1577_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_id_1581_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_cidx_1574_);
lean_ctor_set(v_reuseFailAlloc_1592_, 2, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1590_; 
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v___x_1588_);
v___x_1590_ = v___x_1585_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
else
{
lean_dec(v_id_1581_);
lean_del_object(v___x_1577_);
lean_dec(v_cidx_1574_);
return v___x_1582_;
}
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_dec(v_a_1580_);
lean_del_object(v___x_1577_);
lean_dec_ref(v_k_1575_);
lean_dec(v_cidx_1574_);
v___x_1594_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__11, &l_Lean_IR_ToIR_lowerCode___closed__11_once, _init_l_Lean_IR_ToIR_lowerCode___closed__11);
v___x_1595_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1594_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1595_;
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_del_object(v___x_1577_);
lean_dec_ref(v_k_1575_);
lean_dec(v_cidx_1574_);
v_a_1596_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1579_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1579_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
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
}
case 11:
{
lean_object* v_fvarId_1605_; lean_object* v_n_1606_; uint8_t v_check_1607_; uint8_t v_persistent_1608_; lean_object* v_k_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1638_; 
v_fvarId_1605_ = lean_ctor_get(v_c_1269_, 0);
v_n_1606_ = lean_ctor_get(v_c_1269_, 1);
v_check_1607_ = lean_ctor_get_uint8(v_c_1269_, sizeof(void*)*3);
v_persistent_1608_ = lean_ctor_get_uint8(v_c_1269_, sizeof(void*)*3 + 1);
v_k_1609_ = lean_ctor_get(v_c_1269_, 2);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_c_1269_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1611_ = v_c_1269_;
v_isShared_1612_ = v_isSharedCheck_1638_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_k_1609_);
lean_inc(v_n_1606_);
lean_inc(v_fvarId_1605_);
lean_dec(v_c_1269_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1638_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1605_, v_a_1270_);
lean_dec(v_fvarId_1605_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
if (lean_obj_tag(v_a_1614_) == 0)
{
lean_object* v_id_1615_; lean_object* v___x_1616_; 
v_id_1615_ = lean_ctor_get(v_a_1614_, 0);
lean_inc(v_id_1615_);
lean_dec_ref_known(v_a_1614_, 1);
v___x_1616_ = l_Lean_IR_ToIR_lowerCode(v_k_1609_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1627_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1627_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1627_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1612_ == 0)
{
lean_ctor_set_tag(v___x_1611_, 6);
lean_ctor_set(v___x_1611_, 2, v_a_1617_);
lean_ctor_set(v___x_1611_, 0, v_id_1615_);
v___x_1622_ = v___x_1611_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_id_1615_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_n_1606_);
lean_ctor_set(v_reuseFailAlloc_1626_, 2, v_a_1617_);
lean_ctor_set_uint8(v_reuseFailAlloc_1626_, sizeof(void*)*3, v_check_1607_);
lean_ctor_set_uint8(v_reuseFailAlloc_1626_, sizeof(void*)*3 + 1, v_persistent_1608_);
v___x_1622_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1624_; 
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v___x_1622_);
v___x_1624_ = v___x_1619_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1622_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
else
{
lean_dec(v_id_1615_);
lean_del_object(v___x_1611_);
lean_dec(v_n_1606_);
return v___x_1616_;
}
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec(v_a_1614_);
lean_del_object(v___x_1611_);
lean_dec_ref(v_k_1609_);
lean_dec(v_n_1606_);
v___x_1628_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__12, &l_Lean_IR_ToIR_lowerCode___closed__12_once, _init_l_Lean_IR_ToIR_lowerCode___closed__12);
v___x_1629_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1628_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1629_;
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_del_object(v___x_1611_);
lean_dec_ref(v_k_1609_);
lean_dec(v_n_1606_);
v_a_1630_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1613_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1613_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
case 12:
{
lean_object* v_fvarId_1639_; lean_object* v_n_1640_; uint8_t v_check_1641_; uint8_t v_persistent_1642_; lean_object* v_k_1643_; lean_object* v___x_1644_; 
v_fvarId_1639_ = lean_ctor_get(v_c_1269_, 0);
lean_inc(v_fvarId_1639_);
v_n_1640_ = lean_ctor_get(v_c_1269_, 1);
lean_inc(v_n_1640_);
v_check_1641_ = lean_ctor_get_uint8(v_c_1269_, sizeof(void*)*4);
v_persistent_1642_ = lean_ctor_get_uint8(v_c_1269_, sizeof(void*)*4 + 1);
v_k_1643_ = lean_ctor_get(v_c_1269_, 3);
lean_inc_ref(v_k_1643_);
lean_dec_ref_known(v_c_1269_, 4);
v___x_1644_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1639_, v_a_1270_);
lean_dec(v_fvarId_1639_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v___x_1644_, 1);
if (lean_obj_tag(v_a_1645_) == 0)
{
lean_object* v_id_1646_; lean_object* v___x_1647_; 
v_id_1646_ = lean_ctor_get(v_a_1645_, 0);
lean_inc(v_id_1646_);
lean_dec_ref_known(v_a_1645_, 1);
v___x_1647_ = l_Lean_IR_ToIR_lowerCode(v_k_1643_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1656_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1656_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1656_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1652_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v___x_1652_, 0, v_id_1646_);
lean_ctor_set(v___x_1652_, 1, v_n_1640_);
lean_ctor_set(v___x_1652_, 2, v_a_1648_);
lean_ctor_set_uint8(v___x_1652_, sizeof(void*)*3, v_check_1641_);
lean_ctor_set_uint8(v___x_1652_, sizeof(void*)*3 + 1, v_persistent_1642_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1652_);
v___x_1654_ = v___x_1650_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
else
{
lean_dec(v_id_1646_);
lean_dec(v_n_1640_);
return v___x_1647_;
}
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
lean_dec(v_a_1645_);
lean_dec_ref(v_k_1643_);
lean_dec(v_n_1640_);
v___x_1657_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__13, &l_Lean_IR_ToIR_lowerCode___closed__13_once, _init_l_Lean_IR_ToIR_lowerCode___closed__13);
v___x_1658_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1657_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1658_;
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec_ref(v_k_1643_);
lean_dec(v_n_1640_);
v_a_1659_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1644_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1644_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
default: 
{
lean_object* v_fvarId_1667_; lean_object* v_k_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1697_; 
v_fvarId_1667_ = lean_ctor_get(v_c_1269_, 0);
v_k_1668_ = lean_ctor_get(v_c_1269_, 1);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_c_1269_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1670_ = v_c_1269_;
v_isShared_1671_ = v_isSharedCheck_1697_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_k_1668_);
lean_inc(v_fvarId_1667_);
lean_dec(v_c_1269_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1697_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_1667_, v_a_1270_);
lean_dec(v_fvarId_1667_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_a_1673_);
lean_dec_ref_known(v___x_1672_, 1);
if (lean_obj_tag(v_a_1673_) == 0)
{
lean_object* v_id_1674_; lean_object* v___x_1675_; 
v_id_1674_ = lean_ctor_get(v_a_1673_, 0);
lean_inc(v_id_1674_);
lean_dec_ref_known(v_a_1673_, 1);
v___x_1675_ = l_Lean_IR_ToIR_lowerCode(v_k_1668_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1686_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1678_ = v___x_1675_;
v_isShared_1679_ = v_isSharedCheck_1686_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1675_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1686_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set_tag(v___x_1670_, 8);
lean_ctor_set(v___x_1670_, 1, v_a_1676_);
lean_ctor_set(v___x_1670_, 0, v_id_1674_);
v___x_1681_ = v___x_1670_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_id_1674_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1683_; 
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1681_);
v___x_1683_ = v___x_1678_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
else
{
lean_dec(v_id_1674_);
lean_del_object(v___x_1670_);
return v___x_1675_;
}
}
else
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_dec(v_a_1673_);
lean_del_object(v___x_1670_);
lean_dec_ref(v_k_1668_);
v___x_1687_ = lean_obj_once(&l_Lean_IR_ToIR_lowerCode___closed__14, &l_Lean_IR_ToIR_lowerCode___closed__14_once, _init_l_Lean_IR_ToIR_lowerCode___closed__14);
v___x_1688_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(v___x_1687_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1688_;
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_del_object(v___x_1670_);
lean_dec_ref(v_k_1668_);
v_a_1689_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1672_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1672_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object* v_decl_1698_, lean_object* v_k_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v_fvarId_1704_; lean_object* v___x_1705_; 
v_fvarId_1704_ = lean_ctor_get(v_decl_1698_, 0);
lean_inc(v_fvarId_1704_);
lean_dec_ref(v_decl_1698_);
v___x_1705_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_1704_, v_a_1700_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v___x_1706_; 
lean_dec_ref_known(v___x_1705_, 1);
v___x_1706_ = l_Lean_IR_ToIR_lowerCode(v_k_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
return v___x_1706_;
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec_ref(v_k_1699_);
v_a_1707_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1705_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1705_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg___boxed(lean_object* v_decl_1715_, lean_object* v_k_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1715_, v_k_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue___boxed(lean_object* v_decl_1722_, lean_object* v_k_1723_, lean_object* v_fvarId_1724_, lean_object* v_f_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_1722_, v_k_1723_, v_fvarId_1724_, v_f_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_a_1726_);
lean_dec(v_fvarId_1724_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4___boxed(lean_object* v_sz_1731_, lean_object* v_i_1732_, lean_object* v_bs_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
size_t v_sz_boxed_1738_; size_t v_i_boxed_1739_; lean_object* v_res_1740_; 
v_sz_boxed_1738_ = lean_unbox_usize(v_sz_1731_);
lean_dec(v_sz_1731_);
v_i_boxed_1739_ = lean_unbox_usize(v_i_1732_);
lean_dec(v_i_1732_);
v_res_1740_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_boxed_1738_, v_i_boxed_1739_, v_bs_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt___boxed(lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_IR_ToIR_lowerAlt(v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
lean_dec(v_a_1742_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___boxed(lean_object* v_decl_1747_, lean_object* v_k_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_IR_ToIR_lowerLet(v_decl_1747_, v_k_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
lean_dec(v_a_1749_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode___boxed(lean_object* v_c_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_IR_ToIR_lowerCode(v_c_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object* v_decl_1760_, lean_object* v_k_1761_, lean_object* v_x_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_1760_, v_k_1761_, v_a_1763_, v_a_1764_, v_a_1765_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object* v_decl_1768_, lean_object* v_k_1769_, lean_object* v_x_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(v_decl_1768_, v_k_1769_, v_x_1770_, v_a_1771_, v_a_1772_, v_a_1773_);
lean_dec(v_a_1773_);
lean_dec_ref(v_a_1772_);
lean_dec(v_a_1771_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(size_t v_sz_1776_, size_t v_i_1777_, lean_object* v_bs_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1776_, v_i_1777_, v_bs_1778_, v___y_1779_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object* v_sz_1784_, lean_object* v_i_1785_, lean_object* v_bs_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
size_t v_sz_boxed_1791_; size_t v_i_boxed_1792_; lean_object* v_res_1793_; 
v_sz_boxed_1791_ = lean_unbox_usize(v_sz_1784_);
lean_dec(v_sz_1784_);
v_i_boxed_1792_ = lean_unbox_usize(v_i_1785_);
lean_dec(v_i_1785_);
v_res_1793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(v_sz_boxed_1791_, v_i_boxed_1792_, v_bs_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(size_t v_sz_1794_, size_t v_i_1795_, lean_object* v_bs_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_1794_, v_i_1795_, v_bs_1796_, v___y_1797_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object* v_sz_1802_, lean_object* v_i_1803_, lean_object* v_bs_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
size_t v_sz_boxed_1809_; size_t v_i_boxed_1810_; lean_object* v_res_1811_; 
v_sz_boxed_1809_ = lean_unbox_usize(v_sz_1802_);
lean_dec(v_sz_1802_);
v_i_boxed_1810_ = lean_unbox_usize(v_i_1803_);
lean_dec(v_i_1803_);
v_res_1811_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(v_sz_boxed_1809_, v_i_boxed_1810_, v_bs_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object* v_d_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v_toSignature_1817_; lean_object* v_value_1818_; lean_object* v_name_1819_; lean_object* v_type_1820_; lean_object* v_params_1821_; size_t v_sz_1822_; size_t v___x_1823_; lean_object* v___x_1824_; 
v_toSignature_1817_ = lean_ctor_get(v_d_1812_, 0);
lean_inc_ref(v_toSignature_1817_);
v_value_1818_ = lean_ctor_get(v_d_1812_, 1);
lean_inc_ref(v_value_1818_);
lean_dec_ref(v_d_1812_);
v_name_1819_ = lean_ctor_get(v_toSignature_1817_, 0);
lean_inc(v_name_1819_);
v_type_1820_ = lean_ctor_get(v_toSignature_1817_, 2);
lean_inc_ref(v_type_1820_);
v_params_1821_ = lean_ctor_get(v_toSignature_1817_, 3);
lean_inc_ref(v_params_1821_);
lean_dec_ref(v_toSignature_1817_);
v_sz_1822_ = lean_array_size(v_params_1821_);
v___x_1823_ = ((size_t)0ULL);
v___x_1824_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_1822_, v___x_1823_, v_params_1821_, v_a_1813_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1881_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1881_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1881_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_IR_toIRType(v_type_1820_);
lean_dec_ref(v_type_1820_);
if (lean_obj_tag(v_value_1818_) == 0)
{
lean_object* v_code_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1856_; 
lean_del_object(v___x_1827_);
v_code_1830_ = lean_ctor_get(v_value_1818_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_value_1818_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1832_ = v_value_1818_;
v_isShared_1833_ = v_isSharedCheck_1856_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_code_1830_);
lean_dec(v_value_1818_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1856_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_IR_ToIR_lowerCode(v_code_1830_, v_a_1813_, v_a_1814_, v_a_1815_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1847_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1847_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1847_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1839_ = lean_box(0);
v___x_1840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1840_, 0, v_name_1819_);
lean_ctor_set(v___x_1840_, 1, v_a_1825_);
lean_ctor_set(v___x_1840_, 2, v___x_1829_);
lean_ctor_set(v___x_1840_, 3, v_a_1835_);
lean_ctor_set(v___x_1840_, 4, v___x_1839_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set_tag(v___x_1832_, 1);
lean_ctor_set(v___x_1832_, 0, v___x_1840_);
v___x_1842_ = v___x_1832_;
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
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1842_);
v___x_1844_ = v___x_1837_;
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
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_del_object(v___x_1832_);
lean_dec(v___x_1829_);
lean_dec(v_a_1825_);
lean_dec(v_name_1819_);
v_a_1848_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1834_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1834_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
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
else
{
lean_object* v_externAttrData_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1880_; 
v_externAttrData_1857_ = lean_ctor_get(v_value_1818_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_value_1818_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1859_ = v_value_1818_;
v_isShared_1860_ = v_isSharedCheck_1880_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_externAttrData_1857_);
lean_dec(v_value_1818_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1880_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
uint8_t v___x_1861_; 
v___x_1861_ = l_List_isEmpty___redArg(v_externAttrData_1857_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1862_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1862_, 0, v_name_1819_);
lean_ctor_set(v___x_1862_, 1, v_a_1825_);
lean_ctor_set(v___x_1862_, 2, v___x_1829_);
lean_ctor_set(v___x_1862_, 3, v_externAttrData_1857_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1862_);
v___x_1864_ = v___x_1859_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1866_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1864_);
v___x_1866_ = v___x_1827_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1878_; 
lean_del_object(v___x_1859_);
lean_dec(v_externAttrData_1857_);
lean_del_object(v___x_1827_);
v___x_1869_ = l_Lean_IR_mkDummyExternDecl(v_name_1819_, v_a_1825_, v___x_1829_);
v___x_1870_ = l_Lean_IR_ToIR_addDecl___redArg(v___x_1869_, v_a_1815_);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1878_ == 0)
{
lean_object* v_unused_1879_; 
v_unused_1879_ = lean_ctor_get(v___x_1870_, 0);
lean_dec(v_unused_1879_);
v___x_1872_ = v___x_1870_;
v_isShared_1873_ = v_isSharedCheck_1878_;
goto v_resetjp_1871_;
}
else
{
lean_dec(v___x_1870_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1878_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1874_ = lean_box(0);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1874_);
v___x_1876_ = v___x_1872_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec_ref(v_type_1820_);
lean_dec(v_name_1819_);
lean_dec_ref(v_value_1818_);
v_a_1882_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1824_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1824_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl___boxed(lean_object* v_d_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_IR_ToIR_lowerDecl(v_d_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
lean_dec(v_a_1891_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(lean_object* v_as_1896_, size_t v_sz_1897_, size_t v_i_1898_, lean_object* v_b_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_a_1904_; uint8_t v___x_1908_; 
v___x_1908_ = lean_usize_dec_lt(v_i_1898_, v_sz_1897_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1909_, 0, v_b_1899_);
return v___x_1909_;
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v_a_1910_ = lean_array_uget_borrowed(v_as_1896_, v_i_1898_);
lean_inc(v_a_1910_);
v___x_1911_ = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerDecl___boxed), 5, 1);
lean_closure_set(v___x_1911_, 0, v_a_1910_);
v___x_1912_ = l_Lean_IR_ToIR_M_run___redArg(v___x_1911_, v___y_1900_, v___y_1901_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v___x_1912_, 1);
if (lean_obj_tag(v_a_1913_) == 1)
{
lean_object* v_val_1914_; lean_object* v___x_1915_; 
v_val_1914_ = lean_ctor_get(v_a_1913_, 0);
lean_inc(v_val_1914_);
lean_dec_ref_known(v_a_1913_, 1);
v___x_1915_ = lean_array_push(v_b_1899_, v_val_1914_);
v_a_1904_ = v___x_1915_;
goto v___jp_1903_;
}
else
{
lean_dec(v_a_1913_);
v_a_1904_ = v_b_1899_;
goto v___jp_1903_;
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec_ref(v_b_1899_);
v_a_1916_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1912_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1912_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
v___jp_1903_:
{
size_t v___x_1905_; size_t v___x_1906_; 
v___x_1905_ = ((size_t)1ULL);
v___x_1906_ = lean_usize_add(v_i_1898_, v___x_1905_);
v_i_1898_ = v___x_1906_;
v_b_1899_ = v_a_1904_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0___boxed(lean_object* v_as_1924_, lean_object* v_sz_1925_, lean_object* v_i_1926_, lean_object* v_b_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
size_t v_sz_boxed_1931_; size_t v_i_boxed_1932_; lean_object* v_res_1933_; 
v_sz_boxed_1931_ = lean_unbox_usize(v_sz_1925_);
lean_dec(v_sz_1925_);
v_i_boxed_1932_ = lean_unbox_usize(v_i_1926_);
lean_dec(v_i_1926_);
v_res_1933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_as_1924_, v_sz_boxed_1931_, v_i_boxed_1932_, v_b_1927_, v___y_1928_, v___y_1929_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec_ref(v_as_1924_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object* v_decls_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_){
_start:
{
lean_object* v_irDecls_1940_; size_t v_sz_1941_; size_t v___x_1942_; lean_object* v___x_1943_; 
v_irDecls_1940_ = ((lean_object*)(l_Lean_IR_toIR___closed__0));
v_sz_1941_ = lean_array_size(v_decls_1936_);
v___x_1942_ = ((size_t)0ULL);
v___x_1943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_decls_1936_, v_sz_1941_, v___x_1942_, v_irDecls_1940_, v_a_1937_, v_a_1938_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object* v_decls_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_IR_toIR(v_decls_1944_, v_a_1945_, v_a_1946_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec_ref(v_decls_1944_);
return v_res_1948_;
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
