// Lean compiler output
// Module: Lean.Attributes
// Imports: public import Lean.CoreM public import Lean.Compiler.MetaAttr
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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t l_Lean_initializing();
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedMessageData_default;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_reverse___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedAttributeApplicationTime_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedAttributeApplicationTime;
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeApplicationTime_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeApplicationTime_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqAttributeApplicationTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqAttributeApplicationTime_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqAttributeApplicationTime___closed__0 = (const lean_object*)&l_Lean_instBEqAttributeApplicationTime___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqAttributeApplicationTime = (const lean_object*)&l_Lean_instBEqAttributeApplicationTime___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instMonadLiftImportMAttrM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instMonadLiftImportMAttrM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMonadLiftImportMAttrM___closed__0 = (const lean_object*)&l_Lean_instMonadLiftImportMAttrM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instMonadLiftImportMAttrM = (const lean_object*)&l_Lean_instMonadLiftImportMAttrM___closed__0_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__0 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__1 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__2 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__2_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__3 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__3_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_1),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_2),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__4 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__4_value;
static const lean_array_object l_Lean_AttributeImplCore_ref___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__5 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__5_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__6 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__6_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_1),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_2),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__7 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__7_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__8 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__8_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__9 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__9_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__10 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__10_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_1),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_2),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__11 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__11_value;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__12;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__13;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__14 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__14_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__15 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__15_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_1),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_2),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__15_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__16 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__16_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__17 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__17_value;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__18;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__19;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__20;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__21;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__22;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__23;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__24;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__25;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__26;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__27;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__28;
LEAN_EXPORT lean_object* l_Lean_AttributeImplCore_ref___autoParam;
static const lean_string_object l_Lean_instInhabitedAttributeImplCore_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "instInhabitedAttributeImplCore"};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__0_value;
static const lean_string_object l_Lean_instInhabitedAttributeImplCore_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__1_value;
static const lean_ctor_object l_Lean_instInhabitedAttributeImplCore_default___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instInhabitedAttributeImplCore_default___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__2_value_aux_0),((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 168, 67, 30, 9, 195, 195, 250)}};
static const lean_ctor_object l_Lean_instInhabitedAttributeImplCore_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__2_value_aux_1),((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__1_value),LEAN_SCALAR_PTR_LITERAL(6, 28, 76, 169, 127, 73, 161, 93)}};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__2_value;
static const lean_string_object l_Lean_instInhabitedAttributeImplCore_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__3 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__3_value;
static const lean_ctor_object l_Lean_instInhabitedAttributeImplCore_default___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__4 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImplCore_default = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImplCore = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqAttributeKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqAttributeKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqAttributeKind___closed__0 = (const lean_object*)&l_Lean_instBEqAttributeKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqAttributeKind = (const lean_object*)&l_Lean_instBEqAttributeKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_instInhabitedAttributeKind_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedAttributeKind;
static const lean_string_object l_Lean_instToStringAttributeKind___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_instToStringAttributeKind___lam__0___closed__0 = (const lean_object*)&l_Lean_instToStringAttributeKind___lam__0___closed__0_value;
static const lean_string_object l_Lean_instToStringAttributeKind___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_instToStringAttributeKind___lam__0___closed__1 = (const lean_object*)&l_Lean_instToStringAttributeKind___lam__0___closed__1_value;
static const lean_string_object l_Lean_instToStringAttributeKind___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_instToStringAttributeKind___lam__0___closed__2 = (const lean_object*)&l_Lean_instToStringAttributeKind___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToStringAttributeKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToStringAttributeKind___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToStringAttributeKind___closed__0 = (const lean_object*)&l_Lean_instToStringAttributeKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToStringAttributeKind = (const lean_object*)&l_Lean_instToStringAttributeKind___closed__0_value;
static lean_once_cell_t l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1;
static const lean_string_object l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instInhabitedAttributeImpl_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedAttributeImpl_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value)} };
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__1_value;
static const lean_ctor_object l_Lean_instInhabitedAttributeImpl_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value),((lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__0_value),((lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__1_value)}};
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImpl_default = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImpl = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__2_value;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_attributeMapRef;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_registerBuiltinAttribute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "Failed to register attribute: Attributes can only be registered during initialization"};
static const lean_object* l_Lean_registerBuiltinAttribute___closed__0 = (const lean_object*)&l_Lean_registerBuiltinAttribute___closed__0_value;
static lean_once_cell_t l_Lean_registerBuiltinAttribute___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerBuiltinAttribute___closed__1;
static const lean_string_object l_Lean_registerBuiltinAttribute___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Invalid builtin attribute declaration: `"};
static const lean_object* l_Lean_registerBuiltinAttribute___closed__2 = (const lean_object*)&l_Lean_registerBuiltinAttribute___closed__2_value;
static const lean_string_object l_Lean_registerBuiltinAttribute___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "` has already been used"};
static const lean_object* l_Lean_registerBuiltinAttribute___closed__3 = (const lean_object*)&l_Lean_registerBuiltinAttribute___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__0 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value;
static const lean_string_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "class"};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__1 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__1_value;
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_1),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_2),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(149, 14, 146, 125, 144, 1, 65, 64)}};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__2 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value;
static const lean_string_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "Unexpected attribute argument: This attribute takes no arguments"};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__3 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__3_value;
static lean_once_cell_t l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__4;
static const lean_string_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__5 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__5_value;
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_1),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_2),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__5_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__6 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "macro"};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__0 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_2),((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 202, 70, 6, 8, 133, 137, 74)}};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__1 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value;
static const lean_string_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "export"};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__2 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_1),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_2),((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(43, 70, 85, 26, 88, 142, 178, 115)}};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__3 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value;
static const lean_string_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Unexpected attribute argument"};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__4 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Attribute_Builtin_getIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Unexpected attribute argument: Expected identifier, but found"};
static const lean_object* l_Lean_Attribute_Builtin_getIdent___closed__0 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent___closed__0_value;
static lean_once_cell_t l_Lean_Attribute_Builtin_getIdent___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Attribute_Builtin_getIdent___closed__1;
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getAttrParamOptPrio___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Unexpected attribute argument: Expected a priority, but found"};
static const lean_object* l_Lean_getAttrParamOptPrio___closed__0 = (const lean_object*)&l_Lean_getAttrParamOptPrio___closed__0_value;
static lean_once_cell_t l_Lean_getAttrParamOptPrio___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getAttrParamOptPrio___closed__1;
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Attribute_Builtin_getPrio___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "Unexpected attribute argument: Expected an optional priority, but found"};
static const lean_object* l_Lean_Attribute_Builtin_getPrio___closed__0 = (const lean_object*)&l_Lean_Attribute_Builtin_getPrio___closed__0_value;
static lean_once_cell_t l_Lean_Attribute_Builtin_getPrio___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Attribute_Builtin_getPrio___closed__1;
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` to declaration `"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` because it is in an imported module"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "` because it is not from the present async context"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " `"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "]`: Declaration `"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` has type"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "\nbut `["};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "]` can only be added to declarations of type"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "` must be public"};
static const lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0 = (const lean_object*)&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ensureAttrDeclIsMeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` must be marked as `meta`"};
static const lean_object* l_Lean_ensureAttrDeclIsMeta___closed__0 = (const lean_object*)&l_Lean_ensureAttrDeclIsMeta___closed__0_value;
static lean_once_cell_t l_Lean_ensureAttrDeclIsMeta___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ensureAttrDeclIsMeta___closed__1;
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instInhabitedTagAttribute_default___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___closed__0 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_instInhabitedTagAttribute_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedTagAttribute_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedTagAttribute_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedTagAttribute_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedTagAttribute_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedTagAttribute_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedTagAttribute_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedTagAttribute_default___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedTagAttribute_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___closed__2_value;
static const lean_closure_object l_Lean_instInhabitedTagAttribute_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedTagAttribute_default___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedTagAttribute_default___closed__3 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___closed__3_value;
static lean_once_cell_t l_Lean_instInhabitedTagAttribute_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTagAttribute_default___closed__4;
static lean_once_cell_t l_Lean_instInhabitedTagAttribute_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTagAttribute_default___closed__5;
static lean_once_cell_t l_Lean_instInhabitedTagAttribute_default___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTagAttribute_default___closed__6;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute;
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___auto__1;
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerTagAttribute___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tag attribute"};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__0 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_registerTagAttribute___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__0_value)}};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__1 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_registerTagAttribute___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__2 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__2_value;
static const lean_string_object l_Lean_registerTagAttribute___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "number of local entries: "};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__3 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__3_value;
static const lean_ctor_object l_Lean_registerTagAttribute___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__3_value)}};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__4 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__4_value;
static const lean_ctor_object l_Lean_registerTagAttribute___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__2_value),((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__4_value)}};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__5 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_registerTagAttribute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__0 = (const lean_object*)&l_Lean_registerTagAttribute___closed__0_value;
static const lean_closure_object l_Lean_registerTagAttribute___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__1 = (const lean_object*)&l_Lean_registerTagAttribute___closed__1_value;
static const lean_closure_object l_Lean_registerTagAttribute___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__2 = (const lean_object*)&l_Lean_registerTagAttribute___closed__2_value;
static const lean_closure_object l_Lean_registerTagAttribute___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__3, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__3 = (const lean_object*)&l_Lean_registerTagAttribute___closed__3_value;
static const lean_closure_object l_Lean_registerTagAttribute___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_insert, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__4 = (const lean_object*)&l_Lean_registerTagAttribute___closed__4_value;
static lean_once_cell_t l_Lean_registerTagAttribute___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTagAttribute___closed__5;
static lean_once_cell_t l_Lean_registerTagAttribute___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTagAttribute___closed__6;
static const lean_ctor_object l_Lean_registerTagAttribute___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___closed__1_value)}};
static const lean_object* l_Lean_registerTagAttribute___closed__7 = (const lean_object*)&l_Lean_registerTagAttribute___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___closed__2_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__3 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___closed__3_value;
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__4;
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__5;
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__6;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "parametric attribute"};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__2_value;
static const lean_ctor_object l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__2_value),((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__4_value)}};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__0 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__0_value;
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__1 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__1_value;
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__2 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__2_value;
static const lean_ctor_object l_Lean_registerParametricAttributeExt___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__3 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__3_value;
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__3_value)} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__4 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__4_value;
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__3_value)} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__5 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__3 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__3_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__4 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__4_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__5 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__5_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__6 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__6_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__7 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__7_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__8 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__8_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__9 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__9_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__3_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__4_value)}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__10 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__10_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__10_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__5_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__6_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__7_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__8_value)}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__11 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__11_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__11_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__9_value)}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Failed to add parametric attribute `["};
static const lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0 = (const lean_object*)&l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0_value;
static const lean_string_object l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "]` to `"};
static const lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1 = (const lean_object*)&l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1_value;
static const lean_string_object l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "`: Attribute has already been set"};
static const lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2 = (const lean_object*)&l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2_value;
static const lean_string_object l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`: Declaration is in an imported module"};
static const lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3 = (const lean_object*)&l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___closed__2_value;
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__3;
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__4;
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__5;
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___auto__1;
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerEnumAttributes___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "enumeration attribute extension"};
static const lean_object* l_Lean_registerEnumAttributes___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__2_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__2_value),((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__4_value)}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___lam__2___closed__3 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__0 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__0_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__1 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__1_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__2 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__2_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__3 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__3_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__4, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__4 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__4_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__5___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__5 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__5_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__6___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__6 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__6_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__7 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__7_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__1_value)}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__8 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Internal error calling `"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__0 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__0_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = ".setValue` for `"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__1 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__1_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = ": Declaration is not from this async context `"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__2 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__2_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__3 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__3_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "(some "};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__4 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__4_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__5 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__5_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = ": Attribute has already been set"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__6 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__6_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = ": Declaration is in an imported module"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__7 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_attributeImplBuilderTableRef;
static const lean_string_object l_Lean_registerAttributeImplBuilder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Attribute implementation builder `"};
static const lean_object* l_Lean_registerAttributeImplBuilder___closed__0 = (const lean_object*)&l_Lean_registerAttributeImplBuilder___closed__0_value;
static const lean_string_object l_Lean_registerAttributeImplBuilder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` has already been declared"};
static const lean_object* l_Lean_registerAttributeImplBuilder___closed__1 = (const lean_object*)&l_Lean_registerAttributeImplBuilder___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkAttributeImplOfEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Unknown attribute implementation builder `"};
static const lean_object* l_Lean_mkAttributeImplOfEntry___closed__0 = (const lean_object*)&l_Lean_mkAttributeImplOfEntry___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedAttributeExtensionState_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeExtensionState_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeExtensionState;
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object*);
static const lean_string_object l_Lean_mkAttributeImplOfConstantUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "Unexpected attribute implementation type: `{.ofConstName declName}` is not of type `Lean.AttributeImpl`"};
static const lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___closed__0 = (const lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__0_value;
static const lean_ctor_object l_Lean_mkAttributeImplOfConstantUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__0_value)}};
static const lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___closed__1 = (const lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__1_value;
static const lean_string_object l_Lean_mkAttributeImplOfConstantUnsafe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___closed__2 = (const lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__2_value;
static const lean_string_object l_Lean_mkAttributeImplOfConstantUnsafe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "AttributeImpl"};
static const lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___closed__3 = (const lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object*);
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "attributeExtension"};
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(219, 25, 250, 145, 208, 184, 170, 105)}};
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_addAttrEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_attributeExtension;
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_getBuiltinAttributeNames_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_getBuiltinAttributeNames_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames();
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object*);
static const lean_string_object l_Lean_getBuiltinAttributeImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Unknown attribute `"};
static const lean_object* l_Lean_getBuiltinAttributeImpl___closed__0 = (const lean_object*)&l_Lean_getBuiltinAttributeImpl___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_updateEnvAttributesImpl_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_updateEnvAttributesImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_updateEnvAttributesImpl_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_num_attributes();
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
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
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_AttributeApplicationTime_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_AttributeApplicationTime_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_AttributeApplicationTime_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(lean_object* v_afterTypeChecking_23_){
_start:
{
lean_inc(v_afterTypeChecking_23_);
return v_afterTypeChecking_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg___boxed(lean_object* v_afterTypeChecking_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(v_afterTypeChecking_24_);
lean_dec(v_afterTypeChecking_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_afterTypeChecking_29_){
_start:
{
lean_inc(v_afterTypeChecking_29_);
return v_afterTypeChecking_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_afterTypeChecking_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_AttributeApplicationTime_afterTypeChecking_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_afterTypeChecking_33_);
lean_dec(v_afterTypeChecking_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(lean_object* v_afterCompilation_36_){
_start:
{
lean_inc(v_afterCompilation_36_);
return v_afterCompilation_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg___boxed(lean_object* v_afterCompilation_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(v_afterCompilation_37_);
lean_dec(v_afterCompilation_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_afterCompilation_42_){
_start:
{
lean_inc(v_afterCompilation_42_);
return v_afterCompilation_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_afterCompilation_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_AttributeApplicationTime_afterCompilation_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_afterCompilation_46_);
lean_dec(v_afterCompilation_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(lean_object* v_beforeElaboration_49_){
_start:
{
lean_inc(v_beforeElaboration_49_);
return v_beforeElaboration_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg___boxed(lean_object* v_beforeElaboration_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(v_beforeElaboration_50_);
lean_dec(v_beforeElaboration_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_beforeElaboration_55_){
_start:
{
lean_inc(v_beforeElaboration_55_);
return v_beforeElaboration_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_beforeElaboration_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_AttributeApplicationTime_beforeElaboration_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_beforeElaboration_59_);
lean_dec(v_beforeElaboration_59_);
return v_res_61_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeApplicationTime_default(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeApplicationTime(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeApplicationTime_beq(uint8_t v_x_64_, uint8_t v_y_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_66_ = l_Lean_AttributeApplicationTime_ctorIdx(v_x_64_);
v___x_67_ = l_Lean_AttributeApplicationTime_ctorIdx(v_y_65_);
v___x_68_ = lean_nat_dec_eq(v___x_66_, v___x_67_);
lean_dec(v___x_67_);
lean_dec(v___x_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeApplicationTime_beq___boxed(lean_object* v_x_69_, lean_object* v_y_70_){
_start:
{
uint8_t v_x_17__boxed_71_; uint8_t v_y_18__boxed_72_; uint8_t v_res_73_; lean_object* v_r_74_; 
v_x_17__boxed_71_ = lean_unbox(v_x_69_);
v_y_18__boxed_72_ = lean_unbox(v_y_70_);
v_res_73_ = l_Lean_instBEqAttributeApplicationTime_beq(v_x_17__boxed_71_, v_y_18__boxed_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0(lean_object* v_00_u03b1_77_, lean_object* v_x_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v___x_82_; lean_object* v_env_83_; lean_object* v_options_84_; lean_object* v_ref_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_82_ = lean_st_ref_get(v___y_80_);
v_env_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc_ref(v_env_83_);
lean_dec(v___x_82_);
v_options_84_ = lean_ctor_get(v___y_79_, 2);
v_ref_85_ = lean_ctor_get(v___y_79_, 5);
lean_inc_ref(v_options_84_);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v_env_83_);
lean_ctor_set(v___x_86_, 1, v_options_84_);
v___x_87_ = lean_apply_2(v_x_78_, v___x_86_, lean_box(0));
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_95_ == 0)
{
v___x_90_ = v___x_87_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_87_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_a_88_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_107_; 
v_a_96_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_107_ == 0)
{
v___x_98_ = v___x_87_;
v_isShared_99_ = v_isSharedCheck_107_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_87_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_107_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_100_ = lean_io_error_to_string(v_a_96_);
v___x_101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
v___x_102_ = l_Lean_MessageData_ofFormat(v___x_101_);
lean_inc(v_ref_85_);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v_ref_85_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_103_);
v___x_105_ = v___x_98_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0___boxed(lean_object* v_00_u03b1_108_, lean_object* v_x_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_instMonadLiftImportMAttrM___lam__0(v_00_u03b1_108_, v_x_109_, v___y_110_, v___y_111_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
return v_res_113_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__10));
v___x_143_ = l_Lean_mkAtom(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__12, &l_Lean_AttributeImplCore_ref___autoParam___closed__12_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12);
v___x_145_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_146_ = lean_array_push(v___x_145_, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__17));
v___x_156_ = l_Lean_mkAtom(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__18, &l_Lean_AttributeImplCore_ref___autoParam___closed__18_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18);
v___x_158_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_159_ = lean_array_push(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_160_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__19, &l_Lean_AttributeImplCore_ref___autoParam___closed__19_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19);
v___x_161_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__16));
v___x_162_ = lean_box(2);
v___x_163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
lean_ctor_set(v___x_163_, 2, v___x_160_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__20, &l_Lean_AttributeImplCore_ref___autoParam___closed__20_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20);
v___x_165_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__13, &l_Lean_AttributeImplCore_ref___autoParam___closed__13_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13);
v___x_166_ = lean_array_push(v___x_165_, v___x_164_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__21, &l_Lean_AttributeImplCore_ref___autoParam___closed__21_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21);
v___x_168_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__11));
v___x_169_ = lean_box(2);
v___x_170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_167_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__22, &l_Lean_AttributeImplCore_ref___autoParam___closed__22_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22);
v___x_172_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_173_ = lean_array_push(v___x_172_, v___x_171_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_174_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__23, &l_Lean_AttributeImplCore_ref___autoParam___closed__23_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23);
v___x_175_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__9));
v___x_176_ = lean_box(2);
v___x_177_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_175_);
lean_ctor_set(v___x_177_, 2, v___x_174_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__24, &l_Lean_AttributeImplCore_ref___autoParam___closed__24_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24);
v___x_179_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_180_ = lean_array_push(v___x_179_, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_181_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__25, &l_Lean_AttributeImplCore_ref___autoParam___closed__25_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25);
v___x_182_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__7));
v___x_183_ = lean_box(2);
v___x_184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___x_182_);
lean_ctor_set(v___x_184_, 2, v___x_181_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__26, &l_Lean_AttributeImplCore_ref___autoParam___closed__26_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26);
v___x_186_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_187_ = lean_array_push(v___x_186_, v___x_185_);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_188_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__27, &l_Lean_AttributeImplCore_ref___autoParam___closed__27_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27);
v___x_189_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__4));
v___x_190_ = lean_box(2);
v___x_191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_189_);
lean_ctor_set(v___x_191_, 2, v___x_188_);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam(void){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx(uint8_t v_x_207_){
_start:
{
switch(v_x_207_)
{
case 0:
{
lean_object* v___x_208_; 
v___x_208_ = lean_unsigned_to_nat(0u);
return v___x_208_;
}
case 1:
{
lean_object* v___x_209_; 
v___x_209_ = lean_unsigned_to_nat(1u);
return v___x_209_;
}
default: 
{
lean_object* v___x_210_; 
v___x_210_ = lean_unsigned_to_nat(2u);
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx___boxed(lean_object* v_x_211_){
_start:
{
uint8_t v_x_boxed_212_; lean_object* v_res_213_; 
v_x_boxed_212_ = lean_unbox(v_x_211_);
v_res_213_ = l_Lean_AttributeKind_ctorIdx(v_x_boxed_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg(lean_object* v_k_214_){
_start:
{
lean_inc(v_k_214_);
return v_k_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg___boxed(lean_object* v_k_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_AttributeKind_ctorElim___redArg(v_k_215_);
lean_dec(v_k_215_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim(lean_object* v_motive_217_, lean_object* v_ctorIdx_218_, uint8_t v_t_219_, lean_object* v_h_220_, lean_object* v_k_221_){
_start:
{
lean_inc(v_k_221_);
return v_k_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___boxed(lean_object* v_motive_222_, lean_object* v_ctorIdx_223_, lean_object* v_t_224_, lean_object* v_h_225_, lean_object* v_k_226_){
_start:
{
uint8_t v_t_boxed_227_; lean_object* v_res_228_; 
v_t_boxed_227_ = lean_unbox(v_t_224_);
v_res_228_ = l_Lean_AttributeKind_ctorElim(v_motive_222_, v_ctorIdx_223_, v_t_boxed_227_, v_h_225_, v_k_226_);
lean_dec(v_k_226_);
lean_dec(v_ctorIdx_223_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg(lean_object* v_global_229_){
_start:
{
lean_inc(v_global_229_);
return v_global_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg___boxed(lean_object* v_global_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_AttributeKind_global_elim___redArg(v_global_230_);
lean_dec(v_global_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim(lean_object* v_motive_232_, uint8_t v_t_233_, lean_object* v_h_234_, lean_object* v_global_235_){
_start:
{
lean_inc(v_global_235_);
return v_global_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___boxed(lean_object* v_motive_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_global_239_){
_start:
{
uint8_t v_t_boxed_240_; lean_object* v_res_241_; 
v_t_boxed_240_ = lean_unbox(v_t_237_);
v_res_241_ = l_Lean_AttributeKind_global_elim(v_motive_236_, v_t_boxed_240_, v_h_238_, v_global_239_);
lean_dec(v_global_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg(lean_object* v_local_242_){
_start:
{
lean_inc(v_local_242_);
return v_local_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg___boxed(lean_object* v_local_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_AttributeKind_local_elim___redArg(v_local_243_);
lean_dec(v_local_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim(lean_object* v_motive_245_, uint8_t v_t_246_, lean_object* v_h_247_, lean_object* v_local_248_){
_start:
{
lean_inc(v_local_248_);
return v_local_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___boxed(lean_object* v_motive_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_local_252_){
_start:
{
uint8_t v_t_boxed_253_; lean_object* v_res_254_; 
v_t_boxed_253_ = lean_unbox(v_t_250_);
v_res_254_ = l_Lean_AttributeKind_local_elim(v_motive_249_, v_t_boxed_253_, v_h_251_, v_local_252_);
lean_dec(v_local_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg(lean_object* v_scoped_255_){
_start:
{
lean_inc(v_scoped_255_);
return v_scoped_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg___boxed(lean_object* v_scoped_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_AttributeKind_scoped_elim___redArg(v_scoped_256_);
lean_dec(v_scoped_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim(lean_object* v_motive_258_, uint8_t v_t_259_, lean_object* v_h_260_, lean_object* v_scoped_261_){
_start:
{
lean_inc(v_scoped_261_);
return v_scoped_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___boxed(lean_object* v_motive_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_scoped_265_){
_start:
{
uint8_t v_t_boxed_266_; lean_object* v_res_267_; 
v_t_boxed_266_ = lean_unbox(v_t_263_);
v_res_267_ = l_Lean_AttributeKind_scoped_elim(v_motive_262_, v_t_boxed_266_, v_h_264_, v_scoped_265_);
lean_dec(v_scoped_265_);
return v_res_267_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t v_x_268_, uint8_t v_y_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_270_ = l_Lean_AttributeKind_ctorIdx(v_x_268_);
v___x_271_ = l_Lean_AttributeKind_ctorIdx(v_y_269_);
v___x_272_ = lean_nat_dec_eq(v___x_270_, v___x_271_);
lean_dec(v___x_271_);
lean_dec(v___x_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeKind_beq___boxed(lean_object* v_x_273_, lean_object* v_y_274_){
_start:
{
uint8_t v_x_17__boxed_275_; uint8_t v_y_18__boxed_276_; uint8_t v_res_277_; lean_object* v_r_278_; 
v_x_17__boxed_275_ = lean_unbox(v_x_273_);
v_y_18__boxed_276_ = lean_unbox(v_y_274_);
v_res_277_ = l_Lean_instBEqAttributeKind_beq(v_x_17__boxed_275_, v_y_18__boxed_276_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind_default(void){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = 0;
return v___x_281_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind(void){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = 0;
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0(uint8_t v_x_286_){
_start:
{
switch(v_x_286_)
{
case 0:
{
lean_object* v___x_287_; 
v___x_287_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
return v___x_287_;
}
case 1:
{
lean_object* v___x_288_; 
v___x_288_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
return v___x_288_;
}
default: 
{
lean_object* v___x_289_; 
v___x_289_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0___boxed(lean_object* v_x_290_){
_start:
{
uint8_t v_x_36__boxed_291_; lean_object* v_res_292_; 
v_x_36__boxed_291_ = lean_unbox(v_x_290_);
v_res_292_ = l_Lean_instToStringAttributeKind___lam__0(v_x_36__boxed_291_);
return v_res_292_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = l_Lean_instInhabitedMessageData_default;
v___x_296_ = lean_box(0);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0(lean_object* v_x_298_, lean_object* v___y_299_, uint8_t v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0, &l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed(lean_object* v_x_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
uint8_t v___y_1012__boxed_312_; lean_object* v_res_313_; 
v___y_1012__boxed_312_ = lean_unbox(v___y_308_);
v_res_313_ = l_Lean_instInhabitedAttributeImpl_default___lam__0(v_x_306_, v___y_307_, v___y_1012__boxed_312_, v___y_309_, v___y_310_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_307_);
lean_dec(v_x_306_);
return v_res_313_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_314_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
lean_ctor_set(v___x_319_, 2, v___x_318_);
lean_ctor_set(v___x_319_, 3, v___x_318_);
lean_ctor_set(v___x_319_, 4, v___x_317_);
lean_ctor_set(v___x_319_, 5, v___x_317_);
lean_ctor_set(v___x_319_, 6, v___x_317_);
lean_ctor_set(v___x_319_, 7, v___x_317_);
lean_ctor_set(v___x_319_, 8, v___x_317_);
lean_ctor_set(v___x_319_, 9, v___x_317_);
lean_ctor_set(v___x_319_, 10, v___x_317_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_unsigned_to_nat(32u);
v___x_321_ = lean_mk_empty_array_with_capacity(v___x_320_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_323_ = ((size_t)5ULL);
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = lean_unsigned_to_nat(32u);
v___x_326_ = lean_mk_empty_array_with_capacity(v___x_325_);
v___x_327_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3);
v___x_328_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___x_326_);
lean_ctor_set(v___x_328_, 2, v___x_324_);
lean_ctor_set(v___x_328_, 3, v___x_324_);
lean_ctor_set_usize(v___x_328_, 4, v___x_323_);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_329_ = lean_box(1);
v___x_330_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4);
v___x_331_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
lean_ctor_set(v___x_332_, 2, v___x_329_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(lean_object* v_msgData_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_337_; lean_object* v_env_338_; lean_object* v_options_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_337_ = lean_st_ref_get(v___y_335_);
v_env_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc_ref(v_env_338_);
lean_dec(v___x_337_);
v_options_339_ = lean_ctor_get(v___y_334_, 2);
v___x_340_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2);
v___x_341_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_339_);
v___x_342_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_342_, 0, v_env_338_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
lean_ctor_set(v___x_342_, 2, v___x_341_);
lean_ctor_set(v___x_342_, 3, v_options_339_);
v___x_343_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v_msgData_333_);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___boxed(lean_object* v_msgData_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msgData_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(lean_object* v_msg_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_ref_354_; lean_object* v___x_355_; lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_364_; 
v_ref_354_ = lean_ctor_get(v___y_351_, 5);
v___x_355_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msg_350_, v___y_351_, v___y_352_);
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_364_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_364_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_364_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
lean_inc(v_ref_354_);
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v_ref_354_);
lean_ctor_set(v___x_360_, 1, v_a_356_);
if (v_isShared_359_ == 0)
{
lean_ctor_set_tag(v___x_358_, 1);
lean_ctor_set(v___x_358_, 0, v___x_360_);
v___x_362_ = v___x_358_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg___boxed(lean_object* v_msg_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
return v_res_369_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0));
v___x_372_ = l_Lean_stringToMessageData(v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2));
v___x_375_ = l_Lean_stringToMessageData(v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1(lean_object* v___x_376_, lean_object* v_decl_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_name_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v_name_381_ = lean_ctor_get(v___x_376_, 1);
lean_inc(v_name_381_);
lean_dec_ref(v___x_376_);
v___x_382_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_383_ = l_Lean_MessageData_ofName(v_name_381_);
v___x_384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_386_, v___y_378_, v___y_379_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed(lean_object* v___x_388_, lean_object* v_decl_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_instInhabitedAttributeImpl_default___lam__1(v___x_388_, v_decl_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v_decl_389_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(lean_object* v_00_u03b1_402_, lean_object* v_msg_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_403_, v___y_404_, v___y_405_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___boxed(lean_object* v_00_u03b1_408_, lean_object* v_msg_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(v_00_u03b1_408_, v_msg_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
return v_res_413_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_415_; lean_object* v___x_416_; 
v_cellCount_415_ = lean_unsigned_to_nat(16u);
v___x_416_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_415_);
return v___x_416_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_417_; lean_object* v___x_418_; 
v_cellCount_417_ = lean_unsigned_to_nat(16u);
v___x_418_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_417_);
return v___x_418_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_419_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_420_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
lean_ctor_set(v___x_422_, 2, v___x_419_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_425_ = lean_st_mk_ref(v___x_424_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(lean_object* v_m_429_, lean_object* v_query_430_, lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
lean_object* v_zero_434_; uint8_t v_isZero_435_; 
v_zero_434_ = lean_unsigned_to_nat(0u);
v_isZero_435_ = lean_nat_dec_eq(v_x_432_, v_zero_434_);
if (v_isZero_435_ == 1)
{
lean_dec(v_x_433_);
lean_dec(v_x_432_);
if (lean_obj_tag(v_x_431_) == 0)
{
lean_object* v___x_436_; 
v___x_436_ = lean_box(2);
return v___x_436_;
}
else
{
lean_object* v_val_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
v_val_437_ = lean_ctor_get(v_x_431_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v_x_431_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v_x_431_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_val_437_);
lean_dec(v_x_431_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_val_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
else
{
lean_object* v_keyArray_445_; lean_object* v_valueArray_446_; lean_object* v___x_447_; uint8_t v_isSome_448_; 
v_keyArray_445_ = lean_ctor_get(v_m_429_, 1);
v_valueArray_446_ = lean_ctor_get(v_m_429_, 2);
v___x_447_ = lean_array_fget_borrowed(v_keyArray_445_, v_x_433_);
v_isSome_448_ = lean_noption_is_some(v___x_447_);
if (v_isSome_448_ == 0)
{
lean_dec(v_x_432_);
if (lean_obj_tag(v_x_431_) == 0)
{
lean_object* v___x_449_; 
v___x_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_449_, 0, v_x_433_);
return v___x_449_;
}
else
{
lean_object* v_val_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_dec(v_x_433_);
v_val_450_ = lean_ctor_get(v_x_431_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v_x_431_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v_x_431_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_val_450_);
lean_dec(v_x_431_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_val_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
else
{
lean_object* v_one_458_; lean_object* v_n_459_; lean_object* v___y_461_; 
v_one_458_ = lean_unsigned_to_nat(1u);
v_n_459_ = lean_nat_sub(v_x_432_, v_one_458_);
lean_dec(v_x_432_);
if (v_isSome_448_ == 0)
{
goto v___jp_467_;
}
else
{
lean_object* v___x_469_; uint8_t v_isSome_470_; 
v___x_469_ = lean_array_fget_borrowed(v_valueArray_446_, v_x_433_);
v_isSome_470_ = lean_noption_is_some(v___x_469_);
if (v_isSome_470_ == 0)
{
goto v___jp_467_;
}
else
{
lean_object* v_val_471_; uint8_t v___x_472_; 
lean_inc(v___x_447_);
v_val_471_ = lean_noption_get(v___x_447_);
v___x_472_ = lean_name_eq(v_val_471_, v_query_430_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
lean_dec(v_val_471_);
v___x_473_ = lean_array_get_size(v_keyArray_445_);
v___x_474_ = lean_nat_add(v_x_433_, v_one_458_);
lean_dec(v_x_433_);
v___x_475_ = lean_nat_dec_lt(v___x_474_, v___x_473_);
if (v___x_475_ == 0)
{
lean_dec(v___x_474_);
v_x_432_ = v_n_459_;
v_x_433_ = v_zero_434_;
goto _start;
}
else
{
v_x_432_ = v_n_459_;
v_x_433_ = v___x_474_;
goto _start;
}
}
else
{
lean_object* v_val_478_; lean_object* v___x_479_; 
lean_dec(v_n_459_);
lean_dec(v_x_431_);
lean_inc(v___x_469_);
v_val_478_ = lean_noption_get(v___x_469_);
v___x_479_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_479_, 0, v_x_433_);
lean_ctor_set(v___x_479_, 1, v_val_471_);
lean_ctor_set(v___x_479_, 2, v_val_478_);
return v___x_479_;
}
}
}
v___jp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_462_ = lean_array_get_size(v_keyArray_445_);
v___x_463_ = lean_nat_add(v_x_433_, v_one_458_);
lean_dec(v_x_433_);
v___x_464_ = lean_nat_dec_lt(v___x_463_, v___x_462_);
if (v___x_464_ == 0)
{
lean_dec(v___x_463_);
v_x_431_ = v___y_461_;
v_x_432_ = v_n_459_;
v_x_433_ = v_zero_434_;
goto _start;
}
else
{
v_x_431_ = v___y_461_;
v_x_432_ = v_n_459_;
v_x_433_ = v___x_463_;
goto _start;
}
}
v___jp_467_:
{
if (lean_obj_tag(v_x_431_) == 0)
{
lean_object* v___x_468_; 
lean_inc(v_x_433_);
v___x_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_468_, 0, v_x_433_);
v___y_461_ = v___x_468_;
goto v___jp_460_;
}
else
{
v___y_461_ = v_x_431_;
goto v___jp_460_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg___boxed(lean_object* v_m_480_, lean_object* v_query_481_, lean_object* v_x_482_, lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_m_480_, v_query_481_, v_x_482_, v_x_483_, v_x_484_);
lean_dec(v_query_481_);
lean_dec_ref(v_m_480_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(lean_object* v_m_486_, lean_object* v_query_487_){
_start:
{
lean_object* v_keyArray_488_; lean_object* v___x_489_; uint64_t v___y_491_; 
v_keyArray_488_ = lean_ctor_get(v_m_486_, 1);
v___x_489_ = lean_array_get_size(v_keyArray_488_);
if (lean_obj_tag(v_query_487_) == 0)
{
uint64_t v___x_506_; 
v___x_506_ = 1723ULL;
v___y_491_ = v___x_506_;
goto v___jp_490_;
}
else
{
uint64_t v_hash_507_; 
v_hash_507_ = lean_ctor_get_uint64(v_query_487_, sizeof(void*)*2);
v___y_491_ = v_hash_507_;
goto v___jp_490_;
}
v___jp_490_:
{
uint64_t v___x_492_; uint64_t v___x_493_; uint64_t v_fold_494_; uint64_t v___x_495_; uint64_t v___x_496_; uint64_t v___x_497_; size_t v___x_498_; size_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_492_ = 32ULL;
v___x_493_ = lean_uint64_shift_right(v___y_491_, v___x_492_);
v_fold_494_ = lean_uint64_xor(v___y_491_, v___x_493_);
v___x_495_ = 16ULL;
v___x_496_ = lean_uint64_shift_right(v_fold_494_, v___x_495_);
v___x_497_ = lean_uint64_xor(v_fold_494_, v___x_496_);
v___x_498_ = lean_uint64_to_usize(v___x_497_);
v___x_499_ = lean_usize_of_nat(v___x_489_);
v___x_500_ = ((size_t)1ULL);
v___x_501_ = lean_usize_sub(v___x_499_, v___x_500_);
v___x_502_ = lean_usize_land(v___x_498_, v___x_501_);
v___x_503_ = lean_usize_to_nat(v___x_502_);
v___x_504_ = lean_box(0);
v___x_505_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_m_486_, v_query_487_, v___x_504_, v___x_489_, v___x_503_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg___boxed(lean_object* v_m_508_, lean_object* v_query_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_m_508_, v_query_509_);
lean_dec(v_query_509_);
lean_dec_ref(v_m_508_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object* v_m_511_, lean_object* v_query_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_m_511_, v_query_512_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_index_514_; lean_object* v_key_515_; lean_object* v_value_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
v_index_514_ = lean_ctor_get(v___x_513_, 0);
v_key_515_ = lean_ctor_get(v___x_513_, 1);
v_value_516_ = lean_ctor_get(v___x_513_, 2);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_513_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_value_516_);
lean_inc(v_key_515_);
lean_inc(v_index_514_);
lean_dec(v___x_513_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_index_514_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_key_515_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_value_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
else
{
lean_object* v___x_524_; 
lean_dec(v___x_513_);
v___x_524_ = lean_box(1);
return v___x_524_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg___boxed(lean_object* v_m_525_, lean_object* v_query_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_m_525_, v_query_526_);
lean_dec(v_query_526_);
lean_dec_ref(v_m_525_);
return v_res_527_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(lean_object* v_m_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_m_528_, v_a_529_);
if (lean_obj_tag(v___x_530_) == 0)
{
uint8_t v___x_531_; 
lean_dec_ref_known(v___x_530_, 3);
v___x_531_ = 1;
return v___x_531_;
}
else
{
uint8_t v___x_532_; 
v___x_532_ = 0;
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___boxed(lean_object* v_m_533_, lean_object* v_a_534_){
_start:
{
uint8_t v_res_535_; lean_object* v_r_536_; 
v_res_535_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_533_, v_a_534_);
lean_dec(v_a_534_);
lean_dec_ref(v_m_533_);
v_r_536_ = lean_box(v_res_535_);
return v_r_536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4_spec__5___redArg(lean_object* v_b_537_, lean_object* v_acc_538_, lean_object* v_i_539_){
_start:
{
lean_object* v___y_541_; lean_object* v_keyArray_549_; lean_object* v_valueArray_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v_keyArray_549_ = lean_ctor_get(v_b_537_, 1);
v_valueArray_550_ = lean_ctor_get(v_b_537_, 2);
v___x_551_ = lean_array_get_size(v_keyArray_549_);
v___x_552_ = lean_nat_dec_lt(v_i_539_, v___x_551_);
if (v___x_552_ == 0)
{
lean_dec(v_i_539_);
return v_acc_538_;
}
else
{
lean_object* v___x_553_; uint8_t v_isSome_554_; 
v___x_553_ = lean_array_fget_borrowed(v_keyArray_549_, v_i_539_);
v_isSome_554_ = lean_noption_is_some(v___x_553_);
if (v_isSome_554_ == 0)
{
goto v___jp_545_;
}
else
{
lean_object* v___x_555_; uint8_t v_isSome_556_; 
v___x_555_ = lean_array_fget_borrowed(v_valueArray_550_, v_i_539_);
v_isSome_556_ = lean_noption_is_some(v___x_555_);
if (v_isSome_556_ == 0)
{
goto v___jp_545_;
}
else
{
lean_object* v_val_557_; lean_object* v_val_558_; lean_object* v_i_560_; lean_object* v___x_565_; 
lean_inc(v___x_553_);
v_val_557_ = lean_noption_get(v___x_553_);
lean_inc(v___x_555_);
v_val_558_ = lean_noption_get(v___x_555_);
v___x_565_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_acc_538_, v_val_557_);
switch(lean_obj_tag(v___x_565_))
{
case 0:
{
lean_object* v_index_566_; lean_object* v_size_567_; lean_object* v___x_568_; 
v_index_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_index_566_);
lean_dec_ref_known(v___x_565_, 3);
v_size_567_ = lean_ctor_get(v_acc_538_, 0);
lean_inc(v_size_567_);
v___x_568_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_538_, v_size_567_, v_index_566_, v_val_557_, v_val_558_);
lean_dec(v_index_566_);
v___y_541_ = v___x_568_;
goto v___jp_540_;
}
case 1:
{
lean_object* v_index_569_; 
v_index_569_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_index_569_);
lean_dec_ref_known(v___x_565_, 1);
v_i_560_ = v_index_569_;
goto v___jp_559_;
}
default: 
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_538_, v___x_570_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_index_572_; 
v_index_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_index_572_);
lean_dec_ref_known(v___x_571_, 1);
v_i_560_ = v_index_572_;
goto v___jp_559_;
}
else
{
lean_dec(v_val_558_);
lean_dec(v_val_557_);
v___y_541_ = v_acc_538_;
goto v___jp_540_;
}
}
}
v___jp_559_:
{
lean_object* v_size_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_size_561_ = lean_ctor_get(v_acc_538_, 0);
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_add(v_size_561_, v___x_562_);
v___x_564_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_538_, v___x_563_, v_i_560_, v_val_557_, v_val_558_);
lean_dec(v_i_560_);
v___y_541_ = v___x_564_;
goto v___jp_540_;
}
}
}
}
v___jp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_add(v_i_539_, v___x_542_);
lean_dec(v_i_539_);
v_acc_538_ = v___y_541_;
v_i_539_ = v___x_543_;
goto _start;
}
v___jp_545_:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_unsigned_to_nat(1u);
v___x_547_ = lean_nat_add(v_i_539_, v___x_546_);
lean_dec(v_i_539_);
v_i_539_ = v___x_547_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_573_, lean_object* v_acc_574_, lean_object* v_i_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4_spec__5___redArg(v_b_573_, v_acc_574_, v_i_575_);
lean_dec_ref(v_b_573_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4___redArg(lean_object* v_init_577_, lean_object* v_b_578_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4_spec__5___redArg(v_b_578_, v_init_577_, v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4___redArg___boxed(lean_object* v_init_581_, lean_object* v_b_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4___redArg(v_init_581_, v_b_582_);
lean_dec_ref(v_b_582_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg(lean_object* v_m_584_){
_start:
{
lean_object* v_keyArray_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v_cellCount_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v_target_592_; lean_object* v___x_593_; 
v_keyArray_585_ = lean_ctor_get(v_m_584_, 1);
v___x_586_ = lean_array_get_size(v_keyArray_585_);
v___x_587_ = lean_unsigned_to_nat(2u);
v_cellCount_588_ = lean_nat_mul(v___x_586_, v___x_587_);
v___x_589_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_588_);
v___x_590_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_588_);
v___x_591_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_588_);
v_target_592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_592_, 0, v___x_589_);
lean_ctor_set(v_target_592_, 1, v___x_590_);
lean_ctor_set(v_target_592_, 2, v___x_591_);
v___x_593_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4___redArg(v_target_592_, v_m_584_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg___boxed(lean_object* v_m_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg(v_m_594_);
lean_dec_ref(v_m_594_);
return v_res_595_;
}
}
static lean_object* _init_l_Lean_registerBuiltinAttribute___closed__1(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__0));
v___x_598_ = lean_mk_io_user_error(v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute(lean_object* v_attr_601_){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v_toAttributeImplCore_605_; lean_object* v_name_606_; uint8_t v___x_607_; 
v___x_603_ = l_Lean_attributeMapRef;
v___x_604_ = lean_st_ref_get(v___x_603_);
v_toAttributeImplCore_605_ = lean_ctor_get(v_attr_601_, 0);
v_name_606_ = lean_ctor_get(v_toAttributeImplCore_605_, 1);
lean_inc(v_name_606_);
v___x_607_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_604_, v_name_606_);
lean_dec(v___x_604_);
if (v___x_607_ == 0)
{
uint8_t v___x_608_; 
v___x_608_ = l_Lean_initializing();
if (v___x_608_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec(v_name_606_);
lean_dec_ref(v_attr_601_);
v___x_609_ = lean_obj_once(&l_Lean_registerBuiltinAttribute___closed__1, &l_Lean_registerBuiltinAttribute___closed__1_once, _init_l_Lean_registerBuiltinAttribute___closed__1);
v___x_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
else
{
lean_object* v___x_611_; lean_object* v___y_613_; lean_object* v___y_617_; lean_object* v_i_618_; lean_object* v___y_624_; lean_object* v___y_634_; lean_object* v_i_635_; lean_object* v___x_650_; 
v___x_611_ = lean_st_ref_take(v___x_603_);
v___x_650_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_611_, v_name_606_);
switch(lean_obj_tag(v___x_650_))
{
case 0:
{
lean_object* v_index_651_; lean_object* v_size_652_; lean_object* v___x_653_; 
v_index_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_index_651_);
lean_dec_ref_known(v___x_650_, 3);
v_size_652_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_size_652_);
v___x_653_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_611_, v_size_652_, v_index_651_, v_name_606_, v_attr_601_);
lean_dec(v_index_651_);
v___y_613_ = v___x_653_;
goto v___jp_612_;
}
case 1:
{
lean_object* v_index_654_; lean_object* v_size_655_; lean_object* v_keyArray_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v_index_654_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_index_654_);
lean_dec_ref_known(v___x_650_, 1);
v_size_655_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_size_655_);
v_keyArray_656_ = lean_ctor_get(v___x_611_, 1);
lean_inc_ref(v_keyArray_656_);
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = lean_nat_add(v_size_655_, v___x_657_);
lean_dec(v_size_655_);
v___x_659_ = lean_array_get_size(v_keyArray_656_);
lean_dec_ref(v_keyArray_656_);
v___x_660_ = lean_nat_dec_lt(v___x_658_, v___x_659_);
if (v___x_660_ == 0)
{
lean_dec(v___x_658_);
lean_dec(v_index_654_);
goto v___jp_640_;
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_661_ = lean_unsigned_to_nat(4u);
v___x_662_ = lean_nat_mul(v___x_658_, v___x_661_);
v___x_663_ = lean_unsigned_to_nat(3u);
v___x_664_ = lean_nat_mul(v___x_659_, v___x_663_);
v___x_665_ = lean_nat_dec_le(v___x_662_, v___x_664_);
lean_dec(v___x_664_);
lean_dec(v___x_662_);
if (v___x_665_ == 0)
{
lean_dec(v___x_658_);
lean_dec(v_index_654_);
goto v___jp_640_;
}
else
{
lean_object* v___x_666_; 
v___x_666_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_611_, v___x_658_, v_index_654_, v_name_606_, v_attr_601_);
lean_dec(v_index_654_);
v___y_613_ = v___x_666_;
goto v___jp_612_;
}
}
}
default: 
{
lean_object* v_size_667_; lean_object* v_keyArray_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v_size_667_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_size_667_);
v_keyArray_668_ = lean_ctor_get(v___x_611_, 1);
lean_inc_ref(v_keyArray_668_);
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = lean_nat_add(v_size_667_, v___x_669_);
lean_dec(v_size_667_);
v___x_671_ = lean_array_get_size(v_keyArray_668_);
lean_dec_ref(v_keyArray_668_);
v___x_672_ = lean_nat_dec_lt(v___x_670_, v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
lean_dec(v___x_670_);
v___x_673_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg(v___x_611_);
lean_dec(v___x_611_);
v___y_624_ = v___x_673_;
goto v___jp_623_;
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_674_ = lean_unsigned_to_nat(4u);
v___x_675_ = lean_nat_mul(v___x_670_, v___x_674_);
lean_dec(v___x_670_);
v___x_676_ = lean_unsigned_to_nat(3u);
v___x_677_ = lean_nat_mul(v___x_671_, v___x_676_);
v___x_678_ = lean_nat_dec_le(v___x_675_, v___x_677_);
lean_dec(v___x_677_);
lean_dec(v___x_675_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg(v___x_611_);
lean_dec(v___x_611_);
v___y_624_ = v___x_679_;
goto v___jp_623_;
}
else
{
v___y_624_ = v___x_611_;
goto v___jp_623_;
}
}
}
}
v___jp_612_:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_st_ref_put(v___x_603_, v___y_613_);
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
v___jp_616_:
{
lean_object* v_size_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_size_619_ = lean_ctor_get(v___y_617_, 0);
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = lean_nat_add(v_size_619_, v___x_620_);
v___x_622_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_617_, v___x_621_, v_i_618_, v_name_606_, v_attr_601_);
lean_dec(v_i_618_);
v___y_613_ = v___x_622_;
goto v___jp_612_;
}
v___jp_623_:
{
lean_object* v___x_625_; 
v___x_625_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___y_624_, v_name_606_);
switch(lean_obj_tag(v___x_625_))
{
case 0:
{
lean_object* v_index_626_; lean_object* v_size_627_; lean_object* v___x_628_; 
v_index_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_index_626_);
lean_dec_ref_known(v___x_625_, 3);
v_size_627_ = lean_ctor_get(v___y_624_, 0);
lean_inc(v_size_627_);
v___x_628_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_624_, v_size_627_, v_index_626_, v_name_606_, v_attr_601_);
lean_dec(v_index_626_);
v___y_613_ = v___x_628_;
goto v___jp_612_;
}
case 1:
{
lean_object* v_index_629_; 
v_index_629_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_index_629_);
lean_dec_ref_known(v___x_625_, 1);
v___y_617_ = v___y_624_;
v_i_618_ = v_index_629_;
goto v___jp_616_;
}
default: 
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_624_, v___x_630_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_index_632_; 
v_index_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_index_632_);
lean_dec_ref_known(v___x_631_, 1);
v___y_617_ = v___y_624_;
v_i_618_ = v_index_632_;
goto v___jp_616_;
}
else
{
lean_dec(v_name_606_);
lean_dec_ref(v_attr_601_);
v___y_613_ = v___y_624_;
goto v___jp_612_;
}
}
}
}
v___jp_633_:
{
lean_object* v_size_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_size_636_ = lean_ctor_get(v___y_634_, 0);
v___x_637_ = lean_unsigned_to_nat(1u);
v___x_638_ = lean_nat_add(v_size_636_, v___x_637_);
v___x_639_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_634_, v___x_638_, v_i_635_, v_name_606_, v_attr_601_);
lean_dec(v_i_635_);
v___y_613_ = v___x_639_;
goto v___jp_612_;
}
v___jp_640_:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg(v___x_611_);
lean_dec(v___x_611_);
v___x_642_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_641_, v_name_606_);
switch(lean_obj_tag(v___x_642_))
{
case 0:
{
lean_object* v_index_643_; lean_object* v_size_644_; lean_object* v___x_645_; 
v_index_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_index_643_);
lean_dec_ref_known(v___x_642_, 3);
v_size_644_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_size_644_);
v___x_645_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_641_, v_size_644_, v_index_643_, v_name_606_, v_attr_601_);
lean_dec(v_index_643_);
v___y_613_ = v___x_645_;
goto v___jp_612_;
}
case 1:
{
lean_object* v_index_646_; 
v_index_646_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_index_646_);
lean_dec_ref_known(v___x_642_, 1);
v___y_634_ = v___x_641_;
v_i_635_ = v_index_646_;
goto v___jp_633_;
}
default: 
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_641_, v___x_647_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_index_649_; 
v_index_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_index_649_);
lean_dec_ref_known(v___x_648_, 1);
v___y_634_ = v___x_641_;
v_i_635_ = v_index_649_;
goto v___jp_633_;
}
else
{
lean_dec(v_name_606_);
lean_dec_ref(v_attr_601_);
v___y_613_ = v___x_641_;
goto v___jp_612_;
}
}
}
}
}
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
lean_dec_ref(v_attr_601_);
v___x_680_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_681_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_606_, v___x_607_);
v___x_682_ = lean_string_append(v___x_680_, v___x_681_);
lean_dec_ref(v___x_681_);
v___x_683_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_684_ = lean_string_append(v___x_682_, v___x_683_);
v___x_685_ = lean_mk_io_user_error(v___x_684_);
v___x_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute___boxed(lean_object* v_attr_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_registerBuiltinAttribute(v_attr_687_);
return v_res_689_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(lean_object* v_00_u03b2_690_, lean_object* v_m_691_, lean_object* v_a_692_){
_start:
{
uint8_t v___x_693_; 
v___x_693_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_691_, v_a_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___boxed(lean_object* v_00_u03b2_694_, lean_object* v_m_695_, lean_object* v_a_696_){
_start:
{
uint8_t v_res_697_; lean_object* v_r_698_; 
v_res_697_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(v_00_u03b2_694_, v_m_695_, v_a_696_);
lean_dec(v_a_696_);
lean_dec_ref(v_m_695_);
v_r_698_ = lean_box(v_res_697_);
return v_r_698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1(lean_object* v_00_u03b2_699_, lean_object* v_m_700_, lean_object* v_query_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_m_700_, v_query_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___boxed(lean_object* v_00_u03b2_703_, lean_object* v_m_704_, lean_object* v_query_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1(v_00_u03b2_703_, v_m_704_, v_query_705_);
lean_dec(v_query_705_);
lean_dec_ref(v_m_704_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2(lean_object* v_00_u03b2_707_, lean_object* v_m_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg(v_m_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___boxed(lean_object* v_00_u03b2_710_, lean_object* v_m_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2(v_00_u03b2_710_, v_m_711_);
lean_dec_ref(v_m_711_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_object* v_00_u03b2_713_, lean_object* v_m_714_, lean_object* v_query_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_m_714_, v_query_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___boxed(lean_object* v_00_u03b2_717_, lean_object* v_m_718_, lean_object* v_query_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(v_00_u03b2_717_, v_m_718_, v_query_719_);
lean_dec(v_query_719_);
lean_dec_ref(v_m_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(lean_object* v_00_u03b2_721_, lean_object* v_m_722_, lean_object* v_query_723_, lean_object* v_x_724_, lean_object* v_x_725_, lean_object* v_x_726_, lean_object* v_x_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_m_722_, v_query_723_, v_x_724_, v_x_725_, v_x_726_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___boxed(lean_object* v_00_u03b2_729_, lean_object* v_m_730_, lean_object* v_query_731_, lean_object* v_x_732_, lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v_x_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(v_00_u03b2_729_, v_m_730_, v_query_731_, v_x_732_, v_x_733_, v_x_734_, v_x_735_);
lean_dec(v_query_731_);
lean_dec_ref(v_m_730_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4(lean_object* v_00_u03b2_737_, lean_object* v_init_738_, lean_object* v_b_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4___redArg(v_init_738_, v_b_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4___boxed(lean_object* v_00_u03b2_741_, lean_object* v_init_742_, lean_object* v_b_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4(v_00_u03b2_741_, v_init_742_, v_b_743_);
lean_dec_ref(v_b_743_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_745_, lean_object* v_b_746_, lean_object* v_acc_747_, lean_object* v_i_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4_spec__5___redArg(v_b_746_, v_acc_747_, v_i_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_750_, lean_object* v_b_751_, lean_object* v_acc_752_, lean_object* v_i_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2_spec__4_spec__5(v_00_u03b2_750_, v_b_751_, v_acc_752_, v_i_753_);
lean_dec_ref(v_b_751_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object* v_ref_755_, lean_object* v_msg_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_fileName_760_; lean_object* v_fileMap_761_; lean_object* v_options_762_; lean_object* v_currRecDepth_763_; lean_object* v_maxRecDepth_764_; lean_object* v_ref_765_; lean_object* v_currNamespace_766_; lean_object* v_openDecls_767_; lean_object* v_initHeartbeats_768_; lean_object* v_maxHeartbeats_769_; lean_object* v_quotContext_770_; lean_object* v_currMacroScope_771_; uint8_t v_diag_772_; lean_object* v_cancelTk_x3f_773_; uint8_t v_suppressElabErrors_774_; lean_object* v_inheritedTraceOptions_775_; lean_object* v_ref_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v_fileName_760_ = lean_ctor_get(v___y_757_, 0);
v_fileMap_761_ = lean_ctor_get(v___y_757_, 1);
v_options_762_ = lean_ctor_get(v___y_757_, 2);
v_currRecDepth_763_ = lean_ctor_get(v___y_757_, 3);
v_maxRecDepth_764_ = lean_ctor_get(v___y_757_, 4);
v_ref_765_ = lean_ctor_get(v___y_757_, 5);
v_currNamespace_766_ = lean_ctor_get(v___y_757_, 6);
v_openDecls_767_ = lean_ctor_get(v___y_757_, 7);
v_initHeartbeats_768_ = lean_ctor_get(v___y_757_, 8);
v_maxHeartbeats_769_ = lean_ctor_get(v___y_757_, 9);
v_quotContext_770_ = lean_ctor_get(v___y_757_, 10);
v_currMacroScope_771_ = lean_ctor_get(v___y_757_, 11);
v_diag_772_ = lean_ctor_get_uint8(v___y_757_, sizeof(void*)*14);
v_cancelTk_x3f_773_ = lean_ctor_get(v___y_757_, 12);
v_suppressElabErrors_774_ = lean_ctor_get_uint8(v___y_757_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_775_ = lean_ctor_get(v___y_757_, 13);
v_ref_776_ = l_Lean_replaceRef(v_ref_755_, v_ref_765_);
lean_inc_ref(v_inheritedTraceOptions_775_);
lean_inc(v_cancelTk_x3f_773_);
lean_inc(v_currMacroScope_771_);
lean_inc(v_quotContext_770_);
lean_inc(v_maxHeartbeats_769_);
lean_inc(v_initHeartbeats_768_);
lean_inc(v_openDecls_767_);
lean_inc(v_currNamespace_766_);
lean_inc(v_maxRecDepth_764_);
lean_inc(v_currRecDepth_763_);
lean_inc_ref(v_options_762_);
lean_inc_ref(v_fileMap_761_);
lean_inc_ref(v_fileName_760_);
v___x_777_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_777_, 0, v_fileName_760_);
lean_ctor_set(v___x_777_, 1, v_fileMap_761_);
lean_ctor_set(v___x_777_, 2, v_options_762_);
lean_ctor_set(v___x_777_, 3, v_currRecDepth_763_);
lean_ctor_set(v___x_777_, 4, v_maxRecDepth_764_);
lean_ctor_set(v___x_777_, 5, v_ref_776_);
lean_ctor_set(v___x_777_, 6, v_currNamespace_766_);
lean_ctor_set(v___x_777_, 7, v_openDecls_767_);
lean_ctor_set(v___x_777_, 8, v_initHeartbeats_768_);
lean_ctor_set(v___x_777_, 9, v_maxHeartbeats_769_);
lean_ctor_set(v___x_777_, 10, v_quotContext_770_);
lean_ctor_set(v___x_777_, 11, v_currMacroScope_771_);
lean_ctor_set(v___x_777_, 12, v_cancelTk_x3f_773_);
lean_ctor_set(v___x_777_, 13, v_inheritedTraceOptions_775_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*14, v_diag_772_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*14 + 1, v_suppressElabErrors_774_);
v___x_778_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_756_, v___x_777_, v___y_758_);
lean_dec_ref_known(v___x_777_, 14);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object* v_ref_779_, lean_object* v_msg_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_779_, v_msg_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v_ref_779_);
return v_res_784_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__3));
v___x_794_ = l_Lean_stringToMessageData(v___x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object* v_stx_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v___x_805_; uint8_t v___y_816_; lean_object* v___x_822_; uint8_t v___x_823_; 
lean_inc(v_stx_801_);
v___x_805_ = l_Lean_Syntax_getKind(v_stx_801_);
v___x_822_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_823_ = lean_name_eq(v___x_805_, v___x_822_);
if (v___x_823_ == 0)
{
v___y_816_ = v___x_823_;
goto v___jp_815_;
}
else
{
lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_824_ = lean_unsigned_to_nat(1u);
v___x_825_ = l_Lean_Syntax_getArg(v_stx_801_, v___x_824_);
v___x_826_ = l_Lean_Syntax_isNone(v___x_825_);
lean_dec(v___x_825_);
v___y_816_ = v___x_826_;
goto v___jp_815_;
}
v___jp_806_:
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__2));
v___x_808_ = lean_name_eq(v___x_805_, v___x_807_);
lean_dec(v___x_805_);
if (v___x_808_ == 0)
{
if (lean_obj_tag(v_stx_801_) == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = lean_box(0);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
else
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_obj_once(&l_Lean_Attribute_Builtin_ensureNoArgs___closed__4, &l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once, _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4);
v___x_812_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_801_, v___x_811_, v_a_802_, v_a_803_);
lean_dec(v_stx_801_);
return v___x_812_;
}
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; 
lean_dec(v_stx_801_);
v___x_813_ = lean_box(0);
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
}
}
v___jp_815_:
{
if (v___y_816_ == 0)
{
goto v___jp_806_;
}
else
{
lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_817_ = lean_unsigned_to_nat(2u);
v___x_818_ = l_Lean_Syntax_getArg(v_stx_801_, v___x_817_);
v___x_819_ = l_Lean_Syntax_isNone(v___x_818_);
lean_dec(v___x_818_);
if (v___x_819_ == 0)
{
goto v___jp_806_;
}
else
{
lean_object* v___x_820_; lean_object* v___x_821_; 
lean_dec(v___x_805_);
lean_dec(v_stx_801_);
v___x_820_ = lean_box(0);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object* v_stx_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_827_, v_a_828_, v_a_829_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object* v_00_u03b1_832_, lean_object* v_ref_833_, lean_object* v_msg_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_833_, v_msg_834_, v___y_835_, v___y_836_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object* v_00_u03b1_839_, lean_object* v_ref_840_, lean_object* v_msg_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(v_00_u03b1_839_, v_ref_840_, v_msg_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v_ref_840_);
return v_res_845_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__4));
v___x_860_ = l_Lean_stringToMessageData(v___x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object* v_stx_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
lean_inc(v_stx_861_);
v___x_873_ = l_Lean_Syntax_getKind(v_stx_861_);
v___x_874_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_875_ = lean_name_eq(v___x_873_, v___x_874_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_876_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_877_ = lean_name_eq(v___x_873_, v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_878_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_879_ = lean_name_eq(v___x_873_, v___x_878_);
lean_dec(v___x_873_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_881_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_861_, v___x_880_, v_a_862_, v_a_863_);
lean_dec(v_stx_861_);
return v___x_881_;
}
else
{
goto v___jp_865_;
}
}
else
{
lean_dec(v___x_873_);
goto v___jp_865_;
}
}
else
{
lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
lean_dec(v___x_873_);
v___x_882_ = lean_unsigned_to_nat(1u);
v___x_883_ = l_Lean_Syntax_getArg(v_stx_861_, v___x_882_);
lean_dec(v_stx_861_);
v___x_884_ = l_Lean_Syntax_isNone(v___x_883_);
if (v___x_884_ == 0)
{
if (v___x_875_ == 0)
{
lean_dec(v___x_883_);
goto v___jp_870_;
}
else
{
lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_885_ = lean_unsigned_to_nat(0u);
v___x_886_ = l_Lean_Syntax_getArg(v___x_883_, v___x_885_);
lean_dec(v___x_883_);
v___x_887_ = l_Lean_Syntax_isIdent(v___x_886_);
if (v___x_887_ == 0)
{
lean_dec(v___x_886_);
goto v___jp_870_;
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
}
}
else
{
lean_dec(v___x_883_);
goto v___jp_870_;
}
}
v___jp_865_:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_866_ = lean_unsigned_to_nat(1u);
v___x_867_ = l_Lean_Syntax_getArg(v_stx_861_, v___x_866_);
lean_dec(v_stx_861_);
v___x_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
v___jp_870_:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_box(0);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object* v_stx_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_890_, v_a_891_, v_a_892_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
return v_res_894_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent___closed__1(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent___closed__0));
v___x_897_ = l_Lean_stringToMessageData(v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___x_902_; 
lean_inc(v_stx_898_);
v___x_902_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_898_, v_a_899_, v_a_900_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_916_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_916_ == 0)
{
v___x_905_ = v___x_902_;
v_isShared_906_ = v_isSharedCheck_916_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_902_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_916_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
if (lean_obj_tag(v_a_903_) == 0)
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
lean_del_object(v___x_905_);
v___x_907_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent___closed__1, &l_Lean_Attribute_Builtin_getIdent___closed__1_once, _init_l_Lean_Attribute_Builtin_getIdent___closed__1);
lean_inc(v_stx_898_);
v___x_908_ = l_Lean_MessageData_ofSyntax(v_stx_898_);
v___x_909_ = l_Lean_indentD(v___x_908_);
v___x_910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_907_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_898_, v___x_910_, v_a_899_, v_a_900_);
lean_dec(v_stx_898_);
return v___x_911_;
}
else
{
lean_object* v_val_912_; lean_object* v___x_914_; 
lean_dec(v_stx_898_);
v_val_912_ = lean_ctor_get(v_a_903_, 0);
lean_inc(v_val_912_);
lean_dec_ref_known(v_a_903_, 1);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v_val_912_);
v___x_914_ = v___x_905_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_val_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v_stx_898_);
v_a_917_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_902_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_902_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_Attribute_Builtin_getIdent(v_stx_925_, v_a_926_, v_a_927_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_930_, v_a_931_, v_a_932_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_955_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_955_ == 0)
{
v___x_937_ = v___x_934_;
v_isShared_938_ = v_isSharedCheck_955_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_934_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_955_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
if (lean_obj_tag(v_a_935_) == 0)
{
lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_939_ = lean_box(0);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_939_);
v___x_941_ = v___x_937_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
else
{
lean_object* v_val_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_954_; 
v_val_943_ = lean_ctor_get(v_a_935_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v_a_935_);
if (v_isSharedCheck_954_ == 0)
{
v___x_945_ = v_a_935_;
v_isShared_946_ = v_isSharedCheck_954_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_val_943_);
lean_dec(v_a_935_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_954_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_947_ = l_Lean_Syntax_getId(v_val_943_);
lean_dec(v_val_943_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_947_);
v___x_949_ = v___x_945_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_947_);
v___x_949_ = v_reuseFailAlloc_953_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_951_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_949_);
v___x_951_ = v___x_937_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
v_a_956_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_934_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_934_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_964_, v_a_965_, v_a_966_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_Attribute_Builtin_getIdent(v_stx_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_982_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_982_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = l_Lean_Syntax_getId(v_a_974_);
lean_dec(v_a_974_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_978_);
v___x_980_ = v___x_976_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
v_a_983_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_973_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_973_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
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
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_Attribute_Builtin_getId(v_stx_991_, v_a_992_, v_a_993_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
return v_res_995_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_998_ = l_Lean_stringToMessageData(v___x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
uint8_t v___x_1003_; 
v___x_1003_ = l_Lean_Syntax_isNone(v_optPrioStx_999_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = l_Lean_Syntax_getArg(v_optPrioStx_999_, v___x_1004_);
v___x_1006_ = l_Lean_Syntax_isNatLit_x3f(v___x_1005_);
lean_dec(v___x_1005_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1007_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_999_);
v___x_1008_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_999_);
v___x_1009_ = l_Lean_indentD(v___x_1008_);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1007_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_999_, v___x_1010_, v_a_1000_, v_a_1001_);
lean_dec(v_optPrioStx_999_);
return v___x_1011_;
}
else
{
lean_object* v_val_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_dec(v_optPrioStx_999_);
v_val_1012_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_1006_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_val_1012_);
lean_dec(v___x_1006_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set_tag(v___x_1014_, 0);
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_val_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
else
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_dec(v_optPrioStx_999_);
v___x_1020_ = lean_unsigned_to_nat(1000u);
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
return v___x_1021_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object* v_optPrioStx_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_1022_, v_a_1023_, v_a_1024_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
return v_res_1026_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getPrio___closed__1(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Lean_Attribute_Builtin_getPrio___closed__0));
v___x_1029_ = l_Lean_stringToMessageData(v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
lean_inc(v_stx_1030_);
v___x_1034_ = l_Lean_Syntax_getKind(v_stx_1030_);
v___x_1035_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_1036_ = lean_name_eq(v___x_1034_, v___x_1035_);
lean_dec(v___x_1034_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1037_ = lean_obj_once(&l_Lean_Attribute_Builtin_getPrio___closed__1, &l_Lean_Attribute_Builtin_getPrio___closed__1_once, _init_l_Lean_Attribute_Builtin_getPrio___closed__1);
lean_inc(v_stx_1030_);
v___x_1038_ = l_Lean_MessageData_ofSyntax(v_stx_1030_);
v___x_1039_ = l_Lean_indentD(v___x_1038_);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1037_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_1030_, v___x_1040_, v_a_1031_, v_a_1032_);
lean_dec(v_stx_1030_);
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1042_ = lean_unsigned_to_nat(1u);
v___x_1043_ = l_Lean_Syntax_getArg(v_stx_1030_, v___x_1042_);
lean_dec(v_stx_1030_);
v___x_1044_ = l_Lean_getAttrParamOptPrio(v___x_1043_, v_a_1031_, v_a_1032_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_Attribute_Builtin_getPrio(v_stx_1045_, v_a_1046_, v_a_1047_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
return v_res_1049_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_1052_ = l_Lean_stringToMessageData(v___x_1051_);
return v___x_1052_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_1055_ = l_Lean_stringToMessageData(v___x_1054_);
return v___x_1055_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_1058_ = l_Lean_stringToMessageData(v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_1059_, lean_object* v_inst_1060_, lean_object* v_name_1061_, uint8_t v_kind_1062_){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___y_1069_; 
v___x_1063_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1064_ = l_Lean_MessageData_ofName(v_name_1061_);
v___x_1065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
switch(v_kind_1062_)
{
case 0:
{
lean_object* v___x_1076_; 
v___x_1076_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1069_ = v___x_1076_;
goto v___jp_1068_;
}
case 1:
{
lean_object* v___x_1077_; 
v___x_1077_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1069_ = v___x_1077_;
goto v___jp_1068_;
}
default: 
{
lean_object* v___x_1078_; 
v___x_1078_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1069_ = v___x_1078_;
goto v___jp_1068_;
}
}
v___jp_1068_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_inc_ref(v___y_1069_);
v___x_1070_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___y_1069_);
v___x_1071_ = l_Lean_MessageData_ofFormat(v___x_1070_);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1067_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = l_Lean_throwError___redArg(v_inst_1059_, v_inst_1060_, v___x_1074_);
return v___x_1075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_1079_, lean_object* v_inst_1080_, lean_object* v_name_1081_, lean_object* v_kind_1082_){
_start:
{
uint8_t v_kind_boxed_1083_; lean_object* v_res_1084_; 
v_kind_boxed_1083_ = lean_unbox(v_kind_1082_);
v_res_1084_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_1079_, v_inst_1080_, v_name_1081_, v_kind_boxed_1083_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_1085_, lean_object* v_inst_1086_, lean_object* v_inst_1087_, lean_object* v_00_u03b1_1088_, lean_object* v_name_1089_, uint8_t v_kind_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_1086_, v_inst_1087_, v_name_1089_, v_kind_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_00_u03b1_1095_, lean_object* v_name_1096_, lean_object* v_kind_1097_){
_start:
{
uint8_t v_kind_boxed_1098_; lean_object* v_res_1099_; 
v_kind_boxed_1098_ = lean_unbox(v_kind_1097_);
v_res_1099_ = l_Lean_throwAttrMustBeGlobal(v_m_1092_, v_inst_1093_, v_inst_1094_, v_00_u03b1_1095_, v_name_1096_, v_kind_boxed_1098_);
return v_res_1099_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_1102_ = l_Lean_stringToMessageData(v___x_1101_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_1105_ = l_Lean_stringToMessageData(v___x_1104_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_1108_ = l_Lean_stringToMessageData(v___x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_1109_, lean_object* v_inst_1110_, lean_object* v_attrName_1111_, lean_object* v_declName_1112_){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1113_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1114_ = l_Lean_MessageData_ofName(v_attrName_1111_);
v___x_1115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1113_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v___x_1116_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1115_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = 0;
v___x_1119_ = l_Lean_MessageData_ofConstName(v_declName_1112_, v___x_1118_);
v___x_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1117_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = l_Lean_throwError___redArg(v_inst_1109_, v_inst_1110_, v___x_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1124_, lean_object* v_inst_1125_, lean_object* v_inst_1126_, lean_object* v_00_u03b1_1127_, lean_object* v_attrName_1128_, lean_object* v_declName_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1125_, v_inst_1126_, v_attrName_1128_, v_declName_1129_);
return v___x_1130_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1133_ = l_Lean_stringToMessageData(v___x_1132_);
return v___x_1133_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1136_ = l_Lean_stringToMessageData(v___x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_attrName_1139_, lean_object* v_declName_1140_, lean_object* v_asyncPrefix_x3f_1141_){
_start:
{
lean_object* v___y_1143_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1141_) == 0)
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_MessageData_nil;
v___y_1143_ = v___x_1156_;
goto v___jp_1142_;
}
else
{
lean_object* v_val_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_val_1157_ = lean_ctor_get(v_asyncPrefix_x3f_1141_, 0);
lean_inc(v_val_1157_);
lean_dec_ref_known(v_asyncPrefix_x3f_1141_, 1);
v___x_1158_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1159_ = l_Lean_MessageData_ofName(v_val_1157_);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1160_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___y_1143_ = v___x_1162_;
goto v___jp_1142_;
}
v___jp_1142_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1144_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1145_ = l_Lean_MessageData_ofName(v_attrName_1139_);
v___x_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1144_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1146_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = 0;
v___x_1150_ = l_Lean_MessageData_ofConstName(v_declName_1140_, v___x_1149_);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1148_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v___y_1143_);
v___x_1155_ = l_Lean_throwError___redArg(v_inst_1137_, v_inst_1138_, v___x_1154_);
return v___x_1155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_00_u03b1_1166_, lean_object* v_attrName_1167_, lean_object* v_declName_1168_, lean_object* v_asyncPrefix_x3f_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1164_, v_inst_1165_, v_attrName_1167_, v_declName_1168_, v_asyncPrefix_x3f_1169_);
return v___x_1170_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1173_ = l_Lean_stringToMessageData(v___x_1172_);
return v___x_1173_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1176_ = l_Lean_stringToMessageData(v___x_1175_);
return v___x_1176_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1179_ = l_Lean_stringToMessageData(v___x_1178_);
return v___x_1179_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1182_ = l_Lean_stringToMessageData(v___x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1183_, lean_object* v_inst_1184_, lean_object* v_attrName_1185_, lean_object* v_declName_1186_, lean_object* v_givenType_1187_, lean_object* v_expectedType_1188_){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1189_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1190_ = l_Lean_MessageData_ofName(v_attrName_1185_);
lean_inc_ref(v___x_1190_);
v___x_1191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = 0;
v___x_1195_ = l_Lean_MessageData_ofConstName(v_declName_1186_, v___x_1194_);
v___x_1196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1193_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1196_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = l_Lean_indentExpr(v_givenType_1187_);
v___x_1200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1198_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
lean_ctor_set(v___x_1203_, 1, v___x_1190_);
v___x_1204_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = l_Lean_indentExpr(v_expectedType_1188_);
v___x_1207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1205_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = l_Lean_throwError___redArg(v_inst_1183_, v_inst_1184_, v___x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1209_, lean_object* v_inst_1210_, lean_object* v_inst_1211_, lean_object* v_00_u03b1_1212_, lean_object* v_attrName_1213_, lean_object* v_declName_1214_, lean_object* v_givenType_1215_, lean_object* v_expectedType_1216_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1210_, v_inst_1211_, v_attrName_1213_, v_declName_1214_, v_givenType_1215_, v_expectedType_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1218_, uint8_t v_skipRealize_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___x_1222_; lean_object* v_env_1223_; uint8_t v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1222_ = lean_st_ref_get(v___y_1220_);
v_env_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc_ref(v_env_1223_);
lean_dec(v___x_1222_);
v___x_1224_ = l_Lean_Environment_contains(v_env_1223_, v_constName_1218_, v_skipRealize_1219_);
v___x_1225_ = lean_box(v___x_1224_);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object* v_constName_1227_, lean_object* v_skipRealize_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
uint8_t v_skipRealize_boxed_1231_; lean_object* v_res_1232_; 
v_skipRealize_boxed_1231_ = lean_unbox(v_skipRealize_1228_);
v_res_1232_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1227_, v_skipRealize_boxed_1231_, v___y_1229_);
lean_dec(v___y_1229_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1233_, uint8_t v_skipRealize_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1233_, v_skipRealize_1234_, v___y_1236_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1239_, lean_object* v_skipRealize_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
uint8_t v_skipRealize_boxed_1244_; lean_object* v_res_1245_; 
v_skipRealize_boxed_1244_ = lean_unbox(v_skipRealize_1240_);
v_res_1245_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1239_, v_skipRealize_boxed_1244_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1246_, uint8_t v_isExporting_1247_, lean_object* v___x_1248_, lean_object* v_a_x3f_1249_){
_start:
{
lean_object* v___x_1251_; lean_object* v_env_1252_; lean_object* v_nextMacroScope_1253_; lean_object* v_ngen_1254_; lean_object* v_auxDeclNGen_1255_; lean_object* v_traceState_1256_; lean_object* v_messages_1257_; lean_object* v_infoState_1258_; lean_object* v_snapshotTasks_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1270_; 
v___x_1251_ = lean_st_ref_take(v___y_1246_);
v_env_1252_ = lean_ctor_get(v___x_1251_, 0);
v_nextMacroScope_1253_ = lean_ctor_get(v___x_1251_, 1);
v_ngen_1254_ = lean_ctor_get(v___x_1251_, 2);
v_auxDeclNGen_1255_ = lean_ctor_get(v___x_1251_, 3);
v_traceState_1256_ = lean_ctor_get(v___x_1251_, 4);
v_messages_1257_ = lean_ctor_get(v___x_1251_, 6);
v_infoState_1258_ = lean_ctor_get(v___x_1251_, 7);
v_snapshotTasks_1259_ = lean_ctor_get(v___x_1251_, 8);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1270_ == 0)
{
lean_object* v_unused_1271_; 
v_unused_1271_ = lean_ctor_get(v___x_1251_, 5);
lean_dec(v_unused_1271_);
v___x_1261_ = v___x_1251_;
v_isShared_1262_ = v_isSharedCheck_1270_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_snapshotTasks_1259_);
lean_inc(v_infoState_1258_);
lean_inc(v_messages_1257_);
lean_inc(v_traceState_1256_);
lean_inc(v_auxDeclNGen_1255_);
lean_inc(v_ngen_1254_);
lean_inc(v_nextMacroScope_1253_);
lean_inc(v_env_1252_);
lean_dec(v___x_1251_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1270_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1263_ = l_Lean_Environment_setExporting(v_env_1252_, v_isExporting_1247_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 5, v___x_1248_);
lean_ctor_set(v___x_1261_, 0, v___x_1263_);
v___x_1265_ = v___x_1261_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_nextMacroScope_1253_);
lean_ctor_set(v_reuseFailAlloc_1269_, 2, v_ngen_1254_);
lean_ctor_set(v_reuseFailAlloc_1269_, 3, v_auxDeclNGen_1255_);
lean_ctor_set(v_reuseFailAlloc_1269_, 4, v_traceState_1256_);
lean_ctor_set(v_reuseFailAlloc_1269_, 5, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1269_, 6, v_messages_1257_);
lean_ctor_set(v_reuseFailAlloc_1269_, 7, v_infoState_1258_);
lean_ctor_set(v_reuseFailAlloc_1269_, 8, v_snapshotTasks_1259_);
v___x_1265_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1266_ = lean_st_ref_put(v___y_1246_, v___x_1265_);
v___x_1267_ = lean_box(0);
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
return v___x_1268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1272_, lean_object* v_isExporting_1273_, lean_object* v___x_1274_, lean_object* v_a_x3f_1275_, lean_object* v___y_1276_){
_start:
{
uint8_t v_isExporting_boxed_1277_; lean_object* v_res_1278_; 
v_isExporting_boxed_1277_ = lean_unbox(v_isExporting_1273_);
v_res_1278_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1272_, v_isExporting_boxed_1277_, v___x_1274_, v_a_x3f_1275_);
lean_dec(v_a_x3f_1275_);
lean_dec(v___y_1272_);
return v_res_1278_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1279_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
return v___x_1281_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1284_, uint8_t v_isExporting_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___x_1289_; lean_object* v_env_1290_; uint8_t v_isExporting_1291_; lean_object* v___x_1342_; uint8_t v_isModule_1343_; 
v___x_1289_ = lean_st_ref_get(v___y_1287_);
v_env_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc_ref(v_env_1290_);
lean_dec(v___x_1289_);
v_isExporting_1291_ = lean_ctor_get_uint8(v_env_1290_, sizeof(void*)*8);
v___x_1342_ = l_Lean_Environment_header(v_env_1290_);
lean_dec_ref(v_env_1290_);
v_isModule_1343_ = lean_ctor_get_uint8(v___x_1342_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1342_);
if (v_isModule_1343_ == 0)
{
lean_object* v___x_1344_; 
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
v___x_1344_ = lean_apply_3(v_x_1284_, v___y_1286_, v___y_1287_, lean_box(0));
return v___x_1344_;
}
else
{
if (v_isExporting_1291_ == 0)
{
if (v_isExporting_1285_ == 0)
{
lean_object* v___x_1345_; 
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
v___x_1345_ = lean_apply_3(v_x_1284_, v___y_1286_, v___y_1287_, lean_box(0));
return v___x_1345_;
}
else
{
goto v___jp_1292_;
}
}
else
{
if (v_isExporting_1285_ == 0)
{
goto v___jp_1292_;
}
else
{
lean_object* v___x_1346_; 
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
v___x_1346_ = lean_apply_3(v_x_1284_, v___y_1286_, v___y_1287_, lean_box(0));
return v___x_1346_;
}
}
}
v___jp_1292_:
{
lean_object* v___x_1293_; lean_object* v_env_1294_; lean_object* v_nextMacroScope_1295_; lean_object* v_ngen_1296_; lean_object* v_auxDeclNGen_1297_; lean_object* v_traceState_1298_; lean_object* v_messages_1299_; lean_object* v_infoState_1300_; lean_object* v_snapshotTasks_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1340_; 
v___x_1293_ = lean_st_ref_take(v___y_1287_);
v_env_1294_ = lean_ctor_get(v___x_1293_, 0);
v_nextMacroScope_1295_ = lean_ctor_get(v___x_1293_, 1);
v_ngen_1296_ = lean_ctor_get(v___x_1293_, 2);
v_auxDeclNGen_1297_ = lean_ctor_get(v___x_1293_, 3);
v_traceState_1298_ = lean_ctor_get(v___x_1293_, 4);
v_messages_1299_ = lean_ctor_get(v___x_1293_, 6);
v_infoState_1300_ = lean_ctor_get(v___x_1293_, 7);
v_snapshotTasks_1301_ = lean_ctor_get(v___x_1293_, 8);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; 
v_unused_1341_ = lean_ctor_get(v___x_1293_, 5);
lean_dec(v_unused_1341_);
v___x_1303_ = v___x_1293_;
v_isShared_1304_ = v_isSharedCheck_1340_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_snapshotTasks_1301_);
lean_inc(v_infoState_1300_);
lean_inc(v_messages_1299_);
lean_inc(v_traceState_1298_);
lean_inc(v_auxDeclNGen_1297_);
lean_inc(v_ngen_1296_);
lean_inc(v_nextMacroScope_1295_);
lean_inc(v_env_1294_);
lean_dec(v___x_1293_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1340_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1305_ = l_Lean_Environment_setExporting(v_env_1294_, v_isExporting_1285_);
v___x_1306_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 5, v___x_1306_);
lean_ctor_set(v___x_1303_, 0, v___x_1305_);
v___x_1308_ = v___x_1303_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1305_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_nextMacroScope_1295_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_ngen_1296_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v_auxDeclNGen_1297_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v_traceState_1298_);
lean_ctor_set(v_reuseFailAlloc_1339_, 5, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1339_, 6, v_messages_1299_);
lean_ctor_set(v_reuseFailAlloc_1339_, 7, v_infoState_1300_);
lean_ctor_set(v_reuseFailAlloc_1339_, 8, v_snapshotTasks_1301_);
v___x_1308_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_object* v___x_1309_; lean_object* v_r_1310_; 
v___x_1309_ = lean_st_ref_put(v___y_1287_, v___x_1308_);
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
v_r_1310_ = lean_apply_3(v_x_1284_, v___y_1286_, v___y_1287_, lean_box(0));
if (lean_obj_tag(v_r_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1327_; 
v_a_1311_ = lean_ctor_get(v_r_1310_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_r_1310_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1313_ = v_r_1310_;
v_isShared_1314_ = v_isSharedCheck_1327_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v_r_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1327_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
lean_inc(v_a_1311_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set_tag(v___x_1313_, 1);
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
v___x_1317_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1287_, v_isExporting_1291_, v___x_1306_, v___x_1316_);
lean_dec_ref(v___x_1316_);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; 
v_unused_1325_ = lean_ctor_get(v___x_1317_, 0);
lean_dec(v_unused_1325_);
v___x_1319_ = v___x_1317_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_dec(v___x_1317_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v_a_1311_);
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1311_);
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
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
v_a_1328_ = lean_ctor_get(v_r_1310_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v_r_1310_, 1);
v___x_1329_ = lean_box(0);
v___x_1330_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1287_, v_isExporting_1291_, v___x_1306_, v___x_1329_);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; 
v_unused_1338_ = lean_ctor_get(v___x_1330_, 0);
lean_dec(v_unused_1338_);
v___x_1332_ = v___x_1330_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_dec(v___x_1330_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
lean_ctor_set_tag(v___x_1332_, 1);
lean_ctor_set(v___x_1332_, 0, v_a_1328_);
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1328_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1347_, lean_object* v_isExporting_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
uint8_t v_isExporting_boxed_1352_; lean_object* v_res_1353_; 
v_isExporting_boxed_1352_ = lean_unbox(v_isExporting_1348_);
v_res_1353_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1347_, v_isExporting_boxed_1352_, v___y_1349_, v___y_1350_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1354_, lean_object* v_x_1355_, uint8_t v_isExporting_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1355_, v_isExporting_1356_, v___y_1357_, v___y_1358_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1361_, lean_object* v_x_1362_, lean_object* v_isExporting_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
uint8_t v_isExporting_boxed_1367_; lean_object* v_res_1368_; 
v_isExporting_boxed_1367_ = lean_unbox(v_isExporting_1363_);
v_res_1368_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1361_, v_x_1362_, v_isExporting_boxed_1367_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
return v_res_1368_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1369_, lean_object* v_opt_1370_){
_start:
{
lean_object* v_name_1371_; lean_object* v_defValue_1372_; lean_object* v_map_1373_; lean_object* v___x_1374_; 
v_name_1371_ = lean_ctor_get(v_opt_1370_, 0);
v_defValue_1372_ = lean_ctor_get(v_opt_1370_, 1);
v_map_1373_ = lean_ctor_get(v_opts_1369_, 0);
v___x_1374_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1373_, v_name_1371_);
if (lean_obj_tag(v___x_1374_) == 0)
{
uint8_t v___x_1375_; 
v___x_1375_ = lean_unbox(v_defValue_1372_);
return v___x_1375_;
}
else
{
lean_object* v_val_1376_; 
v_val_1376_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_val_1376_);
lean_dec_ref_known(v___x_1374_, 1);
if (lean_obj_tag(v_val_1376_) == 1)
{
uint8_t v_v_1377_; 
v_v_1377_ = lean_ctor_get_uint8(v_val_1376_, 0);
lean_dec_ref_known(v_val_1376_, 0);
return v_v_1377_;
}
else
{
uint8_t v___x_1378_; 
lean_dec(v_val_1376_);
v___x_1378_ = lean_unbox(v_defValue_1372_);
return v___x_1378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1379_, lean_object* v_opt_1380_){
_start:
{
uint8_t v_res_1381_; lean_object* v_r_1382_; 
v_res_1381_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1379_, v_opt_1380_);
lean_dec_ref(v_opt_1380_);
lean_dec_ref(v_opts_1379_);
v_r_1382_ = lean_box(v_res_1381_);
return v_r_1382_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v___y_1390_, uint8_t v_suppressElabErrors_1391_, lean_object* v_x_1392_){
_start:
{
if (lean_obj_tag(v_x_1392_) == 1)
{
lean_object* v_pre_1393_; 
v_pre_1393_ = lean_ctor_get(v_x_1392_, 0);
switch(lean_obj_tag(v_pre_1393_))
{
case 1:
{
lean_object* v_pre_1394_; 
v_pre_1394_ = lean_ctor_get(v_pre_1393_, 0);
switch(lean_obj_tag(v_pre_1394_))
{
case 0:
{
lean_object* v_str_1395_; lean_object* v_str_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v_str_1395_ = lean_ctor_get(v_x_1392_, 1);
v_str_1396_ = lean_ctor_get(v_pre_1393_, 1);
v___x_1397_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1398_ = lean_string_dec_eq(v_str_1396_, v___x_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1399_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1400_ = lean_string_dec_eq(v_str_1396_, v___x_1399_);
if (v___x_1400_ == 0)
{
return v___y_1390_;
}
else
{
lean_object* v___x_1401_; uint8_t v___x_1402_; 
v___x_1401_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1402_ = lean_string_dec_eq(v_str_1395_, v___x_1401_);
if (v___x_1402_ == 0)
{
return v___y_1390_;
}
else
{
return v_suppressElabErrors_1391_;
}
}
}
else
{
lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1403_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1404_ = lean_string_dec_eq(v_str_1395_, v___x_1403_);
if (v___x_1404_ == 0)
{
return v___y_1390_;
}
else
{
return v_suppressElabErrors_1391_;
}
}
}
case 1:
{
lean_object* v_pre_1405_; 
v_pre_1405_ = lean_ctor_get(v_pre_1394_, 0);
if (lean_obj_tag(v_pre_1405_) == 0)
{
lean_object* v_str_1406_; lean_object* v_str_1407_; lean_object* v_str_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v_str_1406_ = lean_ctor_get(v_x_1392_, 1);
v_str_1407_ = lean_ctor_get(v_pre_1393_, 1);
v_str_1408_ = lean_ctor_get(v_pre_1394_, 1);
v___x_1409_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1410_ = lean_string_dec_eq(v_str_1408_, v___x_1409_);
if (v___x_1410_ == 0)
{
return v___y_1390_;
}
else
{
lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1411_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1412_ = lean_string_dec_eq(v_str_1407_, v___x_1411_);
if (v___x_1412_ == 0)
{
return v___y_1390_;
}
else
{
lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1413_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1414_ = lean_string_dec_eq(v_str_1406_, v___x_1413_);
if (v___x_1414_ == 0)
{
return v___y_1390_;
}
else
{
return v_suppressElabErrors_1391_;
}
}
}
}
else
{
return v___y_1390_;
}
}
default: 
{
return v___y_1390_;
}
}
}
case 0:
{
lean_object* v_str_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v_str_1415_ = lean_ctor_get(v_x_1392_, 1);
v___x_1416_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1417_ = lean_string_dec_eq(v_str_1415_, v___x_1416_);
if (v___x_1417_ == 0)
{
return v___y_1390_;
}
else
{
return v_suppressElabErrors_1391_;
}
}
default: 
{
return v___y_1390_;
}
}
}
else
{
return v___y_1390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v___y_1418_, lean_object* v_suppressElabErrors_1419_, lean_object* v_x_1420_){
_start:
{
uint8_t v___y_4996__boxed_1421_; uint8_t v_suppressElabErrors_boxed_1422_; uint8_t v_res_1423_; lean_object* v_r_1424_; 
v___y_4996__boxed_1421_ = lean_unbox(v___y_1418_);
v_suppressElabErrors_boxed_1422_ = lean_unbox(v_suppressElabErrors_1419_);
v_res_1423_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v___y_4996__boxed_1421_, v_suppressElabErrors_boxed_1422_, v_x_1420_);
lean_dec(v_x_1420_);
v_r_1424_ = lean_box(v_res_1423_);
return v_r_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1425_, lean_object* v_msgData_1426_, uint8_t v_severity_1427_, uint8_t v_isSilent_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; uint8_t v___y_1437_; lean_object* v___y_1438_; uint8_t v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; uint8_t v___y_1472_; uint8_t v___y_1473_; lean_object* v___y_1474_; uint8_t v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; uint8_t v___y_1497_; uint8_t v___y_1498_; lean_object* v___y_1499_; uint8_t v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1505_; lean_object* v___y_1506_; uint8_t v___y_1507_; lean_object* v___y_1508_; uint8_t v___y_1509_; lean_object* v___y_1510_; uint8_t v___y_1511_; uint8_t v___x_1516_; lean_object* v___y_1518_; lean_object* v___y_1519_; uint8_t v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; uint8_t v___y_1523_; uint8_t v___y_1524_; uint8_t v___y_1526_; uint8_t v___x_1541_; 
v___x_1516_ = 2;
v___x_1541_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1427_, v___x_1516_);
if (v___x_1541_ == 0)
{
v___y_1526_ = v___x_1541_;
goto v___jp_1525_;
}
else
{
uint8_t v___x_1542_; 
lean_inc_ref(v_msgData_1426_);
v___x_1542_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1426_);
v___y_1526_ = v___x_1542_;
goto v___jp_1525_;
}
v___jp_1432_:
{
lean_object* v___x_1442_; lean_object* v_currNamespace_1443_; lean_object* v_openDecls_1444_; lean_object* v_env_1445_; lean_object* v_nextMacroScope_1446_; lean_object* v_ngen_1447_; lean_object* v_auxDeclNGen_1448_; lean_object* v_traceState_1449_; lean_object* v_cache_1450_; lean_object* v_messages_1451_; lean_object* v_infoState_1452_; lean_object* v_snapshotTasks_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1467_; 
v___x_1442_ = lean_st_ref_take(v___y_1441_);
v_currNamespace_1443_ = lean_ctor_get(v___y_1440_, 6);
v_openDecls_1444_ = lean_ctor_get(v___y_1440_, 7);
v_env_1445_ = lean_ctor_get(v___x_1442_, 0);
v_nextMacroScope_1446_ = lean_ctor_get(v___x_1442_, 1);
v_ngen_1447_ = lean_ctor_get(v___x_1442_, 2);
v_auxDeclNGen_1448_ = lean_ctor_get(v___x_1442_, 3);
v_traceState_1449_ = lean_ctor_get(v___x_1442_, 4);
v_cache_1450_ = lean_ctor_get(v___x_1442_, 5);
v_messages_1451_ = lean_ctor_get(v___x_1442_, 6);
v_infoState_1452_ = lean_ctor_get(v___x_1442_, 7);
v_snapshotTasks_1453_ = lean_ctor_get(v___x_1442_, 8);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1455_ = v___x_1442_;
v_isShared_1456_ = v_isSharedCheck_1467_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_snapshotTasks_1453_);
lean_inc(v_infoState_1452_);
lean_inc(v_messages_1451_);
lean_inc(v_cache_1450_);
lean_inc(v_traceState_1449_);
lean_inc(v_auxDeclNGen_1448_);
lean_inc(v_ngen_1447_);
lean_inc(v_nextMacroScope_1446_);
lean_inc(v_env_1445_);
lean_dec(v___x_1442_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1467_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
lean_inc(v_openDecls_1444_);
lean_inc(v_currNamespace_1443_);
v___x_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1457_, 0, v_currNamespace_1443_);
lean_ctor_set(v___x_1457_, 1, v_openDecls_1444_);
v___x_1458_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
lean_ctor_set(v___x_1458_, 1, v___y_1436_);
lean_inc_ref(v___y_1435_);
lean_inc_ref(v___y_1438_);
v___x_1459_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1459_, 0, v___y_1438_);
lean_ctor_set(v___x_1459_, 1, v___y_1434_);
lean_ctor_set(v___x_1459_, 2, v___y_1433_);
lean_ctor_set(v___x_1459_, 3, v___y_1435_);
lean_ctor_set(v___x_1459_, 4, v___x_1458_);
lean_ctor_set_uint8(v___x_1459_, sizeof(void*)*5, v___y_1437_);
lean_ctor_set_uint8(v___x_1459_, sizeof(void*)*5 + 1, v___y_1439_);
lean_ctor_set_uint8(v___x_1459_, sizeof(void*)*5 + 2, v_isSilent_1428_);
v___x_1460_ = l_Lean_MessageLog_add(v___x_1459_, v_messages_1451_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 6, v___x_1460_);
v___x_1462_ = v___x_1455_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_env_1445_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_nextMacroScope_1446_);
lean_ctor_set(v_reuseFailAlloc_1466_, 2, v_ngen_1447_);
lean_ctor_set(v_reuseFailAlloc_1466_, 3, v_auxDeclNGen_1448_);
lean_ctor_set(v_reuseFailAlloc_1466_, 4, v_traceState_1449_);
lean_ctor_set(v_reuseFailAlloc_1466_, 5, v_cache_1450_);
lean_ctor_set(v_reuseFailAlloc_1466_, 6, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1466_, 7, v_infoState_1452_);
lean_ctor_set(v_reuseFailAlloc_1466_, 8, v_snapshotTasks_1453_);
v___x_1462_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1463_ = lean_st_ref_put(v___y_1441_, v___x_1462_);
v___x_1464_ = lean_box(0);
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
return v___x_1465_;
}
}
}
v___jp_1468_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1492_; 
v___x_1477_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1426_);
v___x_1478_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v___x_1477_, v___y_1429_, v___y_1430_);
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1492_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1492_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
lean_inc_ref_n(v___y_1470_, 2);
v___x_1483_ = l_Lean_FileMap_toPosition(v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
v___x_1484_ = l_Lean_FileMap_toPosition(v___y_1470_, v___y_1476_);
lean_dec(v___y_1476_);
v___x_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
v___x_1486_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1472_ == 0)
{
lean_del_object(v___x_1481_);
lean_dec_ref(v___y_1469_);
v___y_1433_ = v___x_1485_;
v___y_1434_ = v___x_1483_;
v___y_1435_ = v___x_1486_;
v___y_1436_ = v_a_1479_;
v___y_1437_ = v___y_1473_;
v___y_1438_ = v___y_1474_;
v___y_1439_ = v___y_1475_;
v___y_1440_ = v___y_1429_;
v___y_1441_ = v___y_1430_;
goto v___jp_1432_;
}
else
{
uint8_t v___x_1487_; 
lean_inc(v_a_1479_);
v___x_1487_ = l_Lean_MessageData_hasTag(v___y_1469_, v_a_1479_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1490_; 
lean_dec_ref_known(v___x_1485_, 1);
lean_dec_ref(v___x_1483_);
lean_dec(v_a_1479_);
v___x_1488_ = lean_box(0);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1488_);
v___x_1490_ = v___x_1481_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
else
{
lean_del_object(v___x_1481_);
v___y_1433_ = v___x_1485_;
v___y_1434_ = v___x_1483_;
v___y_1435_ = v___x_1486_;
v___y_1436_ = v_a_1479_;
v___y_1437_ = v___y_1473_;
v___y_1438_ = v___y_1474_;
v___y_1439_ = v___y_1475_;
v___y_1440_ = v___y_1429_;
v___y_1441_ = v___y_1430_;
goto v___jp_1432_;
}
}
}
}
v___jp_1493_:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_Syntax_getTailPos_x3f(v___y_1495_, v___y_1498_);
lean_dec(v___y_1495_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_inc(v___y_1501_);
v___y_1469_ = v___y_1494_;
v___y_1470_ = v___y_1496_;
v___y_1471_ = v___y_1501_;
v___y_1472_ = v___y_1497_;
v___y_1473_ = v___y_1498_;
v___y_1474_ = v___y_1499_;
v___y_1475_ = v___y_1500_;
v___y_1476_ = v___y_1501_;
goto v___jp_1468_;
}
else
{
lean_object* v_val_1503_; 
v_val_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_val_1503_);
lean_dec_ref_known(v___x_1502_, 1);
v___y_1469_ = v___y_1494_;
v___y_1470_ = v___y_1496_;
v___y_1471_ = v___y_1501_;
v___y_1472_ = v___y_1497_;
v___y_1473_ = v___y_1498_;
v___y_1474_ = v___y_1499_;
v___y_1475_ = v___y_1500_;
v___y_1476_ = v_val_1503_;
goto v___jp_1468_;
}
}
v___jp_1504_:
{
lean_object* v_ref_1512_; lean_object* v___x_1513_; 
v_ref_1512_ = l_Lean_replaceRef(v_ref_1425_, v___y_1508_);
v___x_1513_ = l_Lean_Syntax_getPos_x3f(v_ref_1512_, v___y_1509_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_unsigned_to_nat(0u);
v___y_1494_ = v___y_1505_;
v___y_1495_ = v_ref_1512_;
v___y_1496_ = v___y_1506_;
v___y_1497_ = v___y_1507_;
v___y_1498_ = v___y_1509_;
v___y_1499_ = v___y_1510_;
v___y_1500_ = v___y_1511_;
v___y_1501_ = v___x_1514_;
goto v___jp_1493_;
}
else
{
lean_object* v_val_1515_; 
v_val_1515_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_val_1515_);
lean_dec_ref_known(v___x_1513_, 1);
v___y_1494_ = v___y_1505_;
v___y_1495_ = v_ref_1512_;
v___y_1496_ = v___y_1506_;
v___y_1497_ = v___y_1507_;
v___y_1498_ = v___y_1509_;
v___y_1499_ = v___y_1510_;
v___y_1500_ = v___y_1511_;
v___y_1501_ = v_val_1515_;
goto v___jp_1493_;
}
}
v___jp_1517_:
{
if (v___y_1524_ == 0)
{
v___y_1505_ = v___y_1518_;
v___y_1506_ = v___y_1519_;
v___y_1507_ = v___y_1520_;
v___y_1508_ = v___y_1521_;
v___y_1509_ = v___y_1523_;
v___y_1510_ = v___y_1522_;
v___y_1511_ = v_severity_1427_;
goto v___jp_1504_;
}
else
{
v___y_1505_ = v___y_1518_;
v___y_1506_ = v___y_1519_;
v___y_1507_ = v___y_1520_;
v___y_1508_ = v___y_1521_;
v___y_1509_ = v___y_1523_;
v___y_1510_ = v___y_1522_;
v___y_1511_ = v___x_1516_;
goto v___jp_1504_;
}
}
v___jp_1525_:
{
if (v___y_1526_ == 0)
{
lean_object* v_fileName_1527_; lean_object* v_fileMap_1528_; lean_object* v_options_1529_; lean_object* v_ref_1530_; uint8_t v_suppressElabErrors_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___f_1534_; uint8_t v___x_1535_; uint8_t v___x_1536_; 
v_fileName_1527_ = lean_ctor_get(v___y_1429_, 0);
v_fileMap_1528_ = lean_ctor_get(v___y_1429_, 1);
v_options_1529_ = lean_ctor_get(v___y_1429_, 2);
v_ref_1530_ = lean_ctor_get(v___y_1429_, 5);
v_suppressElabErrors_1531_ = lean_ctor_get_uint8(v___y_1429_, sizeof(void*)*14 + 1);
v___x_1532_ = lean_box(v___y_1526_);
v___x_1533_ = lean_box(v_suppressElabErrors_1531_);
v___f_1534_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1534_, 0, v___x_1532_);
lean_closure_set(v___f_1534_, 1, v___x_1533_);
v___x_1535_ = 1;
v___x_1536_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1427_, v___x_1535_);
if (v___x_1536_ == 0)
{
v___y_1518_ = v___f_1534_;
v___y_1519_ = v_fileMap_1528_;
v___y_1520_ = v_suppressElabErrors_1531_;
v___y_1521_ = v_ref_1530_;
v___y_1522_ = v_fileName_1527_;
v___y_1523_ = v___y_1526_;
v___y_1524_ = v___x_1536_;
goto v___jp_1517_;
}
else
{
lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1537_ = l_Lean_warningAsError;
v___x_1538_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1529_, v___x_1537_);
v___y_1518_ = v___f_1534_;
v___y_1519_ = v_fileMap_1528_;
v___y_1520_ = v_suppressElabErrors_1531_;
v___y_1521_ = v_ref_1530_;
v___y_1522_ = v_fileName_1527_;
v___y_1523_ = v___y_1526_;
v___y_1524_ = v___x_1538_;
goto v___jp_1517_;
}
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_dec_ref(v_msgData_1426_);
v___x_1539_ = lean_box(0);
v___x_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
return v___x_1540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1543_, lean_object* v_msgData_1544_, lean_object* v_severity_1545_, lean_object* v_isSilent_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
uint8_t v_severity_boxed_1550_; uint8_t v_isSilent_boxed_1551_; lean_object* v_res_1552_; 
v_severity_boxed_1550_ = lean_unbox(v_severity_1545_);
v_isSilent_boxed_1551_ = lean_unbox(v_isSilent_1546_);
v_res_1552_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1543_, v_msgData_1544_, v_severity_boxed_1550_, v_isSilent_boxed_1551_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v_ref_1543_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1553_, uint8_t v_severity_1554_, uint8_t v_isSilent_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_ref_1559_; lean_object* v___x_1560_; 
v_ref_1559_ = lean_ctor_get(v___y_1556_, 5);
v___x_1560_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1559_, v_msgData_1553_, v_severity_1554_, v_isSilent_1555_, v___y_1556_, v___y_1557_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1561_, lean_object* v_severity_1562_, lean_object* v_isSilent_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
uint8_t v_severity_boxed_1567_; uint8_t v_isSilent_boxed_1568_; lean_object* v_res_1569_; 
v_severity_boxed_1567_ = lean_unbox(v_severity_1562_);
v_isSilent_boxed_1568_ = lean_unbox(v_isSilent_1563_);
v_res_1569_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1561_, v_severity_boxed_1567_, v_isSilent_boxed_1568_, v___y_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
uint8_t v___x_1574_; uint8_t v___x_1575_; lean_object* v___x_1576_; 
v___x_1574_ = 1;
v___x_1575_ = 0;
v___x_1576_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1570_, v___x_1574_, v___x_1575_, v___y_1571_, v___y_1572_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_options_1585_; uint8_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v_options_1585_ = lean_ctor_get(v___y_1583_, 2);
v___x_1586_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1585_, v_opt_1582_);
v___x_1587_ = lean_box(v___x_1586_);
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1589_, v___y_1590_);
lean_dec_ref(v___y_1590_);
lean_dec_ref(v_opt_1589_);
return v_res_1592_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1595_ = l_Lean_stringToMessageData(v___x_1594_);
return v___x_1595_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1598_ = l_Lean_stringToMessageData(v___x_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v___x_1603_; lean_object* v_env_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1626_; 
v___x_1603_ = lean_st_ref_get(v___y_1601_);
v_env_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc_ref(v_env_1604_);
lean_dec(v___x_1603_);
v___x_1605_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1606_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1605_, v___y_1600_);
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1626_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1626_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
uint8_t v_isExporting_1616_; 
v_isExporting_1616_ = lean_ctor_get_uint8(v_env_1604_, sizeof(void*)*8);
lean_dec_ref(v_env_1604_);
if (v_isExporting_1616_ == 0)
{
lean_dec(v_a_1607_);
lean_dec(v_id_1599_);
goto v___jp_1611_;
}
else
{
uint8_t v___x_1617_; 
v___x_1617_ = l_Lean_isPrivateName(v_id_1599_);
if (v___x_1617_ == 0)
{
lean_dec(v_a_1607_);
lean_dec(v_id_1599_);
goto v___jp_1611_;
}
else
{
uint8_t v___x_1618_; 
v___x_1618_ = lean_unbox(v_a_1607_);
lean_dec(v_a_1607_);
if (v___x_1618_ == 0)
{
lean_dec(v_id_1599_);
goto v___jp_1611_;
}
else
{
lean_object* v___x_1619_; uint8_t v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_del_object(v___x_1609_);
v___x_1619_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1620_ = 0;
v___x_1621_ = l_Lean_MessageData_ofConstName(v_id_1599_, v___x_1620_);
v___x_1622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1619_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1624_, v___y_1600_, v___y_1601_);
return v___x_1625_;
}
}
}
v___jp_1611_:
{
lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1612_ = lean_box(0);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1612_);
v___x_1614_ = v___x_1609_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1612_);
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
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
return v_res_1631_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1634_ = l_Lean_stringToMessageData(v___x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1635_, uint8_t v_isModule_1636_, lean_object* v_attrName_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v___x_1641_; 
lean_inc(v_declName_1635_);
v___x_1641_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1635_, v___y_1638_, v___y_1639_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v___x_1642_; lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1663_; 
lean_dec_ref_known(v___x_1641_, 1);
lean_inc(v_declName_1635_);
v___x_1642_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1635_, v_isModule_1636_, v___y_1639_);
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1663_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1663_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
uint8_t v___x_1647_; 
v___x_1647_ = lean_unbox(v_a_1643_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
lean_del_object(v___x_1645_);
v___x_1648_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1649_ = l_Lean_MessageData_ofName(v_attrName_1637_);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1650_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = lean_unbox(v_a_1643_);
lean_dec(v_a_1643_);
v___x_1654_ = l_Lean_MessageData_ofConstName(v_declName_1635_, v___x_1653_);
v___x_1655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1652_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1657_, v___y_1638_, v___y_1639_);
return v___x_1658_;
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
lean_dec(v_a_1643_);
lean_dec(v_attrName_1637_);
lean_dec(v_declName_1635_);
v___x_1659_ = lean_box(0);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1659_);
v___x_1661_ = v___x_1645_;
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
lean_dec(v_attrName_1637_);
lean_dec(v_declName_1635_);
return v___x_1641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1664_, lean_object* v_isModule_1665_, lean_object* v_attrName_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
uint8_t v_isModule_boxed_1670_; lean_object* v_res_1671_; 
v_isModule_boxed_1670_ = lean_unbox(v_isModule_1665_);
v_res_1671_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1664_, v_isModule_boxed_1670_, v_attrName_1666_, v___y_1667_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1672_, lean_object* v_declName_1673_, uint8_t v_attrKind_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v___x_1678_; lean_object* v_env_1682_; lean_object* v___x_1683_; uint8_t v_isModule_1684_; 
v___x_1678_ = lean_st_ref_get(v_a_1676_);
v_env_1682_ = lean_ctor_get(v___x_1678_, 0);
lean_inc_ref(v_env_1682_);
lean_dec(v___x_1678_);
v___x_1683_ = l_Lean_Environment_header(v_env_1682_);
lean_dec_ref(v_env_1682_);
v_isModule_1684_ = lean_ctor_get_uint8(v___x_1683_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1683_);
if (v_isModule_1684_ == 0)
{
lean_dec(v_declName_1673_);
lean_dec(v_attrName_1672_);
goto v___jp_1679_;
}
else
{
uint8_t v___x_1685_; uint8_t v___x_1686_; 
v___x_1685_ = 1;
v___x_1686_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1674_, v___x_1685_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; lean_object* v___f_1688_; lean_object* v___x_1689_; 
v___x_1687_ = lean_box(v_isModule_1684_);
v___f_1688_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1688_, 0, v_declName_1673_);
lean_closure_set(v___f_1688_, 1, v___x_1687_);
lean_closure_set(v___f_1688_, 2, v_attrName_1672_);
v___x_1689_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1688_, v_isModule_1684_, v_a_1675_, v_a_1676_);
return v___x_1689_;
}
else
{
lean_dec(v_declName_1673_);
lean_dec(v_attrName_1672_);
goto v___jp_1679_;
}
}
v___jp_1679_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = lean_box(0);
v___x_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
return v___x_1681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1690_, lean_object* v_declName_1691_, lean_object* v_attrKind_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
uint8_t v_attrKind_boxed_1696_; lean_object* v_res_1697_; 
v_attrKind_boxed_1696_ = lean_unbox(v_attrKind_1692_);
v_res_1697_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1690_, v_declName_1691_, v_attrKind_boxed_1696_, v_a_1693_, v_a_1694_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1698_, v___y_1699_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec_ref(v_opt_1703_);
return v_res_1707_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1710_ = l_Lean_stringToMessageData(v___x_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1711_, lean_object* v_declName_1712_, uint8_t v_attrKind_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v_env_1719_; lean_object* v___x_1720_; uint8_t v_isModule_1721_; 
v___x_1717_ = lean_st_ref_get(v_a_1715_);
v___x_1718_ = lean_st_ref_get(v_a_1715_);
v_env_1719_ = lean_ctor_get(v___x_1717_, 0);
lean_inc_ref(v_env_1719_);
lean_dec(v___x_1717_);
v___x_1720_ = l_Lean_Environment_header(v_env_1719_);
lean_dec_ref(v_env_1719_);
v_isModule_1721_ = lean_ctor_get_uint8(v___x_1720_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1720_);
if (v_isModule_1721_ == 0)
{
lean_object* v___x_1722_; 
lean_dec(v___x_1718_);
v___x_1722_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1711_, v_declName_1712_, v_attrKind_1713_, v_a_1714_, v_a_1715_);
return v___x_1722_;
}
else
{
lean_object* v_env_1723_; uint8_t v___x_1724_; 
v_env_1723_ = lean_ctor_get(v___x_1718_, 0);
lean_inc_ref(v_env_1723_);
lean_dec(v___x_1718_);
lean_inc(v_declName_1712_);
v___x_1724_ = l_Lean_isMarkedMeta(v_env_1723_, v_declName_1712_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1725_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1726_ = l_Lean_MessageData_ofName(v_attrName_1711_);
v___x_1727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1725_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
v___x_1728_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1727_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
v___x_1730_ = l_Lean_MessageData_ofConstName(v_declName_1712_, v___x_1724_);
v___x_1731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1729_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1731_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1733_, v_a_1714_, v_a_1715_);
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1711_, v_declName_1712_, v_attrKind_1713_, v_a_1714_, v_a_1715_);
return v___x_1735_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1736_, lean_object* v_declName_1737_, lean_object* v_attrKind_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
uint8_t v_attrKind_boxed_1742_; lean_object* v_res_1743_; 
v_attrKind_boxed_1742_ = lean_unbox(v_attrKind_1738_);
v_res_1743_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1736_, v_declName_1737_, v_attrKind_boxed_1742_, v_a_1739_, v_a_1740_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1752_, v___y_1753_);
lean_dec_ref(v___y_1753_);
lean_dec_ref(v_x_1752_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1756_, lean_object* v_x_1757_){
_start:
{
lean_inc(v_s_1756_);
return v_s_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1758_, lean_object* v_x_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1758_, v_x_1759_);
lean_dec(v_x_1759_);
lean_dec(v_s_1758_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1765_, lean_object* v_x_1766_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1768_, lean_object* v_x_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1768_, v_x_1769_);
lean_dec(v_x_1769_);
lean_dec_ref(v_x_1768_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = lean_box(0);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1773_);
lean_dec(v_x_1773_);
return v_res_1774_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1779_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1780_; lean_object* v___f_1781_; lean_object* v___f_1782_; lean_object* v___f_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___f_1780_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1781_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1782_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1783_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1784_ = lean_box(0);
v___x_1785_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1786_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1785_);
lean_ctor_set(v___x_1786_, 1, v___x_1784_);
lean_ctor_set(v___x_1786_, 2, v___f_1783_);
lean_ctor_set(v___x_1786_, 3, v___f_1782_);
lean_ctor_set(v___x_1786_, 4, v___f_1781_);
lean_ctor_set(v___x_1786_, 5, v___f_1780_);
return v___x_1786_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1787_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1788_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
lean_ctor_set(v___x_1789_, 1, v___x_1787_);
return v___x_1789_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1790_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1791_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1793_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_registerTagAttribute___lam__0(v_x_1795_);
lean_dec(v_x_1795_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1797_, lean_object* v_x_1798_, lean_object* v_x_1799_){
_start:
{
if (lean_obj_tag(v_x_1799_) == 0)
{
return v_x_1798_;
}
else
{
lean_object* v_head_1800_; lean_object* v_tail_1801_; uint8_t v___x_1802_; 
v_head_1800_ = lean_ctor_get(v_x_1799_, 0);
lean_inc(v_head_1800_);
v_tail_1801_ = lean_ctor_get(v_x_1799_, 1);
lean_inc(v_tail_1801_);
lean_dec_ref_known(v_x_1799_, 2);
v___x_1802_ = l_Lean_NameSet_contains(v_newState_1797_, v_head_1800_);
if (v___x_1802_ == 0)
{
lean_dec(v_head_1800_);
v_x_1799_ = v_tail_1801_;
goto _start;
}
else
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Lean_NameSet_insert(v_x_1798_, v_head_1800_);
v_x_1798_ = v___x_1804_;
v_x_1799_ = v_tail_1801_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1806_, lean_object* v_x_1807_, lean_object* v_x_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1806_, v_x_1807_, v_x_1808_);
lean_dec(v_newState_1806_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1810_, lean_object* v_newState_1811_, lean_object* v_newConsts_1812_, lean_object* v_s_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1811_, v_s_1813_, v_newConsts_1812_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1815_, lean_object* v_newState_1816_, lean_object* v_newConsts_1817_, lean_object* v_s_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Lean_registerTagAttribute___lam__1(v_x_1815_, v_newState_1816_, v_newConsts_1817_, v_s_1818_);
lean_dec(v_newState_1816_);
lean_dec(v_x_1815_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1832_){
_start:
{
lean_object* v___x_1833_; lean_object* v___y_1835_; 
v___x_1833_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1832_) == 0)
{
lean_object* v_size_1839_; 
v_size_1839_ = lean_ctor_get(v_s_1832_, 0);
lean_inc(v_size_1839_);
lean_dec_ref_known(v_s_1832_, 5);
v___y_1835_ = v_size_1839_;
goto v___jp_1834_;
}
else
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_unsigned_to_nat(0u);
v___y_1835_ = v___x_1840_;
goto v___jp_1834_;
}
v___jp_1834_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1836_ = l_Nat_reprFast(v___y_1835_);
v___x_1837_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
v___x_1838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1833_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
return v___x_1838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1841_, lean_object* v_pivot_1842_, lean_object* v_as_1843_, lean_object* v_i_1844_, lean_object* v_k_1845_){
_start:
{
uint8_t v___x_1846_; 
v___x_1846_ = lean_nat_dec_lt(v_k_1845_, v_hi_1841_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_dec(v_k_1845_);
v___x_1847_ = lean_array_fswap(v_as_1843_, v_i_1844_, v_hi_1841_);
v___x_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1848_, 0, v_i_1844_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
return v___x_1848_;
}
else
{
lean_object* v___x_1849_; uint8_t v___x_1850_; 
v___x_1849_ = lean_array_fget_borrowed(v_as_1843_, v_k_1845_);
v___x_1850_ = l_Lean_Name_quickLt(v___x_1849_, v_pivot_1842_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = lean_unsigned_to_nat(1u);
v___x_1852_ = lean_nat_add(v_k_1845_, v___x_1851_);
lean_dec(v_k_1845_);
v_k_1845_ = v___x_1852_;
goto _start;
}
else
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1854_ = lean_array_fswap(v_as_1843_, v_i_1844_, v_k_1845_);
v___x_1855_ = lean_unsigned_to_nat(1u);
v___x_1856_ = lean_nat_add(v_i_1844_, v___x_1855_);
lean_dec(v_i_1844_);
v___x_1857_ = lean_nat_add(v_k_1845_, v___x_1855_);
lean_dec(v_k_1845_);
v_as_1843_ = v___x_1854_;
v_i_1844_ = v___x_1856_;
v_k_1845_ = v___x_1857_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1859_, lean_object* v_pivot_1860_, lean_object* v_as_1861_, lean_object* v_i_1862_, lean_object* v_k_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1859_, v_pivot_1860_, v_as_1861_, v_i_1862_, v_k_1863_);
lean_dec(v_pivot_1860_);
lean_dec(v_hi_1859_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1865_, lean_object* v_as_1866_, lean_object* v_lo_1867_, lean_object* v_hi_1868_){
_start:
{
lean_object* v___y_1870_; uint8_t v___x_1880_; 
v___x_1880_ = lean_nat_dec_lt(v_lo_1867_, v_hi_1868_);
if (v___x_1880_ == 0)
{
lean_dec(v_lo_1867_);
return v_as_1866_;
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v_mid_1883_; lean_object* v___y_1885_; lean_object* v___y_1891_; lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1881_ = lean_nat_add(v_lo_1867_, v_hi_1868_);
v___x_1882_ = lean_unsigned_to_nat(1u);
v_mid_1883_ = lean_nat_shiftr(v___x_1881_, v___x_1882_);
lean_dec(v___x_1881_);
v___x_1896_ = lean_array_fget_borrowed(v_as_1866_, v_mid_1883_);
v___x_1897_ = lean_array_fget_borrowed(v_as_1866_, v_lo_1867_);
v___x_1898_ = l_Lean_Name_quickLt(v___x_1896_, v___x_1897_);
if (v___x_1898_ == 0)
{
v___y_1891_ = v_as_1866_;
goto v___jp_1890_;
}
else
{
lean_object* v___x_1899_; 
v___x_1899_ = lean_array_fswap(v_as_1866_, v_lo_1867_, v_mid_1883_);
v___y_1891_ = v___x_1899_;
goto v___jp_1890_;
}
v___jp_1884_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; uint8_t v___x_1888_; 
v___x_1886_ = lean_array_fget_borrowed(v___y_1885_, v_mid_1883_);
v___x_1887_ = lean_array_fget_borrowed(v___y_1885_, v_hi_1868_);
v___x_1888_ = l_Lean_Name_quickLt(v___x_1886_, v___x_1887_);
if (v___x_1888_ == 0)
{
lean_dec(v_mid_1883_);
v___y_1870_ = v___y_1885_;
goto v___jp_1869_;
}
else
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_array_fswap(v___y_1885_, v_mid_1883_, v_hi_1868_);
lean_dec(v_mid_1883_);
v___y_1870_ = v___x_1889_;
goto v___jp_1869_;
}
}
v___jp_1890_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1892_ = lean_array_fget_borrowed(v___y_1891_, v_hi_1868_);
v___x_1893_ = lean_array_fget_borrowed(v___y_1891_, v_lo_1867_);
v___x_1894_ = l_Lean_Name_quickLt(v___x_1892_, v___x_1893_);
if (v___x_1894_ == 0)
{
v___y_1885_ = v___y_1891_;
goto v___jp_1884_;
}
else
{
lean_object* v___x_1895_; 
v___x_1895_ = lean_array_fswap(v___y_1891_, v_lo_1867_, v_hi_1868_);
v___y_1885_ = v___x_1895_;
goto v___jp_1884_;
}
}
}
v___jp_1869_:
{
lean_object* v_pivot_1871_; lean_object* v___x_1872_; lean_object* v_fst_1873_; lean_object* v_snd_1874_; uint8_t v___x_1875_; 
v_pivot_1871_ = lean_array_fget(v___y_1870_, v_hi_1868_);
lean_inc_n(v_lo_1867_, 2);
v___x_1872_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1868_, v_pivot_1871_, v___y_1870_, v_lo_1867_, v_lo_1867_);
lean_dec(v_pivot_1871_);
v_fst_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_fst_1873_);
v_snd_1874_ = lean_ctor_get(v___x_1872_, 1);
lean_inc(v_snd_1874_);
lean_dec_ref(v___x_1872_);
v___x_1875_ = lean_nat_dec_le(v_hi_1868_, v_fst_1873_);
if (v___x_1875_ == 0)
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1876_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1865_, v_snd_1874_, v_lo_1867_, v_fst_1873_);
v___x_1877_ = lean_unsigned_to_nat(1u);
v___x_1878_ = lean_nat_add(v_fst_1873_, v___x_1877_);
lean_dec(v_fst_1873_);
v_as_1866_ = v___x_1876_;
v_lo_1867_ = v___x_1878_;
goto _start;
}
else
{
lean_dec(v_fst_1873_);
lean_dec(v_lo_1867_);
return v_snd_1874_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1900_, lean_object* v_as_1901_, lean_object* v_lo_1902_, lean_object* v_hi_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1900_, v_as_1901_, v_lo_1902_, v_hi_1903_);
lean_dec(v_hi_1903_);
lean_dec(v_n_1900_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1905_, lean_object* v_as_1906_, size_t v_i_1907_, size_t v_stop_1908_, lean_object* v_b_1909_){
_start:
{
lean_object* v___y_1911_; uint8_t v___x_1915_; 
v___x_1915_ = lean_usize_dec_eq(v_i_1907_, v_stop_1908_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; uint8_t v___x_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; 
v___x_1916_ = lean_array_uget_borrowed(v_as_1906_, v_i_1907_);
v___x_1917_ = 1;
lean_inc_ref(v_env_1905_);
v___x_1918_ = l_Lean_Environment_setExporting(v_env_1905_, v___x_1917_);
lean_inc(v___x_1916_);
v___x_1919_ = l_Lean_Environment_contains(v___x_1918_, v___x_1916_, v___x_1915_);
if (v___x_1919_ == 0)
{
v___y_1911_ = v_b_1909_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_1920_; 
lean_inc(v___x_1916_);
v___x_1920_ = lean_array_push(v_b_1909_, v___x_1916_);
v___y_1911_ = v___x_1920_;
goto v___jp_1910_;
}
}
else
{
lean_dec_ref(v_env_1905_);
return v_b_1909_;
}
v___jp_1910_:
{
size_t v___x_1912_; size_t v___x_1913_; 
v___x_1912_ = ((size_t)1ULL);
v___x_1913_ = lean_usize_add(v_i_1907_, v___x_1912_);
v_i_1907_ = v___x_1913_;
v_b_1909_ = v___y_1911_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1921_, lean_object* v_as_1922_, lean_object* v_i_1923_, lean_object* v_stop_1924_, lean_object* v_b_1925_){
_start:
{
size_t v_i_boxed_1926_; size_t v_stop_boxed_1927_; lean_object* v_res_1928_; 
v_i_boxed_1926_ = lean_unbox_usize(v_i_1923_);
lean_dec(v_i_1923_);
v_stop_boxed_1927_ = lean_unbox_usize(v_stop_1924_);
lean_dec(v_stop_1924_);
v_res_1928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1921_, v_as_1922_, v_i_boxed_1926_, v_stop_boxed_1927_, v_b_1925_);
lean_dec_ref(v_as_1922_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1929_, lean_object* v_x_1930_){
_start:
{
if (lean_obj_tag(v_x_1930_) == 0)
{
lean_object* v_k_1931_; lean_object* v_l_1932_; lean_object* v_r_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v_k_1931_ = lean_ctor_get(v_x_1930_, 1);
lean_inc(v_k_1931_);
v_l_1932_ = lean_ctor_get(v_x_1930_, 3);
lean_inc(v_l_1932_);
v_r_1933_ = lean_ctor_get(v_x_1930_, 4);
lean_inc(v_r_1933_);
lean_dec_ref_known(v_x_1930_, 5);
v___x_1934_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1929_, v_l_1932_);
v___x_1935_ = lean_array_push(v___x_1934_, v_k_1931_);
v_init_1929_ = v___x_1935_;
v_x_1930_ = v_r_1933_;
goto _start;
}
else
{
return v_init_1929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1937_, lean_object* v_es_1938_){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___y_1942_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___y_1959_; lean_object* v___y_1960_; uint8_t v___x_1962_; 
v___x_1939_ = lean_unsigned_to_nat(0u);
v___x_1940_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1956_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1940_, v_es_1938_);
v___x_1957_ = lean_array_get_size(v___x_1956_);
v___x_1962_ = lean_nat_dec_eq(v___x_1957_, v___x_1939_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___y_1966_; uint8_t v___x_1968_; 
v___x_1963_ = lean_unsigned_to_nat(1u);
v___x_1964_ = lean_nat_sub(v___x_1957_, v___x_1963_);
v___x_1968_ = lean_nat_dec_le(v___x_1939_, v___x_1964_);
if (v___x_1968_ == 0)
{
lean_inc(v___x_1964_);
v___y_1966_ = v___x_1964_;
goto v___jp_1965_;
}
else
{
v___y_1966_ = v___x_1939_;
goto v___jp_1965_;
}
v___jp_1965_:
{
uint8_t v___x_1967_; 
v___x_1967_ = lean_nat_dec_le(v___y_1966_, v___x_1964_);
if (v___x_1967_ == 0)
{
lean_dec(v___x_1964_);
lean_inc(v___y_1966_);
v___y_1959_ = v___y_1966_;
v___y_1960_ = v___y_1966_;
goto v___jp_1958_;
}
else
{
v___y_1959_ = v___y_1966_;
v___y_1960_ = v___x_1964_;
goto v___jp_1958_;
}
}
}
else
{
v___y_1942_ = v___x_1956_;
goto v___jp_1941_;
}
v___jp_1941_:
{
lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1943_ = lean_array_get_size(v___y_1942_);
v___x_1944_ = lean_nat_dec_lt(v___x_1939_, v___x_1943_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; 
lean_dec_ref(v_env_1937_);
v___x_1945_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1940_);
lean_ctor_set(v___x_1945_, 1, v___x_1940_);
lean_ctor_set(v___x_1945_, 2, v___y_1942_);
return v___x_1945_;
}
else
{
uint8_t v___x_1946_; 
v___x_1946_ = lean_nat_dec_le(v___x_1943_, v___x_1943_);
if (v___x_1946_ == 0)
{
if (v___x_1944_ == 0)
{
lean_object* v___x_1947_; 
lean_dec_ref(v_env_1937_);
v___x_1947_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1940_);
lean_ctor_set(v___x_1947_, 1, v___x_1940_);
lean_ctor_set(v___x_1947_, 2, v___y_1942_);
return v___x_1947_;
}
else
{
size_t v___x_1948_; size_t v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1948_ = ((size_t)0ULL);
v___x_1949_ = lean_usize_of_nat(v___x_1943_);
v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1937_, v___y_1942_, v___x_1948_, v___x_1949_, v___x_1940_);
lean_inc_ref(v___x_1950_);
v___x_1951_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
lean_ctor_set(v___x_1951_, 2, v___y_1942_);
return v___x_1951_;
}
}
else
{
size_t v___x_1952_; size_t v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1952_ = ((size_t)0ULL);
v___x_1953_ = lean_usize_of_nat(v___x_1943_);
v___x_1954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1937_, v___y_1942_, v___x_1952_, v___x_1953_, v___x_1940_);
lean_inc_ref(v___x_1954_);
v___x_1955_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
lean_ctor_set(v___x_1955_, 2, v___y_1942_);
return v___x_1955_;
}
}
}
v___jp_1958_:
{
lean_object* v___x_1961_; 
v___x_1961_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1957_, v___x_1956_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
v___y_1942_ = v___x_1961_;
goto v___jp_1941_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v___x_1969_, lean_object* v_x_1970_, lean_object* v_x_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1969_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v___x_1974_, lean_object* v_x_1975_, lean_object* v_x_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_registerTagAttribute___lam__4(v___x_1974_, v_x_1975_, v_x_1976_);
lean_dec_ref(v_x_1976_);
lean_dec_ref(v_x_1975_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1979_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1979_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_registerTagAttribute___lam__5(v___x_1982_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v_name_1985_, lean_object* v_decl_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1990_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1991_ = l_Lean_MessageData_ofName(v_name_1985_);
v___x_1992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1990_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1994_, v___y_1987_, v___y_1988_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v_name_1996_, lean_object* v_decl_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_registerTagAttribute___lam__6(v_name_1996_, v_decl_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v_decl_1997_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_2002_, lean_object* v_declName_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2007_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_2008_ = l_Lean_MessageData_ofName(v_attrName_2002_);
v___x_2009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2007_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_2011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2009_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = 0;
v___x_2013_ = l_Lean_MessageData_ofConstName(v_declName_2003_, v___x_2012_);
v___x_2014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2011_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
v___x_2015_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_2016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2014_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v___x_2017_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2016_, v___y_2004_, v___y_2005_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_2018_, lean_object* v_declName_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2018_, v_declName_2019_, v___y_2020_, v___y_2021_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_2024_, lean_object* v_declName_2025_, lean_object* v_asyncPrefix_x3f_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v___y_2031_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2026_) == 0)
{
lean_object* v___x_2044_; 
v___x_2044_ = l_Lean_MessageData_nil;
v___y_2031_ = v___x_2044_;
goto v___jp_2030_;
}
else
{
lean_object* v_val_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v_val_2045_ = lean_ctor_get(v_asyncPrefix_x3f_2026_, 0);
lean_inc(v_val_2045_);
lean_dec_ref_known(v_asyncPrefix_x3f_2026_, 1);
v___x_2046_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_2047_ = l_Lean_MessageData_ofName(v_val_2045_);
v___x_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2046_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
v___x_2049_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_2050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2048_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
v___y_2031_ = v___x_2050_;
goto v___jp_2030_;
}
v___jp_2030_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2032_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_2033_ = l_Lean_MessageData_ofName(v_attrName_2024_);
v___x_2034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2032_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
v___x_2035_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_2036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2034_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
v___x_2037_ = 0;
v___x_2038_ = l_Lean_MessageData_ofConstName(v_declName_2025_, v___x_2037_);
v___x_2039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2036_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
v___x_2040_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_2041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2039_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
v___x_2042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
lean_ctor_set(v___x_2042_, 1, v___y_2031_);
v___x_2043_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2042_, v___y_2027_, v___y_2028_);
return v___x_2043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_2051_, lean_object* v_declName_2052_, lean_object* v_asyncPrefix_x3f_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2051_, v_declName_2052_, v_asyncPrefix_x3f_2053_, v___y_2054_, v___y_2055_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_2058_, uint8_t v_kind_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___y_2069_; 
v___x_2063_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_2064_ = l_Lean_MessageData_ofName(v_name_2058_);
v___x_2065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2065_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
switch(v_kind_2059_)
{
case 0:
{
lean_object* v___x_2076_; 
v___x_2076_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_2069_ = v___x_2076_;
goto v___jp_2068_;
}
case 1:
{
lean_object* v___x_2077_; 
v___x_2077_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_2069_ = v___x_2077_;
goto v___jp_2068_;
}
default: 
{
lean_object* v___x_2078_; 
v___x_2078_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_2069_ = v___x_2078_;
goto v___jp_2068_;
}
}
v___jp_2068_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
lean_inc_ref(v___y_2069_);
v___x_2070_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___y_2069_);
v___x_2071_ = l_Lean_MessageData_ofFormat(v___x_2070_);
v___x_2072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2067_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_2074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2072_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v___x_2075_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2074_, v___y_2060_, v___y_2061_);
return v___x_2075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_2079_, lean_object* v_kind_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
uint8_t v_kind_boxed_2084_; lean_object* v_res_2085_; 
v_kind_boxed_2084_ = lean_unbox(v_kind_2080_);
v_res_2085_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2079_, v_kind_boxed_2084_, v___y_2081_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_validate_2086_, lean_object* v_a_2087_, lean_object* v_name_2088_, lean_object* v_decl_2089_, lean_object* v_stx_2090_, uint8_t v_kind_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___x_2146_; 
v___x_2146_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2090_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2146_) == 0)
{
uint8_t v___x_2147_; uint8_t v___x_2148_; 
lean_dec_ref_known(v___x_2146_, 1);
v___x_2147_ = 0;
v___x_2148_ = l_Lean_instBEqAttributeKind_beq(v_kind_2091_, v___x_2147_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; 
lean_dec(v_decl_2089_);
lean_dec_ref(v_a_2087_);
lean_dec_ref(v_validate_2086_);
v___x_2149_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2088_, v_kind_2091_, v___y_2092_, v___y_2093_);
return v___x_2149_;
}
else
{
v___y_2140_ = v___y_2092_;
v___y_2141_ = v___y_2093_;
goto v___jp_2139_;
}
}
else
{
lean_dec(v_decl_2089_);
lean_dec(v_name_2088_);
lean_dec_ref(v_a_2087_);
lean_dec_ref(v_validate_2086_);
return v___x_2146_;
}
v___jp_2095_:
{
lean_object* v___x_2098_; 
lean_inc(v___y_2097_);
lean_inc_ref(v___y_2096_);
lean_inc(v_decl_2089_);
v___x_2098_ = lean_apply_4(v_validate_2086_, v_decl_2089_, v___y_2096_, v___y_2097_, lean_box(0));
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2128_; 
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2128_ == 0)
{
lean_object* v_unused_2129_; 
v_unused_2129_ = lean_ctor_get(v___x_2098_, 0);
lean_dec(v_unused_2129_);
v___x_2100_ = v___x_2098_;
v_isShared_2101_ = v_isSharedCheck_2128_;
goto v_resetjp_2099_;
}
else
{
lean_dec(v___x_2098_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2128_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2102_; lean_object* v_toEnvExtension_2103_; lean_object* v_env_2104_; lean_object* v_nextMacroScope_2105_; lean_object* v_ngen_2106_; lean_object* v_auxDeclNGen_2107_; lean_object* v_traceState_2108_; lean_object* v_messages_2109_; lean_object* v_infoState_2110_; lean_object* v_snapshotTasks_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2126_; 
v___x_2102_ = lean_st_ref_take(v___y_2097_);
v_toEnvExtension_2103_ = lean_ctor_get(v_a_2087_, 0);
v_env_2104_ = lean_ctor_get(v___x_2102_, 0);
v_nextMacroScope_2105_ = lean_ctor_get(v___x_2102_, 1);
v_ngen_2106_ = lean_ctor_get(v___x_2102_, 2);
v_auxDeclNGen_2107_ = lean_ctor_get(v___x_2102_, 3);
v_traceState_2108_ = lean_ctor_get(v___x_2102_, 4);
v_messages_2109_ = lean_ctor_get(v___x_2102_, 6);
v_infoState_2110_ = lean_ctor_get(v___x_2102_, 7);
v_snapshotTasks_2111_ = lean_ctor_get(v___x_2102_, 8);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2126_ == 0)
{
lean_object* v_unused_2127_; 
v_unused_2127_ = lean_ctor_get(v___x_2102_, 5);
lean_dec(v_unused_2127_);
v___x_2113_ = v___x_2102_;
v_isShared_2114_ = v_isSharedCheck_2126_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_snapshotTasks_2111_);
lean_inc(v_infoState_2110_);
lean_inc(v_messages_2109_);
lean_inc(v_traceState_2108_);
lean_inc(v_auxDeclNGen_2107_);
lean_inc(v_ngen_2106_);
lean_inc(v_nextMacroScope_2105_);
lean_inc(v_env_2104_);
lean_dec(v___x_2102_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2126_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v_asyncMode_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2119_; 
v_asyncMode_2115_ = lean_ctor_get(v_toEnvExtension_2103_, 2);
lean_inc(v_asyncMode_2115_);
lean_inc(v_decl_2089_);
v___x_2116_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_2087_, v_env_2104_, v_decl_2089_, v_asyncMode_2115_, v_decl_2089_);
lean_dec(v_asyncMode_2115_);
v___x_2117_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 5, v___x_2117_);
lean_ctor_set(v___x_2113_, 0, v___x_2116_);
v___x_2119_ = v___x_2113_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2116_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_nextMacroScope_2105_);
lean_ctor_set(v_reuseFailAlloc_2125_, 2, v_ngen_2106_);
lean_ctor_set(v_reuseFailAlloc_2125_, 3, v_auxDeclNGen_2107_);
lean_ctor_set(v_reuseFailAlloc_2125_, 4, v_traceState_2108_);
lean_ctor_set(v_reuseFailAlloc_2125_, 5, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2125_, 6, v_messages_2109_);
lean_ctor_set(v_reuseFailAlloc_2125_, 7, v_infoState_2110_);
lean_ctor_set(v_reuseFailAlloc_2125_, 8, v_snapshotTasks_2111_);
v___x_2119_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2123_; 
v___x_2120_ = lean_st_ref_put(v___y_2097_, v___x_2119_);
v___x_2121_ = lean_box(0);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v___x_2121_);
v___x_2123_ = v___x_2100_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2121_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
}
else
{
lean_dec(v_decl_2089_);
lean_dec_ref(v_a_2087_);
return v___x_2098_;
}
}
v___jp_2130_:
{
lean_object* v_toEnvExtension_2134_; lean_object* v_asyncMode_2135_; uint8_t v___x_2136_; 
v_toEnvExtension_2134_ = lean_ctor_get(v_a_2087_, 0);
v_asyncMode_2135_ = lean_ctor_get(v_toEnvExtension_2134_, 2);
lean_inc(v_decl_2089_);
lean_inc_ref(v___y_2131_);
v___x_2136_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2131_, v_decl_2089_, v_asyncMode_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
lean_dec_ref(v_a_2087_);
lean_dec_ref(v_validate_2086_);
v___x_2137_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2131_);
v___x_2138_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_2088_, v_decl_2089_, v___x_2137_, v___y_2132_, v___y_2133_);
return v___x_2138_;
}
else
{
lean_dec_ref(v___y_2131_);
lean_dec(v_name_2088_);
v___y_2096_ = v___y_2132_;
v___y_2097_ = v___y_2133_;
goto v___jp_2095_;
}
}
v___jp_2139_:
{
lean_object* v___x_2142_; lean_object* v_env_2143_; lean_object* v___x_2144_; 
v___x_2142_ = lean_st_ref_get(v___y_2141_);
v_env_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc_ref(v_env_2143_);
lean_dec(v___x_2142_);
v___x_2144_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2143_, v_decl_2089_);
if (lean_obj_tag(v___x_2144_) == 0)
{
v___y_2131_ = v_env_2143_;
v___y_2132_ = v___y_2140_;
v___y_2133_ = v___y_2141_;
goto v___jp_2130_;
}
else
{
lean_object* v___x_2145_; 
lean_dec_ref_known(v___x_2144_, 1);
lean_dec_ref(v_env_2143_);
lean_dec_ref(v_a_2087_);
lean_dec_ref(v_validate_2086_);
v___x_2145_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2088_, v_decl_2089_, v___y_2140_, v___y_2141_);
return v___x_2145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object* v_validate_2150_, lean_object* v_a_2151_, lean_object* v_name_2152_, lean_object* v_decl_2153_, lean_object* v_stx_2154_, lean_object* v_kind_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
uint8_t v_kind_boxed_2159_; lean_object* v_res_2160_; 
v_kind_boxed_2159_ = lean_unbox(v_kind_2155_);
v_res_2160_ = l_Lean_registerTagAttribute___lam__7(v_validate_2150_, v_a_2151_, v_name_2152_, v_decl_2153_, v_stx_2154_, v_kind_boxed_2159_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
return v_res_2160_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___f_2167_; 
v___x_2166_ = l_Lean_NameSet_empty;
v___f_2167_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 4, 1);
lean_closure_set(v___f_2167_, 0, v___x_2166_);
return v___f_2167_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2168_; lean_object* v___f_2169_; 
v___x_2168_ = l_Lean_NameSet_empty;
v___f_2169_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2169_, 0, v___x_2168_);
return v___f_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2172_, lean_object* v_descr_2173_, lean_object* v_validate_2174_, lean_object* v_ref_2175_, uint8_t v_applicationTime_2176_, lean_object* v_asyncMode_2177_){
_start:
{
lean_object* v___f_2179_; lean_object* v___f_2180_; lean_object* v___f_2181_; lean_object* v___f_2182_; lean_object* v___f_2183_; lean_object* v___f_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___f_2179_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2180_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2181_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2182_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
v___f_2183_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2184_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2185_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
lean_inc(v_ref_2175_);
v___x_2186_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2186_, 0, v_ref_2175_);
lean_ctor_set(v___x_2186_, 1, v___f_2184_);
lean_ctor_set(v___x_2186_, 2, v___f_2183_);
lean_ctor_set(v___x_2186_, 3, v___f_2182_);
lean_ctor_set(v___x_2186_, 4, v___f_2181_);
lean_ctor_set(v___x_2186_, 5, v___f_2180_);
lean_ctor_set(v___x_2186_, 6, v_asyncMode_2177_);
lean_ctor_set(v___x_2186_, 7, v___x_2185_);
v___x_2187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
lean_ctor_set(v___x_2187_, 1, v___f_2179_);
v___x_2188_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2187_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___f_2190_; lean_object* v___f_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc_n(v_a_2189_, 2);
lean_dec_ref_known(v___x_2188_, 1);
lean_inc_n(v_name_2172_, 2);
v___f_2190_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2190_, 0, v_name_2172_);
v___f_2191_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_2191_, 0, v_validate_2174_);
lean_closure_set(v___f_2191_, 1, v_a_2189_);
lean_closure_set(v___f_2191_, 2, v_name_2172_);
v___x_2192_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2192_, 0, v_ref_2175_);
lean_ctor_set(v___x_2192_, 1, v_name_2172_);
lean_ctor_set(v___x_2192_, 2, v_descr_2173_);
lean_ctor_set_uint8(v___x_2192_, sizeof(void*)*3, v_applicationTime_2176_);
v___x_2193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
lean_ctor_set(v___x_2193_, 1, v___f_2191_);
lean_ctor_set(v___x_2193_, 2, v___f_2190_);
lean_inc_ref(v___x_2193_);
v___x_2194_ = l_Lean_registerBuiltinAttribute(v___x_2193_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2202_; 
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2202_ == 0)
{
lean_object* v_unused_2203_; 
v_unused_2203_ = lean_ctor_get(v___x_2194_, 0);
lean_dec(v_unused_2203_);
v___x_2196_ = v___x_2194_;
v_isShared_2197_ = v_isSharedCheck_2202_;
goto v_resetjp_2195_;
}
else
{
lean_dec(v___x_2194_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2202_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2193_);
lean_ctor_set(v___x_2198_, 1, v_a_2189_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 0, v___x_2198_);
v___x_2200_ = v___x_2196_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec_ref_known(v___x_2193_, 3);
lean_dec(v_a_2189_);
v_a_2204_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2194_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2194_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec(v_ref_2175_);
lean_dec_ref(v_validate_2174_);
lean_dec_ref(v_descr_2173_);
lean_dec(v_name_2172_);
v_a_2212_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2188_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2188_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2220_, lean_object* v_descr_2221_, lean_object* v_validate_2222_, lean_object* v_ref_2223_, lean_object* v_applicationTime_2224_, lean_object* v_asyncMode_2225_, lean_object* v_a_2226_){
_start:
{
uint8_t v_applicationTime_boxed_2227_; lean_object* v_res_2228_; 
v_applicationTime_boxed_2227_ = lean_unbox(v_applicationTime_2224_);
v_res_2228_ = l_Lean_registerTagAttribute(v_name_2220_, v_descr_2221_, v_validate_2222_, v_ref_2223_, v_applicationTime_boxed_2227_, v_asyncMode_2225_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2229_, lean_object* v_t_2230_){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2229_, v_t_2230_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2232_, lean_object* v_as_2233_, lean_object* v_lo_2234_, lean_object* v_hi_2235_, lean_object* v_w_2236_, lean_object* v_hlo_2237_, lean_object* v_hhi_2238_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2232_, v_as_2233_, v_lo_2234_, v_hi_2235_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2240_, lean_object* v_as_2241_, lean_object* v_lo_2242_, lean_object* v_hi_2243_, lean_object* v_w_2244_, lean_object* v_hlo_2245_, lean_object* v_hhi_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2240_, v_as_2241_, v_lo_2242_, v_hi_2243_, v_w_2244_, v_hlo_2245_, v_hhi_2246_);
lean_dec(v_hi_2243_);
lean_dec(v_n_2240_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2248_, lean_object* v_attrName_2249_, lean_object* v_declName_2250_, lean_object* v_asyncPrefix_x3f_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2249_, v_declName_2250_, v_asyncPrefix_x3f_2251_, v___y_2252_, v___y_2253_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2256_, lean_object* v_attrName_2257_, lean_object* v_declName_2258_, lean_object* v_asyncPrefix_x3f_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2256_, v_attrName_2257_, v_declName_2258_, v_asyncPrefix_x3f_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2264_, lean_object* v_attrName_2265_, lean_object* v_declName_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2265_, v_declName_2266_, v___y_2267_, v___y_2268_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2271_, lean_object* v_attrName_2272_, lean_object* v_declName_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2271_, v_attrName_2272_, v_declName_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2278_, lean_object* v_name_2279_, uint8_t v_kind_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2279_, v_kind_2280_, v___y_2281_, v___y_2282_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2285_, lean_object* v_name_2286_, lean_object* v_kind_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
uint8_t v_kind_boxed_2291_; lean_object* v_res_2292_; 
v_kind_boxed_2291_ = lean_unbox(v_kind_2287_);
v_res_2292_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2285_, v_name_2286_, v_kind_boxed_2291_, v___y_2288_, v___y_2289_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2293_, lean_object* v_lo_2294_, lean_object* v_hi_2295_, lean_object* v_hhi_2296_, lean_object* v_pivot_2297_, lean_object* v_as_2298_, lean_object* v_i_2299_, lean_object* v_k_2300_, lean_object* v_ilo_2301_, lean_object* v_ik_2302_, lean_object* v_w_2303_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2295_, v_pivot_2297_, v_as_2298_, v_i_2299_, v_k_2300_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2305_, lean_object* v_lo_2306_, lean_object* v_hi_2307_, lean_object* v_hhi_2308_, lean_object* v_pivot_2309_, lean_object* v_as_2310_, lean_object* v_i_2311_, lean_object* v_k_2312_, lean_object* v_ilo_2313_, lean_object* v_ik_2314_, lean_object* v_w_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2305_, v_lo_2306_, v_hi_2307_, v_hhi_2308_, v_pivot_2309_, v_as_2310_, v_i_2311_, v_k_2312_, v_ilo_2313_, v_ik_2314_, v_w_2315_);
lean_dec(v_pivot_2309_);
lean_dec(v_hi_2307_);
lean_dec(v_lo_2306_);
lean_dec(v_n_2305_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_attr_2317_, lean_object* v_decl_2318_, lean_object* v_env_2319_){
_start:
{
lean_object* v_ext_2320_; lean_object* v_toEnvExtension_2321_; lean_object* v_asyncMode_2322_; lean_object* v___x_2323_; 
v_ext_2320_ = lean_ctor_get(v_attr_2317_, 1);
lean_inc_ref(v_ext_2320_);
lean_dec_ref(v_attr_2317_);
v_toEnvExtension_2321_ = lean_ctor_get(v_ext_2320_, 0);
v_asyncMode_2322_ = lean_ctor_get(v_toEnvExtension_2321_, 2);
lean_inc(v_asyncMode_2322_);
lean_inc(v_decl_2318_);
v___x_2323_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2320_, v_env_2319_, v_decl_2318_, v_asyncMode_2322_, v_decl_2318_);
lean_dec(v_asyncMode_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_modifyEnv_2324_, lean_object* v___f_2325_, lean_object* v_____r_2326_){
_start:
{
lean_object* v___x_2327_; 
v___x_2327_ = lean_apply_1(v_modifyEnv_2324_, v___f_2325_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_attr_2328_, lean_object* v_env_2329_, lean_object* v_decl_2330_, lean_object* v_inst_2331_, lean_object* v_inst_2332_, lean_object* v_toBind_2333_, lean_object* v___f_2334_, lean_object* v_modifyEnv_2335_, lean_object* v___f_2336_, lean_object* v_____r_2337_){
_start:
{
lean_object* v_ext_2338_; lean_object* v_toEnvExtension_2339_; lean_object* v_attr_2340_; lean_object* v_asyncMode_2341_; uint8_t v___x_2342_; 
v_ext_2338_ = lean_ctor_get(v_attr_2328_, 1);
v_toEnvExtension_2339_ = lean_ctor_get(v_ext_2338_, 0);
lean_inc_ref(v_toEnvExtension_2339_);
v_attr_2340_ = lean_ctor_get(v_attr_2328_, 0);
lean_inc_ref(v_attr_2340_);
lean_dec_ref(v_attr_2328_);
v_asyncMode_2341_ = lean_ctor_get(v_toEnvExtension_2339_, 2);
lean_inc(v_asyncMode_2341_);
lean_dec_ref(v_toEnvExtension_2339_);
lean_inc(v_decl_2330_);
lean_inc_ref(v_env_2329_);
v___x_2342_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2329_, v_decl_2330_, v_asyncMode_2341_);
lean_dec(v_asyncMode_2341_);
if (v___x_2342_ == 0)
{
lean_object* v_toAttributeImplCore_2343_; lean_object* v_name_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
lean_dec_ref(v___f_2336_);
lean_dec(v_modifyEnv_2335_);
v_toAttributeImplCore_2343_ = lean_ctor_get(v_attr_2340_, 0);
lean_inc_ref(v_toAttributeImplCore_2343_);
lean_dec_ref(v_attr_2340_);
v_name_2344_ = lean_ctor_get(v_toAttributeImplCore_2343_, 1);
lean_inc(v_name_2344_);
lean_dec_ref(v_toAttributeImplCore_2343_);
v___x_2345_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2329_);
v___x_2346_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2331_, v_inst_2332_, v_name_2344_, v_decl_2330_, v___x_2345_);
v___x_2347_ = lean_apply_4(v_toBind_2333_, lean_box(0), lean_box(0), v___x_2346_, v___f_2334_);
return v___x_2347_;
}
else
{
lean_object* v___x_2348_; 
lean_dec_ref(v_attr_2340_);
lean_dec(v___f_2334_);
lean_dec(v_toBind_2333_);
lean_dec_ref(v_inst_2332_);
lean_dec_ref(v_inst_2331_);
lean_dec(v_decl_2330_);
lean_dec_ref(v_env_2329_);
v___x_2348_ = lean_apply_1(v_modifyEnv_2335_, v___f_2336_);
return v___x_2348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v___f_2349_, lean_object* v_____r_2350_){
_start:
{
lean_object* v___x_2351_; 
v___x_2351_ = lean_apply_1(v___f_2349_, v_____r_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v_attr_2352_, lean_object* v_decl_2353_, lean_object* v_inst_2354_, lean_object* v_inst_2355_, lean_object* v_toBind_2356_, lean_object* v___f_2357_, lean_object* v_modifyEnv_2358_, lean_object* v___f_2359_, lean_object* v_env_2360_){
_start:
{
lean_object* v___f_2361_; lean_object* v___x_2362_; 
lean_inc_ref(v___f_2359_);
lean_inc(v_modifyEnv_2358_);
lean_inc(v___f_2357_);
lean_inc(v_toBind_2356_);
lean_inc_ref(v_inst_2355_);
lean_inc_ref(v_inst_2354_);
lean_inc(v_decl_2353_);
lean_inc_ref(v_env_2360_);
lean_inc_ref(v_attr_2352_);
v___f_2361_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 10, 9);
lean_closure_set(v___f_2361_, 0, v_attr_2352_);
lean_closure_set(v___f_2361_, 1, v_env_2360_);
lean_closure_set(v___f_2361_, 2, v_decl_2353_);
lean_closure_set(v___f_2361_, 3, v_inst_2354_);
lean_closure_set(v___f_2361_, 4, v_inst_2355_);
lean_closure_set(v___f_2361_, 5, v_toBind_2356_);
lean_closure_set(v___f_2361_, 6, v___f_2357_);
lean_closure_set(v___f_2361_, 7, v_modifyEnv_2358_);
lean_closure_set(v___f_2361_, 8, v___f_2359_);
v___x_2362_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2360_, v_decl_2353_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
lean_dec_ref(v___f_2361_);
v___x_2363_ = lean_box(0);
v___x_2364_ = l_Lean_TagAttribute_setTag___redArg___lam__2(v_attr_2352_, v_env_2360_, v_decl_2353_, v_inst_2354_, v_inst_2355_, v_toBind_2356_, v___f_2357_, v_modifyEnv_2358_, v___f_2359_, v___x_2363_);
return v___x_2364_;
}
else
{
lean_object* v_attr_2365_; lean_object* v_toAttributeImplCore_2366_; lean_object* v_name_2367_; lean_object* v___f_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
lean_dec_ref_known(v___x_2362_, 1);
lean_dec_ref(v_env_2360_);
lean_dec_ref(v___f_2359_);
lean_dec(v_modifyEnv_2358_);
lean_dec(v___f_2357_);
v_attr_2365_ = lean_ctor_get(v_attr_2352_, 0);
lean_inc_ref(v_attr_2365_);
lean_dec_ref(v_attr_2352_);
v_toAttributeImplCore_2366_ = lean_ctor_get(v_attr_2365_, 0);
lean_inc_ref(v_toAttributeImplCore_2366_);
lean_dec_ref(v_attr_2365_);
v_name_2367_ = lean_ctor_get(v_toAttributeImplCore_2366_, 1);
lean_inc(v_name_2367_);
lean_dec_ref(v_toAttributeImplCore_2366_);
v___f_2368_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2368_, 0, v___f_2361_);
v___x_2369_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2354_, v_inst_2355_, v_name_2367_, v_decl_2353_);
v___x_2370_ = lean_apply_4(v_toBind_2356_, lean_box(0), lean_box(0), v___x_2369_, v___f_2368_);
return v___x_2370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2371_, lean_object* v_inst_2372_, lean_object* v_inst_2373_, lean_object* v_attr_2374_, lean_object* v_decl_2375_){
_start:
{
lean_object* v_toBind_2376_; lean_object* v_getEnv_2377_; lean_object* v_modifyEnv_2378_; lean_object* v___f_2379_; lean_object* v___f_2380_; lean_object* v___f_2381_; lean_object* v___x_2382_; 
v_toBind_2376_ = lean_ctor_get(v_inst_2371_, 1);
lean_inc_n(v_toBind_2376_, 2);
v_getEnv_2377_ = lean_ctor_get(v_inst_2373_, 0);
lean_inc(v_getEnv_2377_);
v_modifyEnv_2378_ = lean_ctor_get(v_inst_2373_, 1);
lean_inc_n(v_modifyEnv_2378_, 2);
lean_dec_ref(v_inst_2373_);
lean_inc(v_decl_2375_);
lean_inc_ref(v_attr_2374_);
v___f_2379_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2379_, 0, v_attr_2374_);
lean_closure_set(v___f_2379_, 1, v_decl_2375_);
lean_inc_ref(v___f_2379_);
v___f_2380_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2380_, 0, v_modifyEnv_2378_);
lean_closure_set(v___f_2380_, 1, v___f_2379_);
v___f_2381_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2381_, 0, v_attr_2374_);
lean_closure_set(v___f_2381_, 1, v_decl_2375_);
lean_closure_set(v___f_2381_, 2, v_inst_2371_);
lean_closure_set(v___f_2381_, 3, v_inst_2372_);
lean_closure_set(v___f_2381_, 4, v_toBind_2376_);
lean_closure_set(v___f_2381_, 5, v___f_2380_);
lean_closure_set(v___f_2381_, 6, v_modifyEnv_2378_);
lean_closure_set(v___f_2381_, 7, v___f_2379_);
v___x_2382_ = lean_apply_4(v_toBind_2376_, lean_box(0), lean_box(0), v_getEnv_2377_, v___f_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2383_, lean_object* v_inst_2384_, lean_object* v_inst_2385_, lean_object* v_inst_2386_, lean_object* v_attr_2387_, lean_object* v_decl_2388_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2384_, v_inst_2385_, v_inst_2386_, v_attr_2387_, v_decl_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v_as_2390_, lean_object* v_k_2391_, lean_object* v_x_2392_, lean_object* v_x_2393_){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v_m_2396_; lean_object* v_a_2397_; uint8_t v___x_2398_; 
v___x_2394_ = lean_nat_add(v_x_2392_, v_x_2393_);
v___x_2395_ = lean_unsigned_to_nat(1u);
v_m_2396_ = lean_nat_shiftr(v___x_2394_, v___x_2395_);
lean_dec(v___x_2394_);
v_a_2397_ = lean_array_fget_borrowed(v_as_2390_, v_m_2396_);
v___x_2398_ = l_Lean_Name_quickLt(v_a_2397_, v_k_2391_);
if (v___x_2398_ == 0)
{
uint8_t v___x_2399_; 
lean_dec(v_x_2393_);
v___x_2399_ = l_Lean_Name_quickLt(v_k_2391_, v_a_2397_);
if (v___x_2399_ == 0)
{
uint8_t v___x_2400_; 
lean_dec(v_m_2396_);
lean_dec(v_x_2392_);
v___x_2400_ = 1;
return v___x_2400_;
}
else
{
lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2401_ = lean_unsigned_to_nat(0u);
v___x_2402_ = lean_nat_dec_eq(v_m_2396_, v___x_2401_);
if (v___x_2402_ == 0)
{
lean_object* v___x_2403_; uint8_t v___x_2404_; 
v___x_2403_ = lean_nat_sub(v_m_2396_, v___x_2395_);
lean_dec(v_m_2396_);
v___x_2404_ = lean_nat_dec_lt(v___x_2403_, v_x_2392_);
if (v___x_2404_ == 0)
{
v_x_2393_ = v___x_2403_;
goto _start;
}
else
{
lean_dec(v___x_2403_);
lean_dec(v_x_2392_);
return v___x_2398_;
}
}
else
{
lean_dec(v_m_2396_);
lean_dec(v_x_2392_);
return v___x_2398_;
}
}
}
else
{
lean_object* v___x_2406_; uint8_t v___x_2407_; 
lean_dec(v_x_2392_);
v___x_2406_ = lean_nat_add(v_m_2396_, v___x_2395_);
lean_dec(v_m_2396_);
v___x_2407_ = lean_nat_dec_le(v___x_2406_, v_x_2393_);
if (v___x_2407_ == 0)
{
lean_dec(v___x_2406_);
lean_dec(v_x_2393_);
return v___x_2407_;
}
else
{
v_x_2392_ = v___x_2406_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v_as_2409_, lean_object* v_k_2410_, lean_object* v_x_2411_, lean_object* v_x_2412_){
_start:
{
uint8_t v_res_2413_; lean_object* v_r_2414_; 
v_res_2413_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2409_, v_k_2410_, v_x_2411_, v_x_2412_);
lean_dec(v_k_2410_);
lean_dec_ref(v_as_2409_);
v_r_2414_ = lean_box(v_res_2413_);
return v_r_2414_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2415_, lean_object* v_env_2416_, lean_object* v_decl_2417_){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = lean_box(1);
v___x_2419_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2416_, v_decl_2417_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_ext_2420_; lean_object* v_toEnvExtension_2421_; lean_object* v_asyncMode_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v_ext_2420_ = lean_ctor_get(v_attr_2415_, 1);
v_toEnvExtension_2421_ = lean_ctor_get(v_ext_2420_, 0);
v_asyncMode_2422_ = lean_ctor_get(v_toEnvExtension_2421_, 2);
lean_inc(v_decl_2417_);
v___x_2423_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2418_, v_ext_2420_, v_env_2416_, v_asyncMode_2422_, v_decl_2417_);
v___x_2424_ = l_Lean_NameSet_contains(v___x_2423_, v_decl_2417_);
lean_dec(v_decl_2417_);
lean_dec(v___x_2423_);
return v___x_2424_;
}
else
{
lean_object* v_val_2425_; lean_object* v_ext_2426_; uint8_t v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; uint8_t v___x_2431_; 
v_val_2425_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_val_2425_);
lean_dec_ref_known(v___x_2419_, 1);
v_ext_2426_ = lean_ctor_get(v_attr_2415_, 1);
v___x_2427_ = 0;
v___x_2428_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2418_, v_ext_2426_, v_env_2416_, v_val_2425_, v___x_2427_);
lean_dec(v_val_2425_);
lean_dec_ref(v_env_2416_);
v___x_2429_ = lean_unsigned_to_nat(0u);
v___x_2430_ = lean_array_get_size(v___x_2428_);
v___x_2431_ = lean_nat_dec_lt(v___x_2429_, v___x_2430_);
if (v___x_2431_ == 0)
{
lean_dec_ref(v___x_2428_);
lean_dec(v_decl_2417_);
return v___x_2431_;
}
else
{
lean_object* v___x_2432_; lean_object* v___x_2433_; uint8_t v___x_2434_; 
v___x_2432_ = lean_unsigned_to_nat(1u);
v___x_2433_ = lean_nat_sub(v___x_2430_, v___x_2432_);
v___x_2434_ = lean_nat_dec_le(v___x_2429_, v___x_2433_);
if (v___x_2434_ == 0)
{
lean_dec(v___x_2433_);
lean_dec_ref(v___x_2428_);
lean_dec(v_decl_2417_);
return v___x_2434_;
}
else
{
uint8_t v___x_2435_; 
v___x_2435_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2428_, v_decl_2417_, v___x_2429_, v___x_2433_);
lean_dec(v_decl_2417_);
lean_dec_ref(v___x_2428_);
return v___x_2435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2436_, lean_object* v_env_2437_, lean_object* v_decl_2438_){
_start:
{
uint8_t v_res_2439_; lean_object* v_r_2440_; 
v_res_2439_ = l_Lean_TagAttribute_hasTag(v_attr_2436_, v_env_2437_, v_decl_2438_);
lean_dec_ref(v_attr_2436_);
v_r_2440_ = lean_box(v_res_2439_);
return v_r_2440_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v_as_2441_, lean_object* v_k_2442_, lean_object* v_x_2443_, lean_object* v_x_2444_, lean_object* v_x_2445_){
_start:
{
uint8_t v___x_2446_; 
v___x_2446_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2441_, v_k_2442_, v_x_2443_, v_x_2444_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v_as_2447_, lean_object* v_k_2448_, lean_object* v_x_2449_, lean_object* v_x_2450_, lean_object* v_x_2451_){
_start:
{
uint8_t v_res_2452_; lean_object* v_r_2453_; 
v_res_2452_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v_as_2447_, v_k_2448_, v_x_2449_, v_x_2450_, v_x_2451_);
lean_dec(v_k_2448_);
lean_dec_ref(v_as_2447_);
v_r_2453_ = lean_box(v_res_2452_);
return v_r_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object* v_x_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object* v_x_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_instInhabitedParametricAttribute_default___lam__0(v_x_2459_, v___y_2460_);
lean_dec_ref(v___y_2460_);
lean_dec_ref(v_x_2459_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object* v_s_2463_, lean_object* v_x_2464_){
_start:
{
lean_inc_ref(v_s_2463_);
return v_s_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object* v_s_2465_, lean_object* v_x_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_instInhabitedParametricAttribute_default___lam__1(v_s_2465_, v_x_2466_);
lean_dec_ref(v_x_2466_);
lean_dec_ref(v_s_2465_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object* v_x_2472_, lean_object* v_x_2473_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object* v_x_2475_, lean_object* v_x_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_instInhabitedParametricAttribute_default___lam__2(v_x_2475_, v_x_2476_);
lean_dec_ref(v_x_2476_);
lean_dec_ref(v_x_2475_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object* v_x_2478_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = lean_box(0);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object* v_x_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Lean_instInhabitedParametricAttribute_default___lam__3(v_x_2480_);
lean_dec_ref(v_x_2480_);
return v_res_2481_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_2486_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_2487_; lean_object* v___f_2488_; lean_object* v___f_2489_; lean_object* v___f_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___f_2487_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__3));
v___f_2488_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__2));
v___f_2489_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__1));
v___f_2490_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__0));
v___x_2491_ = lean_box(0);
v___x_2492_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__4, &l_Lean_instInhabitedParametricAttribute_default___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__4);
v___x_2493_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
lean_ctor_set(v___x_2493_, 1, v___x_2491_);
lean_ctor_set(v___x_2493_, 2, v___f_2490_);
lean_ctor_set(v___x_2493_, 3, v___f_2489_);
lean_ctor_set(v___x_2493_, 4, v___f_2488_);
lean_ctor_set(v___x_2493_, 5, v___f_2487_);
return v___x_2493_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__6(void){
_start:
{
uint8_t v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2494_ = 0;
v___x_2495_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__5, &l_Lean_instInhabitedParametricAttribute_default___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__5);
v___x_2496_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2497_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
lean_ctor_set(v___x_2497_, 1, v___x_2495_);
lean_ctor_set_uint8(v___x_2497_, sizeof(void*)*2, v___x_2494_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2498_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__6, &l_Lean_instInhabitedParametricAttribute_default___closed__6_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__6);
return v___x_2499_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute___closed__0(void){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Lean_instInhabitedParametricAttribute_default(lean_box(0));
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2501_){
_start:
{
lean_object* v___x_2502_; 
v___x_2502_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute___closed__0, &l_Lean_instInhabitedParametricAttribute___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute___closed__0);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object* v_x_2503_, lean_object* v_p_2504_){
_start:
{
lean_object* v_fst_2505_; lean_object* v_snd_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2523_; 
v_fst_2505_ = lean_ctor_get(v_x_2503_, 0);
v_snd_2506_ = lean_ctor_get(v_x_2503_, 1);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_x_2503_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2508_ = v_x_2503_;
v_isShared_2509_ = v_isSharedCheck_2523_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_snd_2506_);
lean_inc(v_fst_2505_);
lean_dec(v_x_2503_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2523_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v_fst_2510_; lean_object* v_snd_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2522_; 
v_fst_2510_ = lean_ctor_get(v_p_2504_, 0);
v_snd_2511_ = lean_ctor_get(v_p_2504_, 1);
v_isSharedCheck_2522_ = !lean_is_exclusive(v_p_2504_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2513_ = v_p_2504_;
v_isShared_2514_ = v_isSharedCheck_2522_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_snd_2511_);
lean_inc(v_fst_2510_);
lean_dec(v_p_2504_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2522_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
lean_inc(v_fst_2510_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set_tag(v___x_2508_, 1);
lean_ctor_set(v___x_2508_, 1, v_fst_2505_);
lean_ctor_set(v___x_2508_, 0, v_fst_2510_);
v___x_2516_ = v___x_2508_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_fst_2510_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_fst_2505_);
v___x_2516_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2517_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2510_, v_snd_2511_, v_snd_2506_);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 1, v___x_2517_);
lean_ctor_set(v___x_2513_, 0, v___x_2516_);
v___x_2519_ = v___x_2513_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object* v_init_2524_, lean_object* v_x_2525_){
_start:
{
if (lean_obj_tag(v_x_2525_) == 0)
{
lean_object* v_k_2526_; lean_object* v_v_2527_; lean_object* v_l_2528_; lean_object* v_r_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v_k_2526_ = lean_ctor_get(v_x_2525_, 1);
v_v_2527_ = lean_ctor_get(v_x_2525_, 2);
v_l_2528_ = lean_ctor_get(v_x_2525_, 3);
v_r_2529_ = lean_ctor_get(v_x_2525_, 4);
v___x_2530_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2524_, v_l_2528_);
lean_inc(v_v_2527_);
lean_inc(v_k_2526_);
v___x_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2531_, 0, v_k_2526_);
lean_ctor_set(v___x_2531_, 1, v_v_2527_);
v___x_2532_ = lean_array_push(v___x_2530_, v___x_2531_);
v_init_2524_ = v___x_2532_;
v_x_2525_ = v_r_2529_;
goto _start;
}
else
{
return v_init_2524_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object* v_init_2534_, lean_object* v_x_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2534_, v_x_2535_);
lean_dec(v_x_2535_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object* v_snd_2537_, lean_object* v_as_2538_, size_t v_i_2539_, size_t v_stop_2540_, lean_object* v_b_2541_){
_start:
{
lean_object* v___y_2543_; uint8_t v___x_2547_; 
v___x_2547_ = lean_usize_dec_eq(v_i_2539_, v_stop_2540_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = lean_array_uget_borrowed(v_as_2538_, v_i_2539_);
v___x_2549_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2537_, v___x_2548_);
if (lean_obj_tag(v___x_2549_) == 0)
{
v___y_2543_ = v_b_2541_;
goto v___jp_2542_;
}
else
{
lean_object* v_val_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v_val_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_val_2550_);
lean_dec_ref_known(v___x_2549_, 1);
lean_inc(v___x_2548_);
v___x_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2548_);
lean_ctor_set(v___x_2551_, 1, v_val_2550_);
v___x_2552_ = lean_array_push(v_b_2541_, v___x_2551_);
v___y_2543_ = v___x_2552_;
goto v___jp_2542_;
}
}
else
{
return v_b_2541_;
}
v___jp_2542_:
{
size_t v___x_2544_; size_t v___x_2545_; 
v___x_2544_ = ((size_t)1ULL);
v___x_2545_ = lean_usize_add(v_i_2539_, v___x_2544_);
v_i_2539_ = v___x_2545_;
v_b_2541_ = v___y_2543_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2553_, lean_object* v_as_2554_, lean_object* v_i_2555_, lean_object* v_stop_2556_, lean_object* v_b_2557_){
_start:
{
size_t v_i_boxed_2558_; size_t v_stop_boxed_2559_; lean_object* v_res_2560_; 
v_i_boxed_2558_ = lean_unbox_usize(v_i_2555_);
lean_dec(v_i_2555_);
v_stop_boxed_2559_ = lean_unbox_usize(v_stop_2556_);
lean_dec(v_stop_2556_);
v_res_2560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2553_, v_as_2554_, v_i_boxed_2558_, v_stop_boxed_2559_, v_b_2557_);
lean_dec_ref(v_as_2554_);
lean_dec(v_snd_2553_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object* v_snd_2561_, lean_object* v_as_2562_, lean_object* v_start_2563_, lean_object* v_stop_2564_){
_start:
{
lean_object* v___x_2565_; uint8_t v___x_2566_; 
v___x_2565_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2566_ = lean_nat_dec_lt(v_start_2563_, v_stop_2564_);
if (v___x_2566_ == 0)
{
return v___x_2565_;
}
else
{
lean_object* v___x_2567_; uint8_t v___x_2568_; 
v___x_2567_ = lean_array_get_size(v_as_2562_);
v___x_2568_ = lean_nat_dec_le(v_stop_2564_, v___x_2567_);
if (v___x_2568_ == 0)
{
uint8_t v___x_2569_; 
v___x_2569_ = lean_nat_dec_lt(v_start_2563_, v___x_2567_);
if (v___x_2569_ == 0)
{
return v___x_2565_;
}
else
{
size_t v___x_2570_; size_t v___x_2571_; lean_object* v___x_2572_; 
v___x_2570_ = lean_usize_of_nat(v_start_2563_);
v___x_2571_ = lean_usize_of_nat(v___x_2567_);
v___x_2572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2561_, v_as_2562_, v___x_2570_, v___x_2571_, v___x_2565_);
return v___x_2572_;
}
}
else
{
size_t v___x_2573_; size_t v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = lean_usize_of_nat(v_start_2563_);
v___x_2574_ = lean_usize_of_nat(v_stop_2564_);
v___x_2575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2561_, v_as_2562_, v___x_2573_, v___x_2574_, v___x_2565_);
return v___x_2575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object* v_snd_2576_, lean_object* v_as_2577_, lean_object* v_start_2578_, lean_object* v_stop_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2576_, v_as_2577_, v_start_2578_, v_stop_2579_);
lean_dec(v_stop_2579_);
lean_dec(v_start_2578_);
lean_dec_ref(v_as_2577_);
lean_dec(v_snd_2576_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object* v_hi_2581_, lean_object* v_pivot_2582_, lean_object* v_as_2583_, lean_object* v_i_2584_, lean_object* v_k_2585_){
_start:
{
uint8_t v___x_2586_; 
v___x_2586_ = lean_nat_dec_lt(v_k_2585_, v_hi_2581_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
lean_dec(v_k_2585_);
v___x_2587_ = lean_array_fswap(v_as_2583_, v_i_2584_, v_hi_2581_);
v___x_2588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2588_, 0, v_i_2584_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
return v___x_2588_;
}
else
{
lean_object* v___x_2589_; lean_object* v_fst_2590_; lean_object* v_fst_2591_; uint8_t v___x_2592_; 
v___x_2589_ = lean_array_fget_borrowed(v_as_2583_, v_k_2585_);
v_fst_2590_ = lean_ctor_get(v___x_2589_, 0);
v_fst_2591_ = lean_ctor_get(v_pivot_2582_, 0);
v___x_2592_ = l_Lean_Name_quickLt(v_fst_2590_, v_fst_2591_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_unsigned_to_nat(1u);
v___x_2594_ = lean_nat_add(v_k_2585_, v___x_2593_);
lean_dec(v_k_2585_);
v_k_2585_ = v___x_2594_;
goto _start;
}
else
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2596_ = lean_array_fswap(v_as_2583_, v_i_2584_, v_k_2585_);
v___x_2597_ = lean_unsigned_to_nat(1u);
v___x_2598_ = lean_nat_add(v_i_2584_, v___x_2597_);
lean_dec(v_i_2584_);
v___x_2599_ = lean_nat_add(v_k_2585_, v___x_2597_);
lean_dec(v_k_2585_);
v_as_2583_ = v___x_2596_;
v_i_2584_ = v___x_2598_;
v_k_2585_ = v___x_2599_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2601_, lean_object* v_pivot_2602_, lean_object* v_as_2603_, lean_object* v_i_2604_, lean_object* v_k_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2601_, v_pivot_2602_, v_as_2603_, v_i_2604_, v_k_2605_);
lean_dec_ref(v_pivot_2602_);
lean_dec(v_hi_2601_);
return v_res_2606_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object* v_a_2607_, lean_object* v_b_2608_){
_start:
{
lean_object* v_fst_2609_; lean_object* v_fst_2610_; uint8_t v___x_2611_; 
v_fst_2609_ = lean_ctor_get(v_a_2607_, 0);
v_fst_2610_ = lean_ctor_get(v_b_2608_, 0);
v___x_2611_ = l_Lean_Name_quickLt(v_fst_2609_, v_fst_2610_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object* v_a_2612_, lean_object* v_b_2613_){
_start:
{
uint8_t v_res_2614_; lean_object* v_r_2615_; 
v_res_2614_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2612_, v_b_2613_);
lean_dec_ref(v_b_2613_);
lean_dec_ref(v_a_2612_);
v_r_2615_ = lean_box(v_res_2614_);
return v_r_2615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object* v_n_2616_, lean_object* v_as_2617_, lean_object* v_lo_2618_, lean_object* v_hi_2619_){
_start:
{
lean_object* v___y_2621_; uint8_t v___x_2631_; 
v___x_2631_ = lean_nat_dec_lt(v_lo_2618_, v_hi_2619_);
if (v___x_2631_ == 0)
{
lean_dec(v_lo_2618_);
return v_as_2617_;
}
else
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v_mid_2634_; lean_object* v___y_2636_; lean_object* v___y_2642_; lean_object* v___x_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___x_2632_ = lean_nat_add(v_lo_2618_, v_hi_2619_);
v___x_2633_ = lean_unsigned_to_nat(1u);
v_mid_2634_ = lean_nat_shiftr(v___x_2632_, v___x_2633_);
lean_dec(v___x_2632_);
v___x_2647_ = lean_array_fget_borrowed(v_as_2617_, v_mid_2634_);
v___x_2648_ = lean_array_fget_borrowed(v_as_2617_, v_lo_2618_);
v___x_2649_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2647_, v___x_2648_);
if (v___x_2649_ == 0)
{
v___y_2642_ = v_as_2617_;
goto v___jp_2641_;
}
else
{
lean_object* v___x_2650_; 
v___x_2650_ = lean_array_fswap(v_as_2617_, v_lo_2618_, v_mid_2634_);
v___y_2642_ = v___x_2650_;
goto v___jp_2641_;
}
v___jp_2635_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; uint8_t v___x_2639_; 
v___x_2637_ = lean_array_fget_borrowed(v___y_2636_, v_mid_2634_);
v___x_2638_ = lean_array_fget_borrowed(v___y_2636_, v_hi_2619_);
v___x_2639_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2637_, v___x_2638_);
if (v___x_2639_ == 0)
{
lean_dec(v_mid_2634_);
v___y_2621_ = v___y_2636_;
goto v___jp_2620_;
}
else
{
lean_object* v___x_2640_; 
v___x_2640_ = lean_array_fswap(v___y_2636_, v_mid_2634_, v_hi_2619_);
lean_dec(v_mid_2634_);
v___y_2621_ = v___x_2640_;
goto v___jp_2620_;
}
}
v___jp_2641_:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2643_ = lean_array_fget_borrowed(v___y_2642_, v_hi_2619_);
v___x_2644_ = lean_array_fget_borrowed(v___y_2642_, v_lo_2618_);
v___x_2645_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2643_, v___x_2644_);
if (v___x_2645_ == 0)
{
v___y_2636_ = v___y_2642_;
goto v___jp_2635_;
}
else
{
lean_object* v___x_2646_; 
v___x_2646_ = lean_array_fswap(v___y_2642_, v_lo_2618_, v_hi_2619_);
v___y_2636_ = v___x_2646_;
goto v___jp_2635_;
}
}
}
v___jp_2620_:
{
lean_object* v_pivot_2622_; lean_object* v___x_2623_; lean_object* v_fst_2624_; lean_object* v_snd_2625_; uint8_t v___x_2626_; 
v_pivot_2622_ = lean_array_fget(v___y_2621_, v_hi_2619_);
lean_inc_n(v_lo_2618_, 2);
v___x_2623_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2619_, v_pivot_2622_, v___y_2621_, v_lo_2618_, v_lo_2618_);
lean_dec(v_pivot_2622_);
v_fst_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_fst_2624_);
v_snd_2625_ = lean_ctor_get(v___x_2623_, 1);
lean_inc(v_snd_2625_);
lean_dec_ref(v___x_2623_);
v___x_2626_ = lean_nat_dec_le(v_hi_2619_, v_fst_2624_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2627_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2616_, v_snd_2625_, v_lo_2618_, v_fst_2624_);
v___x_2628_ = lean_unsigned_to_nat(1u);
v___x_2629_ = lean_nat_add(v_fst_2624_, v___x_2628_);
lean_dec(v_fst_2624_);
v_as_2617_ = v___x_2627_;
v_lo_2618_ = v___x_2629_;
goto _start;
}
else
{
lean_dec(v_fst_2624_);
lean_dec(v_lo_2618_);
return v_snd_2625_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object* v_n_2651_, lean_object* v_as_2652_, lean_object* v_lo_2653_, lean_object* v_hi_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2651_, v_as_2652_, v_lo_2653_, v_hi_2654_);
lean_dec(v_hi_2654_);
lean_dec(v_n_2651_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object* v_filterExport_2656_, lean_object* v_env_2657_, lean_object* v_as_2658_, size_t v_i_2659_, size_t v_stop_2660_, lean_object* v_b_2661_){
_start:
{
lean_object* v___y_2663_; uint8_t v___x_2667_; 
v___x_2667_ = lean_usize_dec_eq(v_i_2659_, v_stop_2660_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v_fst_2669_; lean_object* v_snd_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; 
v___x_2668_ = lean_array_uget_borrowed(v_as_2658_, v_i_2659_);
v_fst_2669_ = lean_ctor_get(v___x_2668_, 0);
v_snd_2670_ = lean_ctor_get(v___x_2668_, 1);
lean_inc_ref(v_filterExport_2656_);
lean_inc(v_snd_2670_);
lean_inc(v_fst_2669_);
lean_inc_ref(v_env_2657_);
v___x_2671_ = lean_apply_3(v_filterExport_2656_, v_env_2657_, v_fst_2669_, v_snd_2670_);
v___x_2672_ = lean_unbox(v___x_2671_);
if (v___x_2672_ == 0)
{
v___y_2663_ = v_b_2661_;
goto v___jp_2662_;
}
else
{
lean_object* v___x_2673_; 
lean_inc(v___x_2668_);
v___x_2673_ = lean_array_push(v_b_2661_, v___x_2668_);
v___y_2663_ = v___x_2673_;
goto v___jp_2662_;
}
}
else
{
lean_dec_ref(v_env_2657_);
lean_dec_ref(v_filterExport_2656_);
return v_b_2661_;
}
v___jp_2662_:
{
size_t v___x_2664_; size_t v___x_2665_; 
v___x_2664_ = ((size_t)1ULL);
v___x_2665_ = lean_usize_add(v_i_2659_, v___x_2664_);
v_i_2659_ = v___x_2665_;
v_b_2661_ = v___y_2663_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object* v_filterExport_2674_, lean_object* v_env_2675_, lean_object* v_as_2676_, lean_object* v_i_2677_, lean_object* v_stop_2678_, lean_object* v_b_2679_){
_start:
{
size_t v_i_boxed_2680_; size_t v_stop_boxed_2681_; lean_object* v_res_2682_; 
v_i_boxed_2680_ = lean_unbox_usize(v_i_2677_);
lean_dec(v_i_2677_);
v_stop_boxed_2681_ = lean_unbox_usize(v_stop_2678_);
lean_dec(v_stop_2678_);
v_res_2682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2674_, v_env_2675_, v_as_2676_, v_i_boxed_2680_, v_stop_boxed_2681_, v_b_2679_);
lean_dec_ref(v_as_2676_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object* v_filterExport_2683_, uint8_t v_preserveOrder_2684_, lean_object* v_env_2685_, lean_object* v_x_2686_){
_start:
{
lean_object* v___y_2688_; 
if (v_preserveOrder_2684_ == 0)
{
lean_object* v_snd_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v_r_2707_; lean_object* v___x_2708_; lean_object* v___y_2710_; lean_object* v___y_2711_; uint8_t v___x_2713_; 
v_snd_2704_ = lean_ctor_get(v_x_2686_, 1);
lean_inc(v_snd_2704_);
lean_dec_ref(v_x_2686_);
v___x_2705_ = lean_unsigned_to_nat(0u);
v___x_2706_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_2707_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_2706_, v_snd_2704_);
lean_dec(v_snd_2704_);
v___x_2708_ = lean_array_get_size(v_r_2707_);
v___x_2713_ = lean_nat_dec_eq(v___x_2708_, v___x_2705_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___y_2717_; uint8_t v___x_2719_; 
v___x_2714_ = lean_unsigned_to_nat(1u);
v___x_2715_ = lean_nat_sub(v___x_2708_, v___x_2714_);
v___x_2719_ = lean_nat_dec_le(v___x_2705_, v___x_2715_);
if (v___x_2719_ == 0)
{
lean_inc(v___x_2715_);
v___y_2717_ = v___x_2715_;
goto v___jp_2716_;
}
else
{
v___y_2717_ = v___x_2705_;
goto v___jp_2716_;
}
v___jp_2716_:
{
uint8_t v___x_2718_; 
v___x_2718_ = lean_nat_dec_le(v___y_2717_, v___x_2715_);
if (v___x_2718_ == 0)
{
lean_dec(v___x_2715_);
lean_inc(v___y_2717_);
v___y_2710_ = v___y_2717_;
v___y_2711_ = v___y_2717_;
goto v___jp_2709_;
}
else
{
v___y_2710_ = v___y_2717_;
v___y_2711_ = v___x_2715_;
goto v___jp_2709_;
}
}
}
else
{
v___y_2688_ = v_r_2707_;
goto v___jp_2687_;
}
v___jp_2709_:
{
lean_object* v___x_2712_; 
v___x_2712_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_2708_, v_r_2707_, v___y_2710_, v___y_2711_);
lean_dec(v___y_2711_);
v___y_2688_ = v___x_2712_;
goto v___jp_2687_;
}
}
else
{
lean_object* v_fst_2720_; lean_object* v_snd_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v_fst_2720_ = lean_ctor_get(v_x_2686_, 0);
lean_inc(v_fst_2720_);
v_snd_2721_ = lean_ctor_get(v_x_2686_, 1);
lean_inc(v_snd_2721_);
lean_dec_ref(v_x_2686_);
v___x_2722_ = lean_array_mk(v_fst_2720_);
v___x_2723_ = l_Array_reverse___redArg(v___x_2722_);
v___x_2724_ = lean_unsigned_to_nat(0u);
v___x_2725_ = lean_array_get_size(v___x_2723_);
v___x_2726_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2721_, v___x_2723_, v___x_2724_, v___x_2725_);
lean_dec_ref(v___x_2723_);
lean_dec(v_snd_2721_);
v___y_2688_ = v___x_2726_;
goto v___jp_2687_;
}
v___jp_2687_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; uint8_t v___x_2692_; 
v___x_2689_ = lean_unsigned_to_nat(0u);
v___x_2690_ = lean_array_get_size(v___y_2688_);
v___x_2691_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2692_ = lean_nat_dec_lt(v___x_2689_, v___x_2690_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; 
lean_dec_ref(v_env_2685_);
lean_dec_ref(v_filterExport_2683_);
v___x_2693_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2691_);
lean_ctor_set(v___x_2693_, 1, v___x_2691_);
lean_ctor_set(v___x_2693_, 2, v___y_2688_);
return v___x_2693_;
}
else
{
uint8_t v___x_2694_; 
v___x_2694_ = lean_nat_dec_le(v___x_2690_, v___x_2690_);
if (v___x_2694_ == 0)
{
if (v___x_2692_ == 0)
{
lean_object* v___x_2695_; 
lean_dec_ref(v_env_2685_);
lean_dec_ref(v_filterExport_2683_);
v___x_2695_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2691_);
lean_ctor_set(v___x_2695_, 1, v___x_2691_);
lean_ctor_set(v___x_2695_, 2, v___y_2688_);
return v___x_2695_;
}
else
{
size_t v___x_2696_; size_t v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2696_ = ((size_t)0ULL);
v___x_2697_ = lean_usize_of_nat(v___x_2690_);
v___x_2698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2683_, v_env_2685_, v___y_2688_, v___x_2696_, v___x_2697_, v___x_2691_);
lean_inc_ref(v___x_2698_);
v___x_2699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
lean_ctor_set(v___x_2699_, 2, v___y_2688_);
return v___x_2699_;
}
}
else
{
size_t v___x_2700_; size_t v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2700_ = ((size_t)0ULL);
v___x_2701_ = lean_usize_of_nat(v___x_2690_);
v___x_2702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2683_, v_env_2685_, v___y_2688_, v___x_2700_, v___x_2701_, v___x_2691_);
lean_inc_ref(v___x_2702_);
v___x_2703_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
lean_ctor_set(v___x_2703_, 2, v___y_2688_);
return v___x_2703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object* v_filterExport_2727_, lean_object* v_preserveOrder_2728_, lean_object* v_env_2729_, lean_object* v_x_2730_){
_start:
{
uint8_t v_preserveOrder_boxed_2731_; lean_object* v_res_2732_; 
v_preserveOrder_boxed_2731_ = lean_unbox(v_preserveOrder_2728_);
v_res_2732_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2727_, v_preserveOrder_boxed_2731_, v_env_2729_, v_x_2730_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object* v_x_2742_){
_start:
{
lean_object* v_snd_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2757_; 
v_snd_2743_ = lean_ctor_get(v_x_2742_, 1);
v_isSharedCheck_2757_ = !lean_is_exclusive(v_x_2742_);
if (v_isSharedCheck_2757_ == 0)
{
lean_object* v_unused_2758_; 
v_unused_2758_ = lean_ctor_get(v_x_2742_, 0);
lean_dec(v_unused_2758_);
v___x_2745_ = v_x_2742_;
v_isShared_2746_ = v_isSharedCheck_2757_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_snd_2743_);
lean_dec(v_x_2742_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2757_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2747_; lean_object* v___y_2749_; 
v___x_2747_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2743_) == 0)
{
lean_object* v_size_2755_; 
v_size_2755_ = lean_ctor_get(v_snd_2743_, 0);
lean_inc(v_size_2755_);
lean_dec_ref_known(v_snd_2743_, 5);
v___y_2749_ = v_size_2755_;
goto v___jp_2748_;
}
else
{
lean_object* v___x_2756_; 
v___x_2756_ = lean_unsigned_to_nat(0u);
v___y_2749_ = v___x_2756_;
goto v___jp_2748_;
}
v___jp_2748_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2750_ = l_Nat_reprFast(v___y_2749_);
v___x_2751_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set_tag(v___x_2745_, 5);
lean_ctor_set(v___x_2745_, 1, v___x_2751_);
lean_ctor_set(v___x_2745_, 0, v___x_2747_);
v___x_2753_ = v___x_2745_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v___x_2751_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object* v_x_2759_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object* v_x_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Lean_registerParametricAttributeExt___redArg___lam__3(v_x_2761_);
lean_dec_ref(v_x_2761_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object* v___x_2763_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2763_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object* v___x_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2766_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object* v___x_2769_, lean_object* v_x_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2769_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object* v___x_2774_, lean_object* v_x_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2774_, v_x_2775_, v___y_2776_);
lean_dec_ref(v___y_2776_);
lean_dec_ref(v_x_2775_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object* v_ref_2789_, uint8_t v_preserveOrder_2790_, lean_object* v_filterExport_2791_){
_start:
{
lean_object* v___f_2793_; lean_object* v___x_2794_; lean_object* v___f_2795_; lean_object* v___f_2796_; lean_object* v___f_2797_; lean_object* v___f_2798_; lean_object* v___f_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___f_2793_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__0));
v___x_2794_ = lean_box(v_preserveOrder_2790_);
v___f_2795_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2795_, 0, v_filterExport_2791_);
lean_closure_set(v___f_2795_, 1, v___x_2794_);
v___f_2796_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__1));
v___f_2797_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__2));
v___f_2798_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__4));
v___f_2799_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__5));
v___x_2800_ = lean_box(2);
v___x_2801_ = lean_box(0);
v___x_2802_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2802_, 0, v_ref_2789_);
lean_ctor_set(v___x_2802_, 1, v___f_2798_);
lean_ctor_set(v___x_2802_, 2, v___f_2799_);
lean_ctor_set(v___x_2802_, 3, v___f_2793_);
lean_ctor_set(v___x_2802_, 4, v___f_2795_);
lean_ctor_set(v___x_2802_, 5, v___f_2796_);
lean_ctor_set(v___x_2802_, 6, v___x_2800_);
lean_ctor_set(v___x_2802_, 7, v___x_2801_);
v___x_2803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
lean_ctor_set(v___x_2803_, 1, v___f_2797_);
v___x_2804_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2803_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object* v_ref_2805_, lean_object* v_preserveOrder_2806_, lean_object* v_filterExport_2807_, lean_object* v_a_2808_){
_start:
{
uint8_t v_preserveOrder_boxed_2809_; lean_object* v_res_2810_; 
v_preserveOrder_boxed_2809_ = lean_unbox(v_preserveOrder_2806_);
v_res_2810_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2805_, v_preserveOrder_boxed_2809_, v_filterExport_2807_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object* v_00_u03b1_2811_, lean_object* v_ref_2812_, uint8_t v_preserveOrder_2813_, lean_object* v_filterExport_2814_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2812_, v_preserveOrder_2813_, v_filterExport_2814_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object* v_00_u03b1_2817_, lean_object* v_ref_2818_, lean_object* v_preserveOrder_2819_, lean_object* v_filterExport_2820_, lean_object* v_a_2821_){
_start:
{
uint8_t v_preserveOrder_boxed_2822_; lean_object* v_res_2823_; 
v_preserveOrder_boxed_2822_ = lean_unbox(v_preserveOrder_2819_);
v_res_2823_ = l_Lean_registerParametricAttributeExt(v_00_u03b1_2817_, v_ref_2818_, v_preserveOrder_boxed_2822_, v_filterExport_2820_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object* v_00_u03b1_2824_, lean_object* v_filterExport_2825_, lean_object* v_env_2826_, lean_object* v_as_2827_, size_t v_i_2828_, size_t v_stop_2829_, lean_object* v_b_2830_){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2825_, v_env_2826_, v_as_2827_, v_i_2828_, v_stop_2829_, v_b_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object* v_00_u03b1_2832_, lean_object* v_filterExport_2833_, lean_object* v_env_2834_, lean_object* v_as_2835_, lean_object* v_i_2836_, lean_object* v_stop_2837_, lean_object* v_b_2838_){
_start:
{
size_t v_i_boxed_2839_; size_t v_stop_boxed_2840_; lean_object* v_res_2841_; 
v_i_boxed_2839_ = lean_unbox_usize(v_i_2836_);
lean_dec(v_i_2836_);
v_stop_boxed_2840_ = lean_unbox_usize(v_stop_2837_);
lean_dec(v_stop_2837_);
v_res_2841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(v_00_u03b1_2832_, v_filterExport_2833_, v_env_2834_, v_as_2835_, v_i_boxed_2839_, v_stop_boxed_2840_, v_b_2838_);
lean_dec_ref(v_as_2835_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object* v_init_2842_, lean_object* v_t_2843_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2842_, v_t_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object* v_init_2845_, lean_object* v_t_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(v_init_2845_, v_t_2846_);
lean_dec(v_t_2846_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object* v_00_u03b1_2848_, lean_object* v_init_2849_, lean_object* v_t_2850_){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2849_, v_t_2850_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object* v_00_u03b1_2852_, lean_object* v_init_2853_, lean_object* v_t_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(v_00_u03b1_2852_, v_init_2853_, v_t_2854_);
lean_dec(v_t_2854_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object* v_00_u03b1_2856_, lean_object* v_n_2857_, lean_object* v_as_2858_, lean_object* v_lo_2859_, lean_object* v_hi_2860_, lean_object* v_w_2861_, lean_object* v_hlo_2862_, lean_object* v_hhi_2863_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2857_, v_as_2858_, v_lo_2859_, v_hi_2860_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object* v_00_u03b1_2865_, lean_object* v_n_2866_, lean_object* v_as_2867_, lean_object* v_lo_2868_, lean_object* v_hi_2869_, lean_object* v_w_2870_, lean_object* v_hlo_2871_, lean_object* v_hhi_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(v_00_u03b1_2865_, v_n_2866_, v_as_2867_, v_lo_2868_, v_hi_2869_, v_w_2870_, v_hlo_2871_, v_hhi_2872_);
lean_dec(v_hi_2869_);
lean_dec(v_n_2866_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object* v_00_u03b1_2874_, lean_object* v_snd_2875_, lean_object* v_as_2876_, lean_object* v_start_2877_, lean_object* v_stop_2878_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2875_, v_as_2876_, v_start_2877_, v_stop_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object* v_00_u03b1_2880_, lean_object* v_snd_2881_, lean_object* v_as_2882_, lean_object* v_start_2883_, lean_object* v_stop_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(v_00_u03b1_2880_, v_snd_2881_, v_as_2882_, v_start_2883_, v_stop_2884_);
lean_dec(v_stop_2884_);
lean_dec(v_start_2883_);
lean_dec_ref(v_as_2882_);
lean_dec(v_snd_2881_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object* v_00_u03b1_2886_, lean_object* v_init_2887_, lean_object* v_x_2888_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2887_, v_x_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2890_, lean_object* v_init_2891_, lean_object* v_x_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(v_00_u03b1_2890_, v_init_2891_, v_x_2892_);
lean_dec(v_x_2892_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object* v_00_u03b1_2894_, lean_object* v_n_2895_, lean_object* v_lo_2896_, lean_object* v_hi_2897_, lean_object* v_hhi_2898_, lean_object* v_pivot_2899_, lean_object* v_as_2900_, lean_object* v_i_2901_, lean_object* v_k_2902_, lean_object* v_ilo_2903_, lean_object* v_ik_2904_, lean_object* v_w_2905_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2897_, v_pivot_2899_, v_as_2900_, v_i_2901_, v_k_2902_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2907_, lean_object* v_n_2908_, lean_object* v_lo_2909_, lean_object* v_hi_2910_, lean_object* v_hhi_2911_, lean_object* v_pivot_2912_, lean_object* v_as_2913_, lean_object* v_i_2914_, lean_object* v_k_2915_, lean_object* v_ilo_2916_, lean_object* v_ik_2917_, lean_object* v_w_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(v_00_u03b1_2907_, v_n_2908_, v_lo_2909_, v_hi_2910_, v_hhi_2911_, v_pivot_2912_, v_as_2913_, v_i_2914_, v_k_2915_, v_ilo_2916_, v_ik_2917_, v_w_2918_);
lean_dec_ref(v_pivot_2912_);
lean_dec(v_hi_2910_);
lean_dec(v_lo_2909_);
lean_dec(v_n_2908_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object* v_00_u03b1_2920_, lean_object* v_snd_2921_, lean_object* v_as_2922_, size_t v_i_2923_, size_t v_stop_2924_, lean_object* v_b_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2921_, v_as_2922_, v_i_2923_, v_stop_2924_, v_b_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2927_, lean_object* v_snd_2928_, lean_object* v_as_2929_, lean_object* v_i_2930_, lean_object* v_stop_2931_, lean_object* v_b_2932_){
_start:
{
size_t v_i_boxed_2933_; size_t v_stop_boxed_2934_; lean_object* v_res_2935_; 
v_i_boxed_2933_ = lean_unbox_usize(v_i_2930_);
lean_dec(v_i_2930_);
v_stop_boxed_2934_ = lean_unbox_usize(v_stop_2931_);
lean_dec(v_stop_2931_);
v_res_2935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(v_00_u03b1_2927_, v_snd_2928_, v_as_2929_, v_i_boxed_2933_, v_stop_boxed_2934_, v_b_2932_);
lean_dec_ref(v_as_2929_);
lean_dec(v_snd_2928_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object* v_env_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v___x_2939_; lean_object* v_nextMacroScope_2940_; lean_object* v_ngen_2941_; lean_object* v_auxDeclNGen_2942_; lean_object* v_traceState_2943_; lean_object* v_messages_2944_; lean_object* v_infoState_2945_; lean_object* v_snapshotTasks_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2957_; 
v___x_2939_ = lean_st_ref_take(v___y_2937_);
v_nextMacroScope_2940_ = lean_ctor_get(v___x_2939_, 1);
v_ngen_2941_ = lean_ctor_get(v___x_2939_, 2);
v_auxDeclNGen_2942_ = lean_ctor_get(v___x_2939_, 3);
v_traceState_2943_ = lean_ctor_get(v___x_2939_, 4);
v_messages_2944_ = lean_ctor_get(v___x_2939_, 6);
v_infoState_2945_ = lean_ctor_get(v___x_2939_, 7);
v_snapshotTasks_2946_ = lean_ctor_get(v___x_2939_, 8);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2957_ == 0)
{
lean_object* v_unused_2958_; lean_object* v_unused_2959_; 
v_unused_2958_ = lean_ctor_get(v___x_2939_, 5);
lean_dec(v_unused_2958_);
v_unused_2959_ = lean_ctor_get(v___x_2939_, 0);
lean_dec(v_unused_2959_);
v___x_2948_ = v___x_2939_;
v_isShared_2949_ = v_isSharedCheck_2957_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_snapshotTasks_2946_);
lean_inc(v_infoState_2945_);
lean_inc(v_messages_2944_);
lean_inc(v_traceState_2943_);
lean_inc(v_auxDeclNGen_2942_);
lean_inc(v_ngen_2941_);
lean_inc(v_nextMacroScope_2940_);
lean_dec(v___x_2939_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2957_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2950_; lean_object* v___x_2952_; 
v___x_2950_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 5, v___x_2950_);
lean_ctor_set(v___x_2948_, 0, v_env_2936_);
v___x_2952_ = v___x_2948_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_env_2936_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v_nextMacroScope_2940_);
lean_ctor_set(v_reuseFailAlloc_2956_, 2, v_ngen_2941_);
lean_ctor_set(v_reuseFailAlloc_2956_, 3, v_auxDeclNGen_2942_);
lean_ctor_set(v_reuseFailAlloc_2956_, 4, v_traceState_2943_);
lean_ctor_set(v_reuseFailAlloc_2956_, 5, v___x_2950_);
lean_ctor_set(v_reuseFailAlloc_2956_, 6, v_messages_2944_);
lean_ctor_set(v_reuseFailAlloc_2956_, 7, v_infoState_2945_);
lean_ctor_set(v_reuseFailAlloc_2956_, 8, v_snapshotTasks_2946_);
v___x_2952_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2953_ = lean_st_ref_put(v___y_2937_, v___x_2952_);
v___x_2954_ = lean_box(0);
v___x_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
return v___x_2955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object* v_env_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2960_, v___y_2961_);
lean_dec(v___y_2961_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object* v_env_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2964_, v___y_2966_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object* v_env_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(v_env_2969_, v___y_2970_, v___y_2971_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object* v_getParam_2974_, lean_object* v_ext_2975_, lean_object* v_afterSet_2976_, lean_object* v_toAttributeImplCore_2977_, lean_object* v_decl_2978_, lean_object* v_stx_2979_, uint8_t v_kind_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; uint8_t v___y_2989_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; uint8_t v___x_3038_; uint8_t v___x_3039_; 
v___x_3038_ = 0;
v___x_3039_ = l_Lean_instBEqAttributeKind_beq(v_kind_2980_, v___x_3038_);
if (v___x_3039_ == 0)
{
lean_object* v_name_3040_; lean_object* v___x_3041_; 
lean_dec(v_stx_2979_);
lean_dec(v_decl_2978_);
lean_dec_ref(v_afterSet_2976_);
lean_dec_ref(v_ext_2975_);
lean_dec_ref(v_getParam_2974_);
v_name_3040_ = lean_ctor_get(v_toAttributeImplCore_2977_, 1);
lean_inc(v_name_3040_);
lean_dec_ref(v_toAttributeImplCore_2977_);
v___x_3041_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_3040_, v_kind_2980_, v___y_2981_, v___y_2982_);
return v___x_3041_;
}
else
{
goto v___jp_3032_;
}
v___jp_2984_:
{
if (v___y_2989_ == 0)
{
lean_object* v___x_2990_; 
lean_dec_ref(v___y_2988_);
v___x_2990_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v___y_2986_, v___y_2987_);
return v___x_2990_;
}
else
{
lean_dec_ref(v___y_2986_);
return v___y_2988_;
}
}
v___jp_2991_:
{
lean_object* v___x_2995_; 
lean_inc(v___y_2994_);
lean_inc_ref(v___y_2993_);
lean_inc(v_decl_2978_);
v___x_2995_ = lean_apply_5(v_getParam_2974_, v_decl_2978_, v_stx_2979_, v___y_2993_, v___y_2994_, lean_box(0));
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2997_; lean_object* v_toEnvExtension_2998_; lean_object* v_env_2999_; lean_object* v_nextMacroScope_3000_; lean_object* v_ngen_3001_; lean_object* v_auxDeclNGen_3002_; lean_object* v_traceState_3003_; lean_object* v_messages_3004_; lean_object* v_infoState_3005_; lean_object* v_snapshotTasks_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3022_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v___x_2995_, 1);
v___x_2997_ = lean_st_ref_take(v___y_2994_);
v_toEnvExtension_2998_ = lean_ctor_get(v_ext_2975_, 0);
v_env_2999_ = lean_ctor_get(v___x_2997_, 0);
v_nextMacroScope_3000_ = lean_ctor_get(v___x_2997_, 1);
v_ngen_3001_ = lean_ctor_get(v___x_2997_, 2);
v_auxDeclNGen_3002_ = lean_ctor_get(v___x_2997_, 3);
v_traceState_3003_ = lean_ctor_get(v___x_2997_, 4);
v_messages_3004_ = lean_ctor_get(v___x_2997_, 6);
v_infoState_3005_ = lean_ctor_get(v___x_2997_, 7);
v_snapshotTasks_3006_ = lean_ctor_get(v___x_2997_, 8);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3022_ == 0)
{
lean_object* v_unused_3023_; 
v_unused_3023_ = lean_ctor_get(v___x_2997_, 5);
lean_dec(v_unused_3023_);
v___x_3008_ = v___x_2997_;
v_isShared_3009_ = v_isSharedCheck_3022_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_snapshotTasks_3006_);
lean_inc(v_infoState_3005_);
lean_inc(v_messages_3004_);
lean_inc(v_traceState_3003_);
lean_inc(v_auxDeclNGen_3002_);
lean_inc(v_ngen_3001_);
lean_inc(v_nextMacroScope_3000_);
lean_inc(v_env_2999_);
lean_dec(v___x_2997_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3022_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v_asyncMode_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3015_; 
v_asyncMode_3010_ = lean_ctor_get(v_toEnvExtension_2998_, 2);
lean_inc(v_asyncMode_3010_);
lean_inc(v_a_2996_);
lean_inc_n(v_decl_2978_, 2);
v___x_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3011_, 0, v_decl_2978_);
lean_ctor_set(v___x_3011_, 1, v_a_2996_);
v___x_3012_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2975_, v_env_2999_, v___x_3011_, v_asyncMode_3010_, v_decl_2978_);
lean_dec(v_asyncMode_3010_);
v___x_3013_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 5, v___x_3013_);
lean_ctor_set(v___x_3008_, 0, v___x_3012_);
v___x_3015_ = v___x_3008_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3012_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_nextMacroScope_3000_);
lean_ctor_set(v_reuseFailAlloc_3021_, 2, v_ngen_3001_);
lean_ctor_set(v_reuseFailAlloc_3021_, 3, v_auxDeclNGen_3002_);
lean_ctor_set(v_reuseFailAlloc_3021_, 4, v_traceState_3003_);
lean_ctor_set(v_reuseFailAlloc_3021_, 5, v___x_3013_);
lean_ctor_set(v_reuseFailAlloc_3021_, 6, v_messages_3004_);
lean_ctor_set(v_reuseFailAlloc_3021_, 7, v_infoState_3005_);
lean_ctor_set(v_reuseFailAlloc_3021_, 8, v_snapshotTasks_3006_);
v___x_3015_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = lean_st_ref_put(v___y_2994_, v___x_3015_);
lean_inc(v___y_2994_);
lean_inc_ref(v___y_2993_);
v___x_3017_ = lean_apply_5(v_afterSet_2976_, v_decl_2978_, v_a_2996_, v___y_2993_, v___y_2994_, lean_box(0));
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_dec_ref(v___y_2992_);
return v___x_3017_;
}
else
{
lean_object* v_a_3018_; uint8_t v___x_3019_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
v___x_3019_ = l_Lean_Exception_isInterrupt(v_a_3018_);
if (v___x_3019_ == 0)
{
uint8_t v___x_3020_; 
v___x_3020_ = l_Lean_Exception_isRuntime(v_a_3018_);
v___y_2985_ = v___y_2993_;
v___y_2986_ = v___y_2992_;
v___y_2987_ = v___y_2994_;
v___y_2988_ = v___x_3017_;
v___y_2989_ = v___x_3020_;
goto v___jp_2984_;
}
else
{
lean_dec(v_a_3018_);
v___y_2985_ = v___y_2993_;
v___y_2986_ = v___y_2992_;
v___y_2987_ = v___y_2994_;
v___y_2988_ = v___x_3017_;
v___y_2989_ = v___x_3019_;
goto v___jp_2984_;
}
}
}
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
lean_dec_ref(v___y_2992_);
lean_dec(v_decl_2978_);
lean_dec_ref(v_afterSet_2976_);
lean_dec_ref(v_ext_2975_);
v_a_3024_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_2995_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_2995_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
v___jp_3032_:
{
lean_object* v___x_3033_; lean_object* v_env_3034_; lean_object* v___x_3035_; 
v___x_3033_ = lean_st_ref_get(v___y_2982_);
v_env_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc_ref(v_env_3034_);
lean_dec(v___x_3033_);
v___x_3035_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3034_, v_decl_2978_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_dec_ref(v_toAttributeImplCore_2977_);
v___y_2992_ = v_env_3034_;
v___y_2993_ = v___y_2981_;
v___y_2994_ = v___y_2982_;
goto v___jp_2991_;
}
else
{
lean_object* v_name_3036_; lean_object* v___x_3037_; 
lean_dec_ref_known(v___x_3035_, 1);
lean_dec_ref(v_env_3034_);
lean_dec(v_stx_2979_);
lean_dec_ref(v_afterSet_2976_);
lean_dec_ref(v_ext_2975_);
lean_dec_ref(v_getParam_2974_);
v_name_3036_ = lean_ctor_get(v_toAttributeImplCore_2977_, 1);
lean_inc(v_name_3036_);
lean_dec_ref(v_toAttributeImplCore_2977_);
v___x_3037_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_3036_, v_decl_2978_, v___y_2981_, v___y_2982_);
return v___x_3037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed(lean_object* v_getParam_3042_, lean_object* v_ext_3043_, lean_object* v_afterSet_3044_, lean_object* v_toAttributeImplCore_3045_, lean_object* v_decl_3046_, lean_object* v_stx_3047_, lean_object* v_kind_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
uint8_t v_kind_boxed_3052_; lean_object* v_res_3053_; 
v_kind_boxed_3052_ = lean_unbox(v_kind_3048_);
v_res_3053_ = l_Lean_registerParametricAttributeForExt___redArg___lam__0(v_getParam_3042_, v_ext_3043_, v_afterSet_3044_, v_toAttributeImplCore_3045_, v_decl_3046_, v_stx_3047_, v_kind_boxed_3052_, v___y_3049_, v___y_3050_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object* v_toAttributeImplCore_3054_, lean_object* v_decl_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v_name_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v_name_3059_ = lean_ctor_get(v_toAttributeImplCore_3054_, 1);
lean_inc(v_name_3059_);
lean_dec_ref(v_toAttributeImplCore_3054_);
v___x_3060_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3061_ = l_Lean_MessageData_ofName(v_name_3059_);
v___x_3062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3060_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
v___x_3063_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3062_);
lean_ctor_set(v___x_3064_, 1, v___x_3063_);
v___x_3065_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3064_, v___y_3056_, v___y_3057_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object* v_toAttributeImplCore_3066_, lean_object* v_decl_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Lean_registerParametricAttributeForExt___redArg___lam__1(v_toAttributeImplCore_3066_, v_decl_3067_, v___y_3068_, v___y_3069_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec(v_decl_3067_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object* v_impl_3072_, lean_object* v_ext_3073_){
_start:
{
lean_object* v_toAttributeImplCore_3075_; lean_object* v_getParam_3076_; lean_object* v_afterSet_3077_; uint8_t v_preserveOrder_3078_; lean_object* v___f_3079_; lean_object* v___f_3080_; lean_object* v_attrImpl_3081_; lean_object* v___x_3082_; 
v_toAttributeImplCore_3075_ = lean_ctor_get(v_impl_3072_, 0);
lean_inc_ref_n(v_toAttributeImplCore_3075_, 3);
v_getParam_3076_ = lean_ctor_get(v_impl_3072_, 1);
lean_inc_ref(v_getParam_3076_);
v_afterSet_3077_ = lean_ctor_get(v_impl_3072_, 2);
lean_inc_ref(v_afterSet_3077_);
v_preserveOrder_3078_ = lean_ctor_get_uint8(v_impl_3072_, sizeof(void*)*4);
lean_dec_ref(v_impl_3072_);
lean_inc_ref(v_ext_3073_);
v___f_3079_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3079_, 0, v_getParam_3076_);
lean_closure_set(v___f_3079_, 1, v_ext_3073_);
lean_closure_set(v___f_3079_, 2, v_afterSet_3077_);
lean_closure_set(v___f_3079_, 3, v_toAttributeImplCore_3075_);
v___f_3080_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_3080_, 0, v_toAttributeImplCore_3075_);
v_attrImpl_3081_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_attrImpl_3081_, 0, v_toAttributeImplCore_3075_);
lean_ctor_set(v_attrImpl_3081_, 1, v___f_3079_);
lean_ctor_set(v_attrImpl_3081_, 2, v___f_3080_);
lean_inc_ref(v_attrImpl_3081_);
v___x_3082_ = l_Lean_registerBuiltinAttribute(v_attrImpl_3081_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3090_; 
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3090_ == 0)
{
lean_object* v_unused_3091_; 
v_unused_3091_ = lean_ctor_get(v___x_3082_, 0);
lean_dec(v_unused_3091_);
v___x_3084_ = v___x_3082_;
v_isShared_3085_ = v_isSharedCheck_3090_;
goto v_resetjp_3083_;
}
else
{
lean_dec(v___x_3082_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3090_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3086_; lean_object* v___x_3088_; 
v___x_3086_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3086_, 0, v_attrImpl_3081_);
lean_ctor_set(v___x_3086_, 1, v_ext_3073_);
lean_ctor_set_uint8(v___x_3086_, sizeof(void*)*2, v_preserveOrder_3078_);
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 0, v___x_3086_);
v___x_3088_ = v___x_3084_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3086_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_dec_ref_known(v_attrImpl_3081_, 3);
lean_dec_ref(v_ext_3073_);
v_a_3092_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3082_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3082_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object* v_impl_3100_, lean_object* v_ext_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3100_, v_ext_3101_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object* v_00_u03b1_3104_, lean_object* v_impl_3105_, lean_object* v_ext_3106_){
_start:
{
lean_object* v___x_3108_; 
v___x_3108_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3105_, v_ext_3106_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object* v_00_u03b1_3109_, lean_object* v_impl_3110_, lean_object* v_ext_3111_, lean_object* v_a_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_registerParametricAttributeForExt(v_00_u03b1_3109_, v_impl_3110_, v_ext_3111_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_3114_){
_start:
{
lean_object* v_toAttributeImplCore_3116_; uint8_t v_preserveOrder_3117_; lean_object* v_filterExport_3118_; lean_object* v_ref_3119_; lean_object* v___x_3120_; 
v_toAttributeImplCore_3116_ = lean_ctor_get(v_impl_3114_, 0);
v_preserveOrder_3117_ = lean_ctor_get_uint8(v_impl_3114_, sizeof(void*)*4);
v_filterExport_3118_ = lean_ctor_get(v_impl_3114_, 3);
v_ref_3119_ = lean_ctor_get(v_toAttributeImplCore_3116_, 0);
lean_inc_ref(v_filterExport_3118_);
lean_inc(v_ref_3119_);
v___x_3120_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_3119_, v_preserveOrder_3117_, v_filterExport_3118_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; lean_object* v___x_3122_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
lean_dec_ref_known(v___x_3120_, 1);
v___x_3122_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3114_, v_a_3121_);
return v___x_3122_;
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec_ref(v_impl_3114_);
v_a_3123_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3120_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3120_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_3131_, lean_object* v_a_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_Lean_registerParametricAttribute___redArg(v_impl_3131_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_3134_, lean_object* v_impl_3135_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l_Lean_registerParametricAttribute___redArg(v_impl_3135_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_3138_, lean_object* v_impl_3139_, lean_object* v_a_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Lean_registerParametricAttribute(v_00_u03b1_3138_, v_impl_3139_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(lean_object* v_decl_3142_, lean_object* v___x_3143_, lean_object* v___x_3144_, lean_object* v_a_3145_, lean_object* v_x_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v_fst_3148_; uint8_t v___x_3149_; 
v_fst_3148_ = lean_ctor_get(v_a_3145_, 0);
v___x_3149_ = lean_name_eq(v_fst_3148_, v_decl_3142_);
if (v___x_3149_ == 0)
{
lean_object* v___x_3150_; 
lean_dec_ref(v_a_3145_);
v___x_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3143_);
return v___x_3150_;
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
lean_dec_ref(v___x_3143_);
v___x_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3151_, 0, v_a_3145_);
v___x_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3151_);
v___x_3153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3152_);
lean_ctor_set(v___x_3153_, 1, v___x_3144_);
v___x_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
return v___x_3154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed(lean_object* v_decl_3155_, lean_object* v___x_3156_, lean_object* v___x_3157_, lean_object* v_a_3158_, lean_object* v_x_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(v_decl_3155_, v___x_3156_, v___x_3157_, v_a_3158_, v_x_3159_, v___y_3160_);
lean_dec_ref(v___y_3160_);
lean_dec(v_decl_3155_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object* v_inst_3189_, lean_object* v_ext_3190_, uint8_t v_preserveOrder_3191_, lean_object* v_env_3192_, lean_object* v_decl_3193_){
_start:
{
lean_object* v___y_3195_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3207_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3192_, v_decl_3193_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_toEnvExtension_3208_; lean_object* v_asyncMode_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v_snd_3212_; lean_object* v___x_3213_; 
lean_dec(v_inst_3189_);
v_toEnvExtension_3208_ = lean_ctor_get(v_ext_3190_, 0);
v_asyncMode_3209_ = lean_ctor_get(v_toEnvExtension_3208_, 2);
v___x_3210_ = lean_box(0);
v___x_3211_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3206_, v_ext_3190_, v_env_3192_, v_asyncMode_3209_, v___x_3210_);
v_snd_3212_ = lean_ctor_get(v___x_3211_, 1);
lean_inc(v_snd_3212_);
lean_dec(v___x_3211_);
v___x_3213_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3212_, v_decl_3193_);
lean_dec(v_decl_3193_);
lean_dec(v_snd_3212_);
return v___x_3213_;
}
else
{
if (v_preserveOrder_3191_ == 0)
{
lean_object* v_val_3214_; uint8_t v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; uint8_t v___x_3219_; 
v_val_3214_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_val_3214_);
lean_dec_ref_known(v___x_3207_, 1);
v___x_3215_ = 0;
v___x_3216_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3206_, v_ext_3190_, v_env_3192_, v_val_3214_, v___x_3215_);
lean_dec(v_val_3214_);
lean_dec_ref(v_env_3192_);
v___x_3217_ = lean_unsigned_to_nat(0u);
v___x_3218_ = lean_array_get_size(v___x_3216_);
v___x_3219_ = lean_nat_dec_lt(v___x_3217_, v___x_3218_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; 
lean_dec_ref(v___x_3216_);
lean_dec(v_decl_3193_);
lean_dec(v_inst_3189_);
v___x_3220_ = lean_box(0);
return v___x_3220_;
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; uint8_t v___x_3223_; 
v___x_3221_ = lean_unsigned_to_nat(1u);
v___x_3222_ = lean_nat_sub(v___x_3218_, v___x_3221_);
v___x_3223_ = lean_nat_dec_le(v___x_3217_, v___x_3222_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; 
lean_dec(v___x_3222_);
lean_dec_ref(v___x_3216_);
lean_dec(v_decl_3193_);
lean_dec(v_inst_3189_);
v___x_3224_ = lean_box(0);
return v___x_3224_;
}
else
{
lean_object* v___f_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___f_3225_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
v___x_3226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3226_, 0, v_decl_3193_);
lean_ctor_set(v___x_3226_, 1, v_inst_3189_);
v___x_3227_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3228_ = l_Array_binSearchAux___redArg(v___f_3225_, v___x_3227_, v___x_3216_, v___x_3226_, v___x_3217_, v___x_3222_);
lean_dec_ref(v___x_3216_);
v___y_3195_ = v___x_3228_;
goto v___jp_3194_;
}
}
}
else
{
lean_object* v_val_3229_; uint8_t v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___f_3236_; size_t v_sz_3237_; size_t v___x_3238_; lean_object* v___x_3239_; lean_object* v_fst_3240_; 
lean_dec(v_inst_3189_);
v_val_3229_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_val_3229_);
lean_dec_ref_known(v___x_3207_, 1);
v___x_3230_ = 0;
v___x_3231_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3206_, v_ext_3190_, v_env_3192_, v_val_3229_, v___x_3230_);
lean_dec(v_val_3229_);
lean_dec_ref(v_env_3192_);
v___x_3232_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12));
v___x_3233_ = lean_box(0);
v___x_3234_ = lean_box(0);
v___x_3235_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13));
v___f_3236_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3236_, 0, v_decl_3193_);
lean_closure_set(v___f_3236_, 1, v___x_3235_);
lean_closure_set(v___f_3236_, 2, v___x_3234_);
v_sz_3237_ = lean_array_size(v___x_3231_);
v___x_3238_ = ((size_t)0ULL);
v___x_3239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3232_, v___x_3231_, v___f_3236_, v_sz_3237_, v___x_3238_, v___x_3235_);
v_fst_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_fst_3240_);
lean_dec(v___x_3239_);
if (lean_obj_tag(v_fst_3240_) == 0)
{
return v___x_3233_;
}
else
{
lean_object* v_val_3241_; 
v_val_3241_ = lean_ctor_get(v_fst_3240_, 0);
lean_inc(v_val_3241_);
lean_dec_ref_known(v_fst_3240_, 1);
v___y_3195_ = v_val_3241_;
goto v___jp_3194_;
}
}
}
v___jp_3194_:
{
if (lean_obj_tag(v___y_3195_) == 0)
{
lean_object* v___x_3196_; 
v___x_3196_ = lean_box(0);
return v___x_3196_;
}
else
{
lean_object* v_val_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3205_; 
v_val_3197_ = lean_ctor_get(v___y_3195_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___y_3195_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3199_ = v___y_3195_;
v_isShared_3200_ = v_isSharedCheck_3205_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_val_3197_);
lean_dec(v___y_3195_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3205_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v_snd_3201_; lean_object* v___x_3203_; 
v_snd_3201_ = lean_ctor_get(v_val_3197_, 1);
lean_inc(v_snd_3201_);
lean_dec(v_val_3197_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 0, v_snd_3201_);
v___x_3203_ = v___x_3199_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_snd_3201_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object* v_inst_3242_, lean_object* v_ext_3243_, lean_object* v_preserveOrder_3244_, lean_object* v_env_3245_, lean_object* v_decl_3246_){
_start:
{
uint8_t v_preserveOrder_boxed_3247_; lean_object* v_res_3248_; 
v_preserveOrder_boxed_3247_ = lean_unbox(v_preserveOrder_3244_);
v_res_3248_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3242_, v_ext_3243_, v_preserveOrder_boxed_3247_, v_env_3245_, v_decl_3246_);
lean_dec_ref(v_ext_3243_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object* v_00_u03b1_3249_, lean_object* v_inst_3250_, lean_object* v_ext_3251_, uint8_t v_preserveOrder_3252_, lean_object* v_env_3253_, lean_object* v_decl_3254_){
_start:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3250_, v_ext_3251_, v_preserveOrder_3252_, v_env_3253_, v_decl_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object* v_00_u03b1_3256_, lean_object* v_inst_3257_, lean_object* v_ext_3258_, lean_object* v_preserveOrder_3259_, lean_object* v_env_3260_, lean_object* v_decl_3261_){
_start:
{
uint8_t v_preserveOrder_boxed_3262_; lean_object* v_res_3263_; 
v_preserveOrder_boxed_3262_ = lean_unbox(v_preserveOrder_3259_);
v_res_3263_ = l_Lean_ParametricAttribute_getParamFromExt_x3f(v_00_u03b1_3256_, v_inst_3257_, v_ext_3258_, v_preserveOrder_boxed_3262_, v_env_3260_, v_decl_3261_);
lean_dec_ref(v_ext_3258_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3264_, lean_object* v_attr_3265_, lean_object* v_env_3266_, lean_object* v_decl_3267_){
_start:
{
lean_object* v_ext_3268_; uint8_t v_preserveOrder_3269_; lean_object* v___x_3270_; 
v_ext_3268_ = lean_ctor_get(v_attr_3265_, 1);
v_preserveOrder_3269_ = lean_ctor_get_uint8(v_attr_3265_, sizeof(void*)*2);
v___x_3270_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3264_, v_ext_3268_, v_preserveOrder_3269_, v_env_3266_, v_decl_3267_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3271_, lean_object* v_attr_3272_, lean_object* v_env_3273_, lean_object* v_decl_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3271_, v_attr_3272_, v_env_3273_, v_decl_3274_);
lean_dec_ref(v_attr_3272_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3276_, lean_object* v_inst_3277_, lean_object* v_attr_3278_, lean_object* v_env_3279_, lean_object* v_decl_3280_){
_start:
{
lean_object* v___x_3281_; 
v___x_3281_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3277_, v_attr_3278_, v_env_3279_, v_decl_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3282_, lean_object* v_inst_3283_, lean_object* v_attr_3284_, lean_object* v_env_3285_, lean_object* v_decl_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3282_, v_inst_3283_, v_attr_3284_, v_env_3285_, v_decl_3286_);
lean_dec_ref(v_attr_3284_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object* v_ext_3292_, lean_object* v_attr_3293_, lean_object* v_env_3294_, lean_object* v_decl_3295_, lean_object* v_param_3296_){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3294_, v_decl_3295_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_toEnvExtension_3298_; lean_object* v_asyncMode_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v_snd_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3333_; 
v_toEnvExtension_3298_ = lean_ctor_get(v_ext_3292_, 0);
v_asyncMode_3299_ = lean_ctor_get(v_toEnvExtension_3298_, 2);
lean_inc(v_asyncMode_3299_);
v___x_3300_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3301_ = lean_box(0);
lean_inc_ref(v_env_3294_);
v___x_3302_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3300_, v_ext_3292_, v_env_3294_, v_asyncMode_3299_, v___x_3301_);
v_snd_3303_ = lean_ctor_get(v___x_3302_, 1);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3333_ == 0)
{
lean_object* v_unused_3334_; 
v_unused_3334_ = lean_ctor_get(v___x_3302_, 0);
lean_dec(v_unused_3334_);
v___x_3305_ = v___x_3302_;
v_isShared_3306_ = v_isSharedCheck_3333_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_snd_3303_);
lean_dec(v___x_3302_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3333_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3307_; 
v___x_3307_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3303_, v_decl_3295_);
lean_dec(v_snd_3303_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v___x_3309_; 
lean_dec_ref(v_attr_3293_);
if (v_isShared_3306_ == 0)
{
lean_ctor_set(v___x_3305_, 1, v_param_3296_);
lean_ctor_set(v___x_3305_, 0, v_decl_3295_);
v___x_3309_ = v___x_3305_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_decl_3295_);
lean_ctor_set(v_reuseFailAlloc_3312_, 1, v_param_3296_);
v___x_3309_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3292_, v_env_3294_, v___x_3309_, v_asyncMode_3299_, v___x_3301_);
lean_dec(v_asyncMode_3299_);
v___x_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
return v___x_3311_;
}
}
else
{
lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3331_; 
lean_del_object(v___x_3305_);
lean_dec(v_asyncMode_3299_);
lean_dec(v_param_3296_);
lean_dec_ref(v_env_3294_);
lean_dec_ref(v_ext_3292_);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3331_ == 0)
{
lean_object* v_unused_3332_; 
v_unused_3332_ = lean_ctor_get(v___x_3307_, 0);
lean_dec(v_unused_3332_);
v___x_3314_ = v___x_3307_;
v_isShared_3315_ = v_isSharedCheck_3331_;
goto v_resetjp_3313_;
}
else
{
lean_dec(v___x_3307_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3331_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v_toAttributeImplCore_3316_; lean_object* v_name_3317_; uint8_t v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3329_; 
v_toAttributeImplCore_3316_ = lean_ctor_get(v_attr_3293_, 0);
lean_inc_ref(v_toAttributeImplCore_3316_);
lean_dec_ref(v_attr_3293_);
v_name_3317_ = lean_ctor_get(v_toAttributeImplCore_3316_, 1);
lean_inc(v_name_3317_);
lean_dec_ref(v_toAttributeImplCore_3316_);
v___x_3318_ = 1;
v___x_3319_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3320_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3317_, v___x_3318_);
v___x_3321_ = lean_string_append(v___x_3319_, v___x_3320_);
lean_dec_ref(v___x_3320_);
v___x_3322_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3323_ = lean_string_append(v___x_3321_, v___x_3322_);
v___x_3324_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3295_, v___x_3318_);
v___x_3325_ = lean_string_append(v___x_3323_, v___x_3324_);
lean_dec_ref(v___x_3324_);
v___x_3326_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2));
v___x_3327_ = lean_string_append(v___x_3325_, v___x_3326_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set_tag(v___x_3314_, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3327_);
v___x_3329_ = v___x_3314_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3327_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
}
else
{
lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3353_; 
lean_dec(v_param_3296_);
lean_dec_ref(v_env_3294_);
lean_dec_ref(v_ext_3292_);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3353_ == 0)
{
lean_object* v_unused_3354_; 
v_unused_3354_ = lean_ctor_get(v___x_3297_, 0);
lean_dec(v_unused_3354_);
v___x_3336_ = v___x_3297_;
v_isShared_3337_ = v_isSharedCheck_3353_;
goto v_resetjp_3335_;
}
else
{
lean_dec(v___x_3297_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3353_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v_toAttributeImplCore_3338_; lean_object* v_name_3339_; uint8_t v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3351_; 
v_toAttributeImplCore_3338_ = lean_ctor_get(v_attr_3293_, 0);
lean_inc_ref(v_toAttributeImplCore_3338_);
lean_dec_ref(v_attr_3293_);
v_name_3339_ = lean_ctor_get(v_toAttributeImplCore_3338_, 1);
lean_inc(v_name_3339_);
lean_dec_ref(v_toAttributeImplCore_3338_);
v___x_3340_ = 1;
v___x_3341_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3342_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3339_, v___x_3340_);
v___x_3343_ = lean_string_append(v___x_3341_, v___x_3342_);
lean_dec_ref(v___x_3342_);
v___x_3344_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3345_ = lean_string_append(v___x_3343_, v___x_3344_);
v___x_3346_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3295_, v___x_3340_);
v___x_3347_ = lean_string_append(v___x_3345_, v___x_3346_);
lean_dec_ref(v___x_3346_);
v___x_3348_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3));
v___x_3349_ = lean_string_append(v___x_3347_, v___x_3348_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set_tag(v___x_3336_, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3349_);
v___x_3351_ = v___x_3336_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3349_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object* v_00_u03b1_3355_, lean_object* v_ext_3356_, lean_object* v_attr_3357_, lean_object* v_env_3358_, lean_object* v_decl_3359_, lean_object* v_param_3360_){
_start:
{
lean_object* v___x_3361_; 
v___x_3361_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3356_, v_attr_3357_, v_env_3358_, v_decl_3359_, v_param_3360_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3362_, lean_object* v_env_3363_, lean_object* v_decl_3364_, lean_object* v_param_3365_){
_start:
{
lean_object* v_attr_3366_; lean_object* v_ext_3367_; lean_object* v___x_3368_; 
v_attr_3366_ = lean_ctor_get(v_attr_3362_, 0);
lean_inc_ref(v_attr_3366_);
v_ext_3367_ = lean_ctor_get(v_attr_3362_, 1);
lean_inc_ref(v_ext_3367_);
lean_dec_ref(v_attr_3362_);
v___x_3368_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3367_, v_attr_3366_, v_env_3363_, v_decl_3364_, v_param_3365_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3369_, lean_object* v_attr_3370_, lean_object* v_env_3371_, lean_object* v_decl_3372_, lean_object* v_param_3373_){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3370_, v_env_3371_, v_decl_3372_, v_param_3373_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object* v_x_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3378_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object* v_x_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l_Lean_instInhabitedEnumAttributes_default___lam__0(v_x_3380_, v___y_3381_);
lean_dec_ref(v___y_3381_);
lean_dec_ref(v_x_3380_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object* v_s_3384_, lean_object* v_x_3385_){
_start:
{
lean_inc(v_s_3384_);
return v_s_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object* v_s_3386_, lean_object* v_x_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l_Lean_instInhabitedEnumAttributes_default___lam__1(v_s_3386_, v_x_3387_);
lean_dec_ref(v_x_3387_);
lean_dec(v_s_3386_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object* v_x_3389_, lean_object* v_x_3390_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object* v_x_3392_, lean_object* v_x_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Lean_instInhabitedEnumAttributes_default___lam__2(v_x_3392_, v_x_3393_);
lean_dec(v_x_3393_);
lean_dec_ref(v_x_3392_);
return v_res_3394_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__3(void){
_start:
{
lean_object* v___x_3398_; 
v___x_3398_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_3398_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__4(void){
_start:
{
lean_object* v___f_3399_; lean_object* v___f_3400_; lean_object* v___f_3401_; lean_object* v___f_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___f_3399_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3400_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__2));
v___f_3401_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__1));
v___f_3402_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__0));
v___x_3403_ = lean_box(0);
v___x_3404_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__3, &l_Lean_instInhabitedEnumAttributes_default___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__3);
v___x_3405_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
lean_ctor_set(v___x_3405_, 1, v___x_3403_);
lean_ctor_set(v___x_3405_, 2, v___f_3402_);
lean_ctor_set(v___x_3405_, 3, v___f_3401_);
lean_ctor_set(v___x_3405_, 4, v___f_3400_);
lean_ctor_set(v___x_3405_, 5, v___f_3399_);
return v___x_3405_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__5(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3406_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__4, &l_Lean_instInhabitedEnumAttributes_default___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__4);
v___x_3407_ = lean_box(0);
v___x_3408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
lean_ctor_set(v___x_3408_, 1, v___x_3406_);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3409_){
_start:
{
lean_object* v___x_3410_; 
v___x_3410_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__5, &l_Lean_instInhabitedEnumAttributes_default___closed__5_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__5);
return v___x_3410_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes___closed__0(void){
_start:
{
lean_object* v___x_3411_; 
v___x_3411_ = l_Lean_instInhabitedEnumAttributes_default(lean_box(0));
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3412_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes___closed__0, &l_Lean_instInhabitedEnumAttributes___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes___closed__0);
return v___x_3413_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3414_; 
v___x_3414_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3415_){
_start:
{
lean_object* v___x_3416_; 
v___x_3416_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3417_);
lean_dec(v_x_3417_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3419_, lean_object* v_x_3420_, lean_object* v_x_3421_){
_start:
{
if (lean_obj_tag(v_x_3421_) == 0)
{
return v_x_3420_;
}
else
{
lean_object* v_head_3422_; lean_object* v_tail_3423_; lean_object* v___x_3424_; 
v_head_3422_ = lean_ctor_get(v_x_3421_, 0);
lean_inc(v_head_3422_);
v_tail_3423_ = lean_ctor_get(v_x_3421_, 1);
lean_inc(v_tail_3423_);
lean_dec_ref_known(v_x_3421_, 2);
v___x_3424_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3419_, v_head_3422_);
if (lean_obj_tag(v___x_3424_) == 1)
{
lean_object* v_val_3425_; lean_object* v___x_3426_; 
v_val_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_val_3425_);
lean_dec_ref_known(v___x_3424_, 1);
v___x_3426_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3422_, v_val_3425_, v_x_3420_);
v_x_3420_ = v___x_3426_;
v_x_3421_ = v_tail_3423_;
goto _start;
}
else
{
lean_dec(v___x_3424_);
lean_dec(v_head_3422_);
v_x_3421_ = v_tail_3423_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3429_, lean_object* v_x_3430_, lean_object* v_x_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3429_, v_x_3430_, v_x_3431_);
lean_dec(v_newState_3429_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3433_, lean_object* v_newState_3434_, lean_object* v_consts_3435_, lean_object* v_st_3436_){
_start:
{
lean_object* v___x_3437_; 
v___x_3437_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3434_, v_st_3436_, v_consts_3435_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3438_, lean_object* v_newState_3439_, lean_object* v_consts_3440_, lean_object* v_st_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3438_, v_newState_3439_, v_consts_3440_, v_st_3441_);
lean_dec(v_newState_3439_);
lean_dec(v_x_3438_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3452_){
_start:
{
lean_object* v___x_3453_; lean_object* v___y_3455_; 
v___x_3453_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3452_) == 0)
{
lean_object* v_size_3459_; 
v_size_3459_ = lean_ctor_get(v_s_3452_, 0);
lean_inc(v_size_3459_);
lean_dec_ref_known(v_s_3452_, 5);
v___y_3455_ = v_size_3459_;
goto v___jp_3454_;
}
else
{
lean_object* v___x_3460_; 
v___x_3460_ = lean_unsigned_to_nat(0u);
v___y_3455_ = v___x_3460_;
goto v___jp_3454_;
}
v___jp_3454_:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3456_ = l_Nat_reprFast(v___y_3455_);
v___x_3457_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
v___x_3458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3453_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
return v___x_3458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3461_, lean_object* v_as_3462_, size_t v_i_3463_, size_t v_stop_3464_, lean_object* v_b_3465_){
_start:
{
lean_object* v___y_3467_; uint8_t v___x_3471_; 
v___x_3471_ = lean_usize_dec_eq(v_i_3463_, v_stop_3464_);
if (v___x_3471_ == 0)
{
lean_object* v___x_3472_; lean_object* v_fst_3473_; uint8_t v___x_3474_; lean_object* v___x_3475_; uint8_t v___x_3476_; 
v___x_3472_ = lean_array_uget_borrowed(v_as_3462_, v_i_3463_);
v_fst_3473_ = lean_ctor_get(v___x_3472_, 0);
v___x_3474_ = 1;
lean_inc_ref(v_env_3461_);
v___x_3475_ = l_Lean_Environment_setExporting(v_env_3461_, v___x_3474_);
lean_inc(v_fst_3473_);
v___x_3476_ = l_Lean_Environment_contains(v___x_3475_, v_fst_3473_, v___x_3471_);
if (v___x_3476_ == 0)
{
v___y_3467_ = v_b_3465_;
goto v___jp_3466_;
}
else
{
lean_object* v___x_3477_; 
lean_inc(v___x_3472_);
v___x_3477_ = lean_array_push(v_b_3465_, v___x_3472_);
v___y_3467_ = v___x_3477_;
goto v___jp_3466_;
}
}
else
{
lean_dec_ref(v_env_3461_);
return v_b_3465_;
}
v___jp_3466_:
{
size_t v___x_3468_; size_t v___x_3469_; 
v___x_3468_ = ((size_t)1ULL);
v___x_3469_ = lean_usize_add(v_i_3463_, v___x_3468_);
v_i_3463_ = v___x_3469_;
v_b_3465_ = v___y_3467_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3478_, lean_object* v_as_3479_, lean_object* v_i_3480_, lean_object* v_stop_3481_, lean_object* v_b_3482_){
_start:
{
size_t v_i_boxed_3483_; size_t v_stop_boxed_3484_; lean_object* v_res_3485_; 
v_i_boxed_3483_ = lean_unbox_usize(v_i_3480_);
lean_dec(v_i_3480_);
v_stop_boxed_3484_ = lean_unbox_usize(v_stop_3481_);
lean_dec(v_stop_3481_);
v_res_3485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3478_, v_as_3479_, v_i_boxed_3483_, v_stop_boxed_3484_, v_b_3482_);
lean_dec_ref(v_as_3479_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3486_, lean_object* v_m_3487_){
_start:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___y_3491_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___y_3508_; lean_object* v___y_3509_; uint8_t v___x_3511_; 
v___x_3488_ = lean_unsigned_to_nat(0u);
v___x_3489_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_3505_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_3489_, v_m_3487_);
v___x_3506_ = lean_array_get_size(v___x_3505_);
v___x_3511_ = lean_nat_dec_eq(v___x_3506_, v___x_3488_);
if (v___x_3511_ == 0)
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___y_3515_; uint8_t v___x_3517_; 
v___x_3512_ = lean_unsigned_to_nat(1u);
v___x_3513_ = lean_nat_sub(v___x_3506_, v___x_3512_);
v___x_3517_ = lean_nat_dec_le(v___x_3488_, v___x_3513_);
if (v___x_3517_ == 0)
{
lean_inc(v___x_3513_);
v___y_3515_ = v___x_3513_;
goto v___jp_3514_;
}
else
{
v___y_3515_ = v___x_3488_;
goto v___jp_3514_;
}
v___jp_3514_:
{
uint8_t v___x_3516_; 
v___x_3516_ = lean_nat_dec_le(v___y_3515_, v___x_3513_);
if (v___x_3516_ == 0)
{
lean_dec(v___x_3513_);
lean_inc(v___y_3515_);
v___y_3508_ = v___y_3515_;
v___y_3509_ = v___y_3515_;
goto v___jp_3507_;
}
else
{
v___y_3508_ = v___y_3515_;
v___y_3509_ = v___x_3513_;
goto v___jp_3507_;
}
}
}
else
{
v___y_3491_ = v___x_3505_;
goto v___jp_3490_;
}
v___jp_3490_:
{
lean_object* v___x_3492_; uint8_t v___x_3493_; 
v___x_3492_ = lean_array_get_size(v___y_3491_);
v___x_3493_ = lean_nat_dec_lt(v___x_3488_, v___x_3492_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3494_; 
lean_dec_ref(v_env_3486_);
v___x_3494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3489_);
lean_ctor_set(v___x_3494_, 1, v___x_3489_);
lean_ctor_set(v___x_3494_, 2, v___y_3491_);
return v___x_3494_;
}
else
{
uint8_t v___x_3495_; 
v___x_3495_ = lean_nat_dec_le(v___x_3492_, v___x_3492_);
if (v___x_3495_ == 0)
{
if (v___x_3493_ == 0)
{
lean_object* v___x_3496_; 
lean_dec_ref(v_env_3486_);
v___x_3496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3489_);
lean_ctor_set(v___x_3496_, 1, v___x_3489_);
lean_ctor_set(v___x_3496_, 2, v___y_3491_);
return v___x_3496_;
}
else
{
size_t v___x_3497_; size_t v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3497_ = ((size_t)0ULL);
v___x_3498_ = lean_usize_of_nat(v___x_3492_);
v___x_3499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3486_, v___y_3491_, v___x_3497_, v___x_3498_, v___x_3489_);
lean_inc_ref(v___x_3499_);
v___x_3500_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
lean_ctor_set(v___x_3500_, 1, v___x_3499_);
lean_ctor_set(v___x_3500_, 2, v___y_3491_);
return v___x_3500_;
}
}
else
{
size_t v___x_3501_; size_t v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3501_ = ((size_t)0ULL);
v___x_3502_ = lean_usize_of_nat(v___x_3492_);
v___x_3503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3486_, v___y_3491_, v___x_3501_, v___x_3502_, v___x_3489_);
lean_inc_ref(v___x_3503_);
v___x_3504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
lean_ctor_set(v___x_3504_, 1, v___x_3503_);
lean_ctor_set(v___x_3504_, 2, v___y_3491_);
return v___x_3504_;
}
}
}
v___jp_3507_:
{
lean_object* v___x_3510_; 
v___x_3510_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_3506_, v___x_3505_, v___y_3508_, v___y_3509_);
lean_dec(v___y_3509_);
v___y_3491_ = v___x_3510_;
goto v___jp_3490_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3518_, lean_object* v_m_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3518_, v_m_3519_);
lean_dec(v_m_3519_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3521_, lean_object* v_p_3522_){
_start:
{
lean_object* v_fst_3523_; lean_object* v_snd_3524_; lean_object* v___x_3525_; 
v_fst_3523_ = lean_ctor_get(v_p_3522_, 0);
lean_inc(v_fst_3523_);
v_snd_3524_ = lean_ctor_get(v_p_3522_, 1);
lean_inc(v_snd_3524_);
lean_dec_ref(v_p_3522_);
v___x_3525_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3523_, v_snd_3524_, v_s_3521_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3526_, lean_object* v_x_3527_, lean_object* v_x_3528_){
_start:
{
lean_object* v___x_3530_; 
v___x_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3526_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3531_, lean_object* v_x_3532_, lean_object* v_x_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3531_, v_x_3532_, v_x_3533_);
lean_dec_ref(v_x_3533_);
lean_dec_ref(v_x_3532_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3536_, lean_object* v_snd_3537_, lean_object* v_a_3538_, lean_object* v_fst_3539_, lean_object* v_decl_3540_, lean_object* v_stx_3541_, uint8_t v_kind_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___x_3589_; 
v___x_3589_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3541_, v___y_3543_, v___y_3544_);
if (lean_obj_tag(v___x_3589_) == 0)
{
uint8_t v___x_3590_; uint8_t v___x_3591_; 
lean_dec_ref_known(v___x_3589_, 1);
v___x_3590_ = 0;
v___x_3591_ = l_Lean_instBEqAttributeKind_beq(v_kind_3542_, v___x_3590_);
if (v___x_3591_ == 0)
{
lean_object* v___x_3592_; 
lean_dec(v_decl_3540_);
lean_dec_ref(v_a_3538_);
lean_dec(v_snd_3537_);
lean_dec_ref(v_validate_3536_);
v___x_3592_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3539_, v_kind_3542_, v___y_3543_, v___y_3544_);
return v___x_3592_;
}
else
{
v___y_3583_ = v___y_3543_;
v___y_3584_ = v___y_3544_;
goto v___jp_3582_;
}
}
else
{
lean_dec(v_decl_3540_);
lean_dec(v_fst_3539_);
lean_dec_ref(v_a_3538_);
lean_dec(v_snd_3537_);
lean_dec_ref(v_validate_3536_);
return v___x_3589_;
}
v___jp_3546_:
{
lean_object* v___x_3549_; 
lean_inc(v___y_3548_);
lean_inc_ref(v___y_3547_);
lean_inc(v_snd_3537_);
lean_inc(v_decl_3540_);
v___x_3549_ = lean_apply_5(v_validate_3536_, v_decl_3540_, v_snd_3537_, v___y_3547_, v___y_3548_, lean_box(0));
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3580_; 
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3580_ == 0)
{
lean_object* v_unused_3581_; 
v_unused_3581_ = lean_ctor_get(v___x_3549_, 0);
lean_dec(v_unused_3581_);
v___x_3551_ = v___x_3549_;
v_isShared_3552_ = v_isSharedCheck_3580_;
goto v_resetjp_3550_;
}
else
{
lean_dec(v___x_3549_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3580_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3553_; lean_object* v_toEnvExtension_3554_; lean_object* v_env_3555_; lean_object* v_nextMacroScope_3556_; lean_object* v_ngen_3557_; lean_object* v_auxDeclNGen_3558_; lean_object* v_traceState_3559_; lean_object* v_messages_3560_; lean_object* v_infoState_3561_; lean_object* v_snapshotTasks_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3578_; 
v___x_3553_ = lean_st_ref_take(v___y_3548_);
v_toEnvExtension_3554_ = lean_ctor_get(v_a_3538_, 0);
v_env_3555_ = lean_ctor_get(v___x_3553_, 0);
v_nextMacroScope_3556_ = lean_ctor_get(v___x_3553_, 1);
v_ngen_3557_ = lean_ctor_get(v___x_3553_, 2);
v_auxDeclNGen_3558_ = lean_ctor_get(v___x_3553_, 3);
v_traceState_3559_ = lean_ctor_get(v___x_3553_, 4);
v_messages_3560_ = lean_ctor_get(v___x_3553_, 6);
v_infoState_3561_ = lean_ctor_get(v___x_3553_, 7);
v_snapshotTasks_3562_ = lean_ctor_get(v___x_3553_, 8);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3578_ == 0)
{
lean_object* v_unused_3579_; 
v_unused_3579_ = lean_ctor_get(v___x_3553_, 5);
lean_dec(v_unused_3579_);
v___x_3564_ = v___x_3553_;
v_isShared_3565_ = v_isSharedCheck_3578_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_snapshotTasks_3562_);
lean_inc(v_infoState_3561_);
lean_inc(v_messages_3560_);
lean_inc(v_traceState_3559_);
lean_inc(v_auxDeclNGen_3558_);
lean_inc(v_ngen_3557_);
lean_inc(v_nextMacroScope_3556_);
lean_inc(v_env_3555_);
lean_dec(v___x_3553_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3578_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v_asyncMode_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3571_; 
v_asyncMode_3566_ = lean_ctor_get(v_toEnvExtension_3554_, 2);
lean_inc(v_asyncMode_3566_);
lean_inc(v_decl_3540_);
v___x_3567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3567_, 0, v_decl_3540_);
lean_ctor_set(v___x_3567_, 1, v_snd_3537_);
v___x_3568_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3538_, v_env_3555_, v___x_3567_, v_asyncMode_3566_, v_decl_3540_);
lean_dec(v_asyncMode_3566_);
v___x_3569_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 5, v___x_3569_);
lean_ctor_set(v___x_3564_, 0, v___x_3568_);
v___x_3571_ = v___x_3564_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3568_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v_nextMacroScope_3556_);
lean_ctor_set(v_reuseFailAlloc_3577_, 2, v_ngen_3557_);
lean_ctor_set(v_reuseFailAlloc_3577_, 3, v_auxDeclNGen_3558_);
lean_ctor_set(v_reuseFailAlloc_3577_, 4, v_traceState_3559_);
lean_ctor_set(v_reuseFailAlloc_3577_, 5, v___x_3569_);
lean_ctor_set(v_reuseFailAlloc_3577_, 6, v_messages_3560_);
lean_ctor_set(v_reuseFailAlloc_3577_, 7, v_infoState_3561_);
lean_ctor_set(v_reuseFailAlloc_3577_, 8, v_snapshotTasks_3562_);
v___x_3571_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3575_; 
v___x_3572_ = lean_st_ref_put(v___y_3548_, v___x_3571_);
v___x_3573_ = lean_box(0);
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 0, v___x_3573_);
v___x_3575_ = v___x_3551_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3573_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
}
else
{
lean_dec(v_decl_3540_);
lean_dec_ref(v_a_3538_);
lean_dec(v_snd_3537_);
return v___x_3549_;
}
}
v___jp_3582_:
{
lean_object* v___x_3585_; lean_object* v_env_3586_; lean_object* v___x_3587_; 
v___x_3585_ = lean_st_ref_get(v___y_3584_);
v_env_3586_ = lean_ctor_get(v___x_3585_, 0);
lean_inc_ref(v_env_3586_);
lean_dec(v___x_3585_);
v___x_3587_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3586_, v_decl_3540_);
lean_dec_ref(v_env_3586_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_dec(v_fst_3539_);
v___y_3547_ = v___y_3583_;
v___y_3548_ = v___y_3584_;
goto v___jp_3546_;
}
else
{
lean_object* v___x_3588_; 
lean_dec_ref_known(v___x_3587_, 1);
lean_dec_ref(v_a_3538_);
lean_dec(v_snd_3537_);
lean_dec_ref(v_validate_3536_);
v___x_3588_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3539_, v_decl_3540_, v___y_3583_, v___y_3584_);
return v___x_3588_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3593_, lean_object* v_snd_3594_, lean_object* v_a_3595_, lean_object* v_fst_3596_, lean_object* v_decl_3597_, lean_object* v_stx_3598_, lean_object* v_kind_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
uint8_t v_kind_boxed_3603_; lean_object* v_res_3604_; 
v_kind_boxed_3603_ = lean_unbox(v_kind_3599_);
v_res_3604_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3593_, v_snd_3594_, v_a_3595_, v_fst_3596_, v_decl_3597_, v_stx_3598_, v_kind_boxed_3603_, v___y_3600_, v___y_3601_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3605_, lean_object* v_decl_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3610_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3611_ = l_Lean_MessageData_ofName(v_fst_3605_);
v___x_3612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3610_);
lean_ctor_set(v___x_3612_, 1, v___x_3611_);
v___x_3613_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3612_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v___x_3615_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3614_, v___y_3607_, v___y_3608_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3616_, lean_object* v_decl_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v_res_3621_; 
v_res_3621_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3616_, v_decl_3617_, v___y_3618_, v___y_3619_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec(v_decl_3617_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3622_, lean_object* v_a_3623_, lean_object* v_ref_3624_, uint8_t v_applicationTime_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_){
_start:
{
if (lean_obj_tag(v_a_3626_) == 0)
{
lean_object* v___x_3628_; 
lean_dec(v_ref_3624_);
lean_dec_ref(v_a_3623_);
lean_dec_ref(v_validate_3622_);
v___x_3628_ = l_List_reverse___redArg(v_a_3627_);
return v___x_3628_;
}
else
{
lean_object* v_head_3629_; lean_object* v_snd_3630_; lean_object* v_tail_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3646_; 
v_head_3629_ = lean_ctor_get(v_a_3626_, 0);
lean_inc(v_head_3629_);
v_snd_3630_ = lean_ctor_get(v_head_3629_, 1);
lean_inc(v_snd_3630_);
v_tail_3631_ = lean_ctor_get(v_a_3626_, 1);
v_isSharedCheck_3646_ = !lean_is_exclusive(v_a_3626_);
if (v_isSharedCheck_3646_ == 0)
{
lean_object* v_unused_3647_; 
v_unused_3647_ = lean_ctor_get(v_a_3626_, 0);
lean_dec(v_unused_3647_);
v___x_3633_ = v_a_3626_;
v_isShared_3634_ = v_isSharedCheck_3646_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_tail_3631_);
lean_dec(v_a_3626_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3646_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v_fst_3635_; lean_object* v_fst_3636_; lean_object* v_snd_3637_; lean_object* v___f_3638_; lean_object* v___f_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3643_; 
v_fst_3635_ = lean_ctor_get(v_head_3629_, 0);
lean_inc_n(v_fst_3635_, 3);
lean_dec(v_head_3629_);
v_fst_3636_ = lean_ctor_get(v_snd_3630_, 0);
lean_inc(v_fst_3636_);
v_snd_3637_ = lean_ctor_get(v_snd_3630_, 1);
lean_inc(v_snd_3637_);
lean_dec(v_snd_3630_);
v___f_3638_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3638_, 0, v_fst_3635_);
lean_inc_ref(v_a_3623_);
lean_inc_ref(v_validate_3622_);
v___f_3639_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3639_, 0, v_validate_3622_);
lean_closure_set(v___f_3639_, 1, v_snd_3637_);
lean_closure_set(v___f_3639_, 2, v_a_3623_);
lean_closure_set(v___f_3639_, 3, v_fst_3635_);
lean_inc(v_ref_3624_);
v___x_3640_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3640_, 0, v_ref_3624_);
lean_ctor_set(v___x_3640_, 1, v_fst_3635_);
lean_ctor_set(v___x_3640_, 2, v_fst_3636_);
lean_ctor_set_uint8(v___x_3640_, sizeof(void*)*3, v_applicationTime_3625_);
v___x_3641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3640_);
lean_ctor_set(v___x_3641_, 1, v___f_3639_);
lean_ctor_set(v___x_3641_, 2, v___f_3638_);
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 1, v_a_3627_);
lean_ctor_set(v___x_3633_, 0, v___x_3641_);
v___x_3643_ = v___x_3633_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3641_);
lean_ctor_set(v_reuseFailAlloc_3645_, 1, v_a_3627_);
v___x_3643_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
v_a_3626_ = v_tail_3631_;
v_a_3627_ = v___x_3643_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3648_, lean_object* v_a_3649_, lean_object* v_ref_3650_, lean_object* v_applicationTime_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_){
_start:
{
uint8_t v_applicationTime_boxed_3654_; lean_object* v_res_3655_; 
v_applicationTime_boxed_3654_ = lean_unbox(v_applicationTime_3651_);
v_res_3655_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3648_, v_a_3649_, v_ref_3650_, v_applicationTime_boxed_3654_, v_a_3652_, v_a_3653_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3656_){
_start:
{
if (lean_obj_tag(v_as_3656_) == 0)
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = lean_box(0);
v___x_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3658_);
return v___x_3659_;
}
else
{
lean_object* v_head_3660_; lean_object* v_tail_3661_; lean_object* v___x_3662_; 
v_head_3660_ = lean_ctor_get(v_as_3656_, 0);
lean_inc(v_head_3660_);
v_tail_3661_ = lean_ctor_get(v_as_3656_, 1);
lean_inc(v_tail_3661_);
lean_dec_ref_known(v_as_3656_, 2);
v___x_3662_ = l_Lean_registerBuiltinAttribute(v_head_3660_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_dec_ref_known(v___x_3662_, 1);
v_as_3656_ = v_tail_3661_;
goto _start;
}
else
{
lean_dec(v_tail_3661_);
return v___x_3662_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3664_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3680_, lean_object* v_validate_3681_, uint8_t v_applicationTime_3682_, lean_object* v_ref_3683_){
_start:
{
lean_object* v___f_3685_; lean_object* v___f_3686_; lean_object* v___f_3687_; lean_object* v___f_3688_; lean_object* v___f_3689_; lean_object* v___f_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___f_3685_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3686_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3687_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3688_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3689_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3690_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3691_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3692_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3683_);
v___x_3693_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3693_, 0, v_ref_3683_);
lean_ctor_set(v___x_3693_, 1, v___f_3689_);
lean_ctor_set(v___x_3693_, 2, v___f_3690_);
lean_ctor_set(v___x_3693_, 3, v___f_3688_);
lean_ctor_set(v___x_3693_, 4, v___f_3687_);
lean_ctor_set(v___x_3693_, 5, v___f_3686_);
lean_ctor_set(v___x_3693_, 6, v___x_3691_);
lean_ctor_set(v___x_3693_, 7, v___x_3692_);
v___x_3694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3693_);
lean_ctor_set(v___x_3694_, 1, v___f_3685_);
v___x_3695_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3694_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc_n(v_a_3696_, 2);
lean_dec_ref_known(v___x_3695_, 1);
v___x_3697_ = lean_box(0);
v___x_3698_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3681_, v_a_3696_, v_ref_3683_, v_applicationTime_3682_, v_attrDescrs_3680_, v___x_3697_);
lean_inc(v___x_3698_);
v___x_3699_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3698_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3707_; 
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3707_ == 0)
{
lean_object* v_unused_3708_; 
v_unused_3708_ = lean_ctor_get(v___x_3699_, 0);
lean_dec(v_unused_3708_);
v___x_3701_ = v___x_3699_;
v_isShared_3702_ = v_isSharedCheck_3707_;
goto v_resetjp_3700_;
}
else
{
lean_dec(v___x_3699_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3707_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3703_; lean_object* v___x_3705_; 
v___x_3703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3698_);
lean_ctor_set(v___x_3703_, 1, v_a_3696_);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 0, v___x_3703_);
v___x_3705_ = v___x_3701_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v___x_3703_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_dec(v___x_3698_);
lean_dec(v_a_3696_);
v_a_3709_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3699_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3699_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_dec(v_ref_3683_);
lean_dec_ref(v_validate_3681_);
lean_dec(v_attrDescrs_3680_);
v_a_3717_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3695_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3695_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3725_, lean_object* v_validate_3726_, lean_object* v_applicationTime_3727_, lean_object* v_ref_3728_, lean_object* v_a_3729_){
_start:
{
uint8_t v_applicationTime_boxed_3730_; lean_object* v_res_3731_; 
v_applicationTime_boxed_3730_ = lean_unbox(v_applicationTime_3727_);
v_res_3731_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3725_, v_validate_3726_, v_applicationTime_boxed_3730_, v_ref_3728_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3732_, lean_object* v_attrDescrs_3733_, lean_object* v_validate_3734_, uint8_t v_applicationTime_3735_, lean_object* v_ref_3736_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3733_, v_validate_3734_, v_applicationTime_3735_, v_ref_3736_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3739_, lean_object* v_attrDescrs_3740_, lean_object* v_validate_3741_, lean_object* v_applicationTime_3742_, lean_object* v_ref_3743_, lean_object* v_a_3744_){
_start:
{
uint8_t v_applicationTime_boxed_3745_; lean_object* v_res_3746_; 
v_applicationTime_boxed_3745_ = lean_unbox(v_applicationTime_3742_);
v_res_3746_ = l_Lean_registerEnumAttributes(v_00_u03b1_3739_, v_attrDescrs_3740_, v_validate_3741_, v_applicationTime_boxed_3745_, v_ref_3743_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3747_, lean_object* v_env_3748_, lean_object* v_as_3749_, size_t v_i_3750_, size_t v_stop_3751_, lean_object* v_b_3752_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3748_, v_as_3749_, v_i_3750_, v_stop_3751_, v_b_3752_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3754_, lean_object* v_env_3755_, lean_object* v_as_3756_, lean_object* v_i_3757_, lean_object* v_stop_3758_, lean_object* v_b_3759_){
_start:
{
size_t v_i_boxed_3760_; size_t v_stop_boxed_3761_; lean_object* v_res_3762_; 
v_i_boxed_3760_ = lean_unbox_usize(v_i_3757_);
lean_dec(v_i_3757_);
v_stop_boxed_3761_ = lean_unbox_usize(v_stop_3758_);
lean_dec(v_stop_3758_);
v_res_3762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3754_, v_env_3755_, v_as_3756_, v_i_boxed_3760_, v_stop_boxed_3761_, v_b_3759_);
lean_dec_ref(v_as_3756_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3763_, lean_object* v_newState_3764_, lean_object* v_x_3765_, lean_object* v_x_3766_){
_start:
{
lean_object* v___x_3767_; 
v___x_3767_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3764_, v_x_3765_, v_x_3766_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3768_, lean_object* v_newState_3769_, lean_object* v_x_3770_, lean_object* v_x_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3768_, v_newState_3769_, v_x_3770_, v_x_3771_);
lean_dec(v_newState_3769_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3773_, lean_object* v_validate_3774_, lean_object* v_a_3775_, lean_object* v_ref_3776_, uint8_t v_applicationTime_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_){
_start:
{
lean_object* v___x_3780_; 
v___x_3780_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3774_, v_a_3775_, v_ref_3776_, v_applicationTime_3777_, v_a_3778_, v_a_3779_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3781_, lean_object* v_validate_3782_, lean_object* v_a_3783_, lean_object* v_ref_3784_, lean_object* v_applicationTime_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_){
_start:
{
uint8_t v_applicationTime_boxed_3788_; lean_object* v_res_3789_; 
v_applicationTime_boxed_3788_ = lean_unbox(v_applicationTime_3785_);
v_res_3789_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3781_, v_validate_3782_, v_a_3783_, v_ref_3784_, v_applicationTime_boxed_3788_, v_a_3786_, v_a_3787_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3790_, lean_object* v_attr_3791_, lean_object* v_env_3792_, lean_object* v_decl_3793_){
_start:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3794_ = lean_box(1);
v___x_3795_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3792_, v_decl_3793_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_ext_3796_; lean_object* v_toEnvExtension_3797_; lean_object* v_asyncMode_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
lean_dec(v_inst_3790_);
v_ext_3796_ = lean_ctor_get(v_attr_3791_, 1);
lean_inc_ref(v_ext_3796_);
lean_dec_ref(v_attr_3791_);
v_toEnvExtension_3797_ = lean_ctor_get(v_ext_3796_, 0);
v_asyncMode_3798_ = lean_ctor_get(v_toEnvExtension_3797_, 2);
lean_inc(v_asyncMode_3798_);
lean_inc(v_decl_3793_);
v___x_3799_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3794_, v_ext_3796_, v_env_3792_, v_asyncMode_3798_, v_decl_3793_);
lean_dec(v_asyncMode_3798_);
lean_dec_ref(v_ext_3796_);
v___x_3800_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3799_, v_decl_3793_);
lean_dec(v_decl_3793_);
lean_dec(v___x_3799_);
return v___x_3800_;
}
else
{
lean_object* v_val_3801_; lean_object* v_ext_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3832_; 
v_val_3801_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_val_3801_);
lean_dec_ref_known(v___x_3795_, 1);
v_ext_3802_ = lean_ctor_get(v_attr_3791_, 1);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_attr_3791_);
if (v_isSharedCheck_3832_ == 0)
{
lean_object* v_unused_3833_; 
v_unused_3833_ = lean_ctor_get(v_attr_3791_, 0);
lean_dec(v_unused_3833_);
v___x_3804_ = v_attr_3791_;
v_isShared_3805_ = v_isSharedCheck_3832_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_ext_3802_);
lean_dec(v_attr_3791_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3832_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
uint8_t v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; uint8_t v___x_3810_; 
v___x_3806_ = 0;
v___x_3807_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3794_, v_ext_3802_, v_env_3792_, v_val_3801_, v___x_3806_);
lean_dec(v_val_3801_);
lean_dec_ref(v_env_3792_);
lean_dec_ref(v_ext_3802_);
v___x_3808_ = lean_unsigned_to_nat(0u);
v___x_3809_ = lean_array_get_size(v___x_3807_);
v___x_3810_ = lean_nat_dec_lt(v___x_3808_, v___x_3809_);
if (v___x_3810_ == 0)
{
lean_object* v___x_3811_; 
lean_dec_ref(v___x_3807_);
lean_del_object(v___x_3804_);
lean_dec(v_decl_3793_);
lean_dec(v_inst_3790_);
v___x_3811_ = lean_box(0);
return v___x_3811_;
}
else
{
lean_object* v___x_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; 
v___x_3812_ = lean_unsigned_to_nat(1u);
v___x_3813_ = lean_nat_sub(v___x_3809_, v___x_3812_);
v___x_3814_ = lean_nat_dec_le(v___x_3808_, v___x_3813_);
if (v___x_3814_ == 0)
{
lean_object* v___x_3815_; 
lean_dec(v___x_3813_);
lean_dec_ref(v___x_3807_);
lean_del_object(v___x_3804_);
lean_dec(v_decl_3793_);
lean_dec(v_inst_3790_);
v___x_3815_ = lean_box(0);
return v___x_3815_;
}
else
{
lean_object* v___f_3816_; lean_object* v___x_3818_; 
v___f_3816_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 1, v_inst_3790_);
lean_ctor_set(v___x_3804_, 0, v_decl_3793_);
v___x_3818_ = v___x_3804_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_decl_3793_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v_inst_3790_);
v___x_3818_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; 
v___x_3819_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3820_ = l_Array_binSearchAux___redArg(v___f_3816_, v___x_3819_, v___x_3807_, v___x_3818_, v___x_3808_, v___x_3813_);
lean_dec_ref(v___x_3807_);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v___x_3821_; 
v___x_3821_ = lean_box(0);
return v___x_3821_;
}
else
{
lean_object* v_val_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3830_; 
v_val_3822_ = lean_ctor_get(v___x_3820_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3820_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3824_ = v___x_3820_;
v_isShared_3825_ = v_isSharedCheck_3830_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_val_3822_);
lean_dec(v___x_3820_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3830_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v_snd_3826_; lean_object* v___x_3828_; 
v_snd_3826_ = lean_ctor_get(v_val_3822_, 1);
lean_inc(v_snd_3826_);
lean_dec(v_val_3822_);
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v_snd_3826_);
v___x_3828_ = v___x_3824_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_snd_3826_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3834_, lean_object* v_inst_3835_, lean_object* v_attr_3836_, lean_object* v_env_3837_, lean_object* v_decl_3838_){
_start:
{
lean_object* v___x_3839_; 
v___x_3839_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3835_, v_attr_3836_, v_env_3837_, v_decl_3838_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3848_, lean_object* v_env_3849_, lean_object* v_decl_3850_, lean_object* v_val_3851_){
_start:
{
lean_object* v_ext_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3916_; 
v_ext_3852_ = lean_ctor_get(v_attrs_3848_, 1);
v_isSharedCheck_3916_ = !lean_is_exclusive(v_attrs_3848_);
if (v_isSharedCheck_3916_ == 0)
{
lean_object* v_unused_3917_; 
v_unused_3917_ = lean_ctor_get(v_attrs_3848_, 0);
lean_dec(v_unused_3917_);
v___x_3854_ = v_attrs_3848_;
v_isShared_3855_ = v_isSharedCheck_3916_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_ext_3852_);
lean_dec(v_attrs_3848_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3916_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v_toEnvExtension_3856_; lean_object* v_name_3857_; lean_object* v___x_3858_; uint8_t v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v_pfx_3867_; lean_object* v___x_3868_; 
v_toEnvExtension_3856_ = lean_ctor_get(v_ext_3852_, 0);
v_name_3857_ = lean_ctor_get(v_ext_3852_, 1);
v___x_3858_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3859_ = 1;
lean_inc(v_name_3857_);
v___x_3860_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3857_, v___x_3859_);
v___x_3861_ = lean_string_append(v___x_3858_, v___x_3860_);
lean_dec_ref(v___x_3860_);
v___x_3862_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3863_ = lean_string_append(v___x_3861_, v___x_3862_);
lean_inc(v_decl_3850_);
v___x_3864_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3850_, v___x_3859_);
v___x_3865_ = lean_string_append(v___x_3863_, v___x_3864_);
lean_dec_ref(v___x_3864_);
v___x_3866_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3867_ = lean_string_append(v___x_3865_, v___x_3866_);
v___x_3868_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3849_, v_decl_3850_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_asyncMode_3869_; uint8_t v___x_3876_; 
v_asyncMode_3869_ = lean_ctor_get(v_toEnvExtension_3856_, 2);
lean_inc(v_asyncMode_3869_);
lean_inc(v_decl_3850_);
lean_inc_ref(v_env_3849_);
v___x_3876_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3849_, v_decl_3850_, v_asyncMode_3869_);
if (v___x_3876_ == 0)
{
lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___y_3880_; lean_object* v___x_3884_; 
lean_dec(v_asyncMode_3869_);
lean_del_object(v___x_3854_);
lean_dec_ref(v_ext_3852_);
lean_dec(v_val_3851_);
lean_dec(v_decl_3850_);
v___x_3877_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3878_ = lean_string_append(v_pfx_3867_, v___x_3877_);
v___x_3884_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3849_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v___x_3885_; 
v___x_3885_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3880_ = v___x_3885_;
goto v___jp_3879_;
}
else
{
lean_object* v_val_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v_val_3886_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_val_3886_);
lean_dec_ref_known(v___x_3884_, 1);
v___x_3887_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3888_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3886_, v___x_3859_);
v___x_3889_ = l_addParenHeuristic(v___x_3888_);
v___x_3890_ = lean_string_append(v___x_3887_, v___x_3889_);
lean_dec_ref(v___x_3889_);
v___x_3891_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3892_ = lean_string_append(v___x_3890_, v___x_3891_);
v___y_3880_ = v___x_3892_;
goto v___jp_3879_;
}
v___jp_3879_:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3881_ = lean_string_append(v___x_3878_, v___y_3880_);
lean_dec_ref(v___y_3880_);
v___x_3882_ = lean_string_append(v___x_3881_, v___x_3866_);
v___x_3883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
return v___x_3883_;
}
}
else
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3893_ = lean_box(1);
lean_inc(v_decl_3850_);
lean_inc_ref(v_env_3849_);
v___x_3894_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3893_, v_ext_3852_, v_env_3849_, v_asyncMode_3869_, v_decl_3850_);
v___x_3895_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3894_, v_decl_3850_);
lean_dec(v___x_3894_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_dec_ref(v_pfx_3867_);
goto v___jp_3870_;
}
else
{
lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3904_; 
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3904_ == 0)
{
lean_object* v_unused_3905_; 
v_unused_3905_ = lean_ctor_get(v___x_3895_, 0);
lean_dec(v_unused_3905_);
v___x_3897_ = v___x_3895_;
v_isShared_3898_ = v_isSharedCheck_3904_;
goto v_resetjp_3896_;
}
else
{
lean_dec(v___x_3895_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3904_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
if (v___x_3876_ == 0)
{
lean_del_object(v___x_3897_);
lean_dec_ref(v_pfx_3867_);
goto v___jp_3870_;
}
else
{
lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3902_; 
lean_dec(v_asyncMode_3869_);
lean_del_object(v___x_3854_);
lean_dec_ref(v_ext_3852_);
lean_dec(v_val_3851_);
lean_dec(v_decl_3850_);
lean_dec_ref(v_env_3849_);
v___x_3899_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3900_ = lean_string_append(v_pfx_3867_, v___x_3899_);
if (v_isShared_3898_ == 0)
{
lean_ctor_set_tag(v___x_3897_, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3900_);
v___x_3902_ = v___x_3897_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3900_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
}
}
v___jp_3870_:
{
lean_object* v___x_3872_; 
lean_inc(v_decl_3850_);
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 1, v_val_3851_);
lean_ctor_set(v___x_3854_, 0, v_decl_3850_);
v___x_3872_ = v___x_3854_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_decl_3850_);
lean_ctor_set(v_reuseFailAlloc_3875_, 1, v_val_3851_);
v___x_3872_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3873_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3852_, v_env_3849_, v___x_3872_, v_asyncMode_3869_, v_decl_3850_);
lean_dec(v_asyncMode_3869_);
v___x_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
return v___x_3874_;
}
}
}
else
{
lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3914_; 
lean_del_object(v___x_3854_);
lean_dec_ref(v_ext_3852_);
lean_dec(v_val_3851_);
lean_dec(v_decl_3850_);
lean_dec_ref(v_env_3849_);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3914_ == 0)
{
lean_object* v_unused_3915_; 
v_unused_3915_ = lean_ctor_get(v___x_3868_, 0);
lean_dec(v_unused_3915_);
v___x_3907_ = v___x_3868_;
v_isShared_3908_ = v_isSharedCheck_3914_;
goto v_resetjp_3906_;
}
else
{
lean_dec(v___x_3868_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3914_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3912_; 
v___x_3909_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3910_ = lean_string_append(v_pfx_3867_, v___x_3909_);
if (v_isShared_3908_ == 0)
{
lean_ctor_set_tag(v___x_3907_, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3910_);
v___x_3912_ = v___x_3907_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3910_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3918_, lean_object* v_attrs_3919_, lean_object* v_env_3920_, lean_object* v_decl_3921_, lean_object* v_val_3922_){
_start:
{
lean_object* v___x_3923_; 
v___x_3923_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3919_, v_env_3920_, v_decl_3921_, v_val_3922_);
return v___x_3923_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_3924_; lean_object* v___x_3925_; 
v_cellCount_3924_ = lean_unsigned_to_nat(16u);
v___x_3925_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3924_);
return v___x_3925_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3926_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_);
v___x_3927_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3928_ = lean_unsigned_to_nat(0u);
v___x_3929_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
lean_ctor_set(v___x_3929_, 1, v___x_3927_);
lean_ctor_set(v___x_3929_, 2, v___x_3926_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3931_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_);
v___x_3932_ = lean_st_mk_ref(v___x_3931_);
v___x_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3938_, lean_object* v_builder_3939_){
_start:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; uint8_t v___x_3943_; 
v___x_3941_ = l_Lean_attributeImplBuilderTableRef;
v___x_3942_ = lean_st_ref_get(v___x_3941_);
v___x_3943_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3942_, v_builderId_3938_);
lean_dec(v___x_3942_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3944_; lean_object* v___y_3946_; lean_object* v___y_3950_; lean_object* v_i_3951_; lean_object* v___y_3957_; lean_object* v___y_3967_; lean_object* v_i_3968_; lean_object* v___x_3983_; 
v___x_3944_ = lean_st_ref_take(v___x_3941_);
v___x_3983_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3944_, v_builderId_3938_);
switch(lean_obj_tag(v___x_3983_))
{
case 0:
{
lean_object* v_index_3984_; lean_object* v_size_3985_; lean_object* v___x_3986_; 
v_index_3984_ = lean_ctor_get(v___x_3983_, 0);
lean_inc(v_index_3984_);
lean_dec_ref_known(v___x_3983_, 3);
v_size_3985_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_size_3985_);
v___x_3986_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3944_, v_size_3985_, v_index_3984_, v_builderId_3938_, v_builder_3939_);
lean_dec(v_index_3984_);
v___y_3946_ = v___x_3986_;
goto v___jp_3945_;
}
case 1:
{
lean_object* v_index_3987_; lean_object* v_size_3988_; lean_object* v_keyArray_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; uint8_t v___x_3993_; 
v_index_3987_ = lean_ctor_get(v___x_3983_, 0);
lean_inc(v_index_3987_);
lean_dec_ref_known(v___x_3983_, 1);
v_size_3988_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_size_3988_);
v_keyArray_3989_ = lean_ctor_get(v___x_3944_, 1);
lean_inc_ref(v_keyArray_3989_);
v___x_3990_ = lean_unsigned_to_nat(1u);
v___x_3991_ = lean_nat_add(v_size_3988_, v___x_3990_);
lean_dec(v_size_3988_);
v___x_3992_ = lean_array_get_size(v_keyArray_3989_);
lean_dec_ref(v_keyArray_3989_);
v___x_3993_ = lean_nat_dec_lt(v___x_3991_, v___x_3992_);
if (v___x_3993_ == 0)
{
lean_dec(v___x_3991_);
lean_dec(v_index_3987_);
goto v___jp_3973_;
}
else
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; uint8_t v___x_3998_; 
v___x_3994_ = lean_unsigned_to_nat(4u);
v___x_3995_ = lean_nat_mul(v___x_3991_, v___x_3994_);
v___x_3996_ = lean_unsigned_to_nat(3u);
v___x_3997_ = lean_nat_mul(v___x_3992_, v___x_3996_);
v___x_3998_ = lean_nat_dec_le(v___x_3995_, v___x_3997_);
lean_dec(v___x_3997_);
lean_dec(v___x_3995_);
if (v___x_3998_ == 0)
{
lean_dec(v___x_3991_);
lean_dec(v_index_3987_);
goto v___jp_3973_;
}
else
{
lean_object* v___x_3999_; 
v___x_3999_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3944_, v___x_3991_, v_index_3987_, v_builderId_3938_, v_builder_3939_);
lean_dec(v_index_3987_);
v___y_3946_ = v___x_3999_;
goto v___jp_3945_;
}
}
}
default: 
{
lean_object* v_size_4000_; lean_object* v_keyArray_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; uint8_t v___x_4005_; 
v_size_4000_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_size_4000_);
v_keyArray_4001_ = lean_ctor_get(v___x_3944_, 1);
lean_inc_ref(v_keyArray_4001_);
v___x_4002_ = lean_unsigned_to_nat(1u);
v___x_4003_ = lean_nat_add(v_size_4000_, v___x_4002_);
lean_dec(v_size_4000_);
v___x_4004_ = lean_array_get_size(v_keyArray_4001_);
lean_dec_ref(v_keyArray_4001_);
v___x_4005_ = lean_nat_dec_lt(v___x_4003_, v___x_4004_);
if (v___x_4005_ == 0)
{
lean_object* v___x_4006_; 
lean_dec(v___x_4003_);
v___x_4006_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg(v___x_3944_);
lean_dec(v___x_3944_);
v___y_3957_ = v___x_4006_;
goto v___jp_3956_;
}
else
{
lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; uint8_t v___x_4011_; 
v___x_4007_ = lean_unsigned_to_nat(4u);
v___x_4008_ = lean_nat_mul(v___x_4003_, v___x_4007_);
lean_dec(v___x_4003_);
v___x_4009_ = lean_unsigned_to_nat(3u);
v___x_4010_ = lean_nat_mul(v___x_4004_, v___x_4009_);
v___x_4011_ = lean_nat_dec_le(v___x_4008_, v___x_4010_);
lean_dec(v___x_4010_);
lean_dec(v___x_4008_);
if (v___x_4011_ == 0)
{
lean_object* v___x_4012_; 
v___x_4012_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg(v___x_3944_);
lean_dec(v___x_3944_);
v___y_3957_ = v___x_4012_;
goto v___jp_3956_;
}
else
{
v___y_3957_ = v___x_3944_;
goto v___jp_3956_;
}
}
}
}
v___jp_3945_:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3947_ = lean_st_ref_put(v___x_3941_, v___y_3946_);
v___x_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3947_);
return v___x_3948_;
}
v___jp_3949_:
{
lean_object* v_size_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v_size_3952_ = lean_ctor_get(v___y_3950_, 0);
v___x_3953_ = lean_unsigned_to_nat(1u);
v___x_3954_ = lean_nat_add(v_size_3952_, v___x_3953_);
v___x_3955_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3950_, v___x_3954_, v_i_3951_, v_builderId_3938_, v_builder_3939_);
lean_dec(v_i_3951_);
v___y_3946_ = v___x_3955_;
goto v___jp_3945_;
}
v___jp_3956_:
{
lean_object* v___x_3958_; 
v___x_3958_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___y_3957_, v_builderId_3938_);
switch(lean_obj_tag(v___x_3958_))
{
case 0:
{
lean_object* v_index_3959_; lean_object* v_size_3960_; lean_object* v___x_3961_; 
v_index_3959_ = lean_ctor_get(v___x_3958_, 0);
lean_inc(v_index_3959_);
lean_dec_ref_known(v___x_3958_, 3);
v_size_3960_ = lean_ctor_get(v___y_3957_, 0);
lean_inc(v_size_3960_);
v___x_3961_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3957_, v_size_3960_, v_index_3959_, v_builderId_3938_, v_builder_3939_);
lean_dec(v_index_3959_);
v___y_3946_ = v___x_3961_;
goto v___jp_3945_;
}
case 1:
{
lean_object* v_index_3962_; 
v_index_3962_ = lean_ctor_get(v___x_3958_, 0);
lean_inc(v_index_3962_);
lean_dec_ref_known(v___x_3958_, 1);
v___y_3950_ = v___y_3957_;
v_i_3951_ = v_index_3962_;
goto v___jp_3949_;
}
default: 
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3963_ = lean_unsigned_to_nat(0u);
v___x_3964_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_3957_, v___x_3963_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_index_3965_; 
v_index_3965_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_index_3965_);
lean_dec_ref_known(v___x_3964_, 1);
v___y_3950_ = v___y_3957_;
v_i_3951_ = v_index_3965_;
goto v___jp_3949_;
}
else
{
lean_dec_ref(v_builder_3939_);
lean_dec(v_builderId_3938_);
v___y_3946_ = v___y_3957_;
goto v___jp_3945_;
}
}
}
}
v___jp_3966_:
{
lean_object* v_size_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v_size_3969_ = lean_ctor_get(v___y_3967_, 0);
v___x_3970_ = lean_unsigned_to_nat(1u);
v___x_3971_ = lean_nat_add(v_size_3969_, v___x_3970_);
v___x_3972_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3967_, v___x_3971_, v_i_3968_, v_builderId_3938_, v_builder_3939_);
lean_dec(v_i_3968_);
v___y_3946_ = v___x_3972_;
goto v___jp_3945_;
}
v___jp_3973_:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg(v___x_3944_);
lean_dec(v___x_3944_);
v___x_3975_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3974_, v_builderId_3938_);
switch(lean_obj_tag(v___x_3975_))
{
case 0:
{
lean_object* v_index_3976_; lean_object* v_size_3977_; lean_object* v___x_3978_; 
v_index_3976_ = lean_ctor_get(v___x_3975_, 0);
lean_inc(v_index_3976_);
lean_dec_ref_known(v___x_3975_, 3);
v_size_3977_ = lean_ctor_get(v___x_3974_, 0);
lean_inc(v_size_3977_);
v___x_3978_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3974_, v_size_3977_, v_index_3976_, v_builderId_3938_, v_builder_3939_);
lean_dec(v_index_3976_);
v___y_3946_ = v___x_3978_;
goto v___jp_3945_;
}
case 1:
{
lean_object* v_index_3979_; 
v_index_3979_ = lean_ctor_get(v___x_3975_, 0);
lean_inc(v_index_3979_);
lean_dec_ref_known(v___x_3975_, 1);
v___y_3967_ = v___x_3974_;
v_i_3968_ = v_index_3979_;
goto v___jp_3966_;
}
default: 
{
lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3980_ = lean_unsigned_to_nat(0u);
v___x_3981_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3974_, v___x_3980_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_index_3982_; 
v_index_3982_ = lean_ctor_get(v___x_3981_, 0);
lean_inc(v_index_3982_);
lean_dec_ref_known(v___x_3981_, 1);
v___y_3967_ = v___x_3974_;
v_i_3968_ = v_index_3982_;
goto v___jp_3966_;
}
else
{
lean_dec_ref(v_builder_3939_);
lean_dec(v_builderId_3938_);
v___y_3946_ = v___x_3974_;
goto v___jp_3945_;
}
}
}
}
}
else
{
lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
lean_dec_ref(v_builder_3939_);
v___x_4013_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_4014_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3938_, v___x_3943_);
v___x_4015_ = lean_string_append(v___x_4013_, v___x_4014_);
lean_dec_ref(v___x_4014_);
v___x_4016_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_4017_ = lean_string_append(v___x_4015_, v___x_4016_);
v___x_4018_ = lean_mk_io_user_error(v___x_4017_);
v___x_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4018_);
return v___x_4019_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_4020_, lean_object* v_builder_4021_, lean_object* v_a_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l_Lean_registerAttributeImplBuilder(v_builderId_4020_, v_builder_4021_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_4024_){
_start:
{
if (lean_obj_tag(v_e_4024_) == 0)
{
lean_object* v_a_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4034_; 
v_a_4026_ = lean_ctor_get(v_e_4024_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v_e_4024_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4028_ = v_e_4024_;
v_isShared_4029_ = v_isSharedCheck_4034_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_a_4026_);
lean_dec(v_e_4024_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4034_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4030_; lean_object* v___x_4032_; 
v___x_4030_ = lean_mk_io_user_error(v_a_4026_);
if (v_isShared_4029_ == 0)
{
lean_ctor_set_tag(v___x_4028_, 1);
lean_ctor_set(v___x_4028_, 0, v___x_4030_);
v___x_4032_ = v___x_4028_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4030_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
else
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4042_; 
v_a_4035_ = lean_ctor_get(v_e_4024_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v_e_4024_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4037_ = v_e_4024_;
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v_e_4024_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
lean_ctor_set_tag(v___x_4037_, 0);
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4035_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_4043_, lean_object* v_a_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_4043_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_4046_, lean_object* v_e_4047_){
_start:
{
lean_object* v___x_4049_; 
v___x_4049_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_4047_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_4050_, lean_object* v_e_4051_, lean_object* v_a_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_4050_, v_e_4051_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_4054_, lean_object* v_a_4055_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_m_4054_, v_a_4055_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v_value_4057_; lean_object* v___x_4058_; 
v_value_4057_ = lean_ctor_get(v___x_4056_, 2);
lean_inc(v_value_4057_);
lean_dec_ref_known(v___x_4056_, 3);
v___x_4058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4058_, 0, v_value_4057_);
return v___x_4058_;
}
else
{
lean_object* v___x_4059_; 
v___x_4059_ = lean_box(0);
return v___x_4059_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_4060_, lean_object* v_a_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_4060_, v_a_4061_);
lean_dec(v_a_4061_);
lean_dec_ref(v_m_4060_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_4064_){
_start:
{
lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v_builderId_4068_; lean_object* v_ref_4069_; lean_object* v_args_4070_; lean_object* v___x_4071_; 
v___x_4066_ = l_Lean_attributeImplBuilderTableRef;
v___x_4067_ = lean_st_ref_get(v___x_4066_);
v_builderId_4068_ = lean_ctor_get(v_e_4064_, 0);
lean_inc(v_builderId_4068_);
v_ref_4069_ = lean_ctor_get(v_e_4064_, 1);
lean_inc(v_ref_4069_);
v_args_4070_ = lean_ctor_get(v_e_4064_, 2);
lean_inc(v_args_4070_);
lean_dec_ref(v_e_4064_);
v___x_4071_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4067_, v_builderId_4068_);
lean_dec(v___x_4067_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v___x_4072_; uint8_t v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
lean_dec(v_args_4070_);
lean_dec(v_ref_4069_);
v___x_4072_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_4073_ = 1;
v___x_4074_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_4068_, v___x_4073_);
v___x_4075_ = lean_string_append(v___x_4072_, v___x_4074_);
lean_dec_ref(v___x_4074_);
v___x_4076_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4077_ = lean_string_append(v___x_4075_, v___x_4076_);
v___x_4078_ = lean_mk_io_user_error(v___x_4077_);
v___x_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
return v___x_4079_;
}
else
{
lean_object* v_val_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
lean_dec(v_builderId_4068_);
v_val_4080_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_val_4080_);
lean_dec_ref_known(v___x_4071_, 1);
v___x_4081_ = lean_apply_2(v_val_4080_, v_ref_4069_, v_args_4070_);
v___x_4082_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_4081_);
return v___x_4082_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_4083_, lean_object* v_a_4084_){
_start:
{
lean_object* v_res_4085_; 
v_res_4085_ = l_Lean_mkAttributeImplOfEntry(v_e_4083_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_4086_, lean_object* v_m_4087_, lean_object* v_a_4088_){
_start:
{
lean_object* v___x_4089_; 
v___x_4089_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_4087_, v_a_4088_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_4090_, lean_object* v_m_4091_, lean_object* v_a_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_4090_, v_m_4091_, v_a_4092_);
lean_dec(v_a_4092_);
lean_dec_ref(v_m_4091_);
return v_res_4093_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4094_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_4095_ = lean_box(0);
v___x_4096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4095_);
lean_ctor_set(v___x_4096_, 1, v___x_4094_);
return v___x_4096_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_4097_; 
v___x_4097_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_4097_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_4098_; 
v___x_4098_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___x_4100_ = l_Lean_attributeMapRef;
v___x_4101_ = lean_st_ref_get(v___x_4100_);
v___x_4102_ = lean_box(0);
v___x_4103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4102_);
lean_ctor_set(v___x_4103_, 1, v___x_4101_);
v___x_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4103_);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_4105_){
_start:
{
lean_object* v_res_4106_; 
v_res_4106_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_4112_, lean_object* v_opts_4113_, lean_object* v_declName_4114_){
_start:
{
uint8_t v___x_4117_; lean_object* v___x_4118_; 
v___x_4117_ = 0;
lean_inc(v_declName_4114_);
lean_inc_ref(v_env_4112_);
v___x_4118_ = l_Lean_Environment_find_x3f(v_env_4112_, v_declName_4114_, v___x_4117_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v___x_4119_; uint8_t v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
lean_dec_ref(v_env_4112_);
v___x_4119_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_4120_ = 1;
v___x_4121_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_4114_, v___x_4120_);
v___x_4122_ = lean_string_append(v___x_4119_, v___x_4121_);
lean_dec_ref(v___x_4121_);
v___x_4123_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4124_ = lean_string_append(v___x_4122_, v___x_4123_);
v___x_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4124_);
return v___x_4125_;
}
else
{
lean_object* v_val_4126_; lean_object* v___x_4127_; 
v_val_4126_ = lean_ctor_get(v___x_4118_, 0);
lean_inc(v_val_4126_);
lean_dec_ref_known(v___x_4118_, 1);
v___x_4127_ = l_Lean_ConstantInfo_type(v_val_4126_);
lean_dec(v_val_4126_);
if (lean_obj_tag(v___x_4127_) == 4)
{
lean_object* v_declName_4128_; 
v_declName_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_declName_4128_);
lean_dec_ref_known(v___x_4127_, 2);
if (lean_obj_tag(v_declName_4128_) == 1)
{
lean_object* v_pre_4129_; 
v_pre_4129_ = lean_ctor_get(v_declName_4128_, 0);
lean_inc(v_pre_4129_);
if (lean_obj_tag(v_pre_4129_) == 1)
{
lean_object* v_pre_4130_; 
v_pre_4130_ = lean_ctor_get(v_pre_4129_, 0);
if (lean_obj_tag(v_pre_4130_) == 0)
{
lean_object* v_str_4131_; lean_object* v_str_4132_; lean_object* v___x_4133_; uint8_t v___x_4134_; 
v_str_4131_ = lean_ctor_get(v_declName_4128_, 1);
lean_inc_ref(v_str_4131_);
lean_dec_ref_known(v_declName_4128_, 2);
v_str_4132_ = lean_ctor_get(v_pre_4129_, 1);
lean_inc_ref(v_str_4132_);
lean_dec_ref_known(v_pre_4129_, 2);
v___x_4133_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_4134_ = lean_string_dec_eq(v_str_4132_, v___x_4133_);
lean_dec_ref(v_str_4132_);
if (v___x_4134_ == 0)
{
lean_dec_ref(v_str_4131_);
lean_dec(v_declName_4114_);
lean_dec_ref(v_env_4112_);
goto v___jp_4115_;
}
else
{
lean_object* v___x_4135_; uint8_t v___x_4136_; 
v___x_4135_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_4136_ = lean_string_dec_eq(v_str_4131_, v___x_4135_);
lean_dec_ref(v_str_4131_);
if (v___x_4136_ == 0)
{
lean_dec(v_declName_4114_);
lean_dec_ref(v_env_4112_);
goto v___jp_4115_;
}
else
{
lean_object* v___x_4137_; 
v___x_4137_ = l_Lean_Environment_evalConst___redArg(v_env_4112_, v_opts_4113_, v_declName_4114_, v___x_4136_);
lean_dec(v_declName_4114_);
lean_dec_ref(v_env_4112_);
return v___x_4137_;
}
}
}
else
{
lean_dec_ref_known(v_pre_4129_, 2);
lean_dec_ref_known(v_declName_4128_, 2);
lean_dec(v_declName_4114_);
lean_dec_ref(v_env_4112_);
goto v___jp_4115_;
}
}
else
{
lean_dec_ref_known(v_declName_4128_, 2);
lean_dec(v_pre_4129_);
lean_dec(v_declName_4114_);
lean_dec_ref(v_env_4112_);
goto v___jp_4115_;
}
}
else
{
lean_dec(v_declName_4128_);
lean_dec(v_declName_4114_);
lean_dec_ref(v_env_4112_);
goto v___jp_4115_;
}
}
else
{
lean_dec_ref(v___x_4127_);
lean_dec(v_declName_4114_);
lean_dec_ref(v_env_4112_);
goto v___jp_4115_;
}
}
v___jp_4115_:
{
lean_object* v___x_4116_; 
v___x_4116_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_4116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_4138_, lean_object* v_opts_4139_, lean_object* v_declName_4140_){
_start:
{
lean_object* v_res_4141_; 
v_res_4141_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_4138_, v_opts_4139_, v_declName_4140_);
lean_dec_ref(v_opts_4139_);
return v_res_4141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_4142_, size_t v_i_4143_, size_t v_stop_4144_, lean_object* v_b_4145_){
_start:
{
uint8_t v___x_4147_; 
v___x_4147_ = lean_usize_dec_eq(v_i_4143_, v_stop_4144_);
if (v___x_4147_ == 0)
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4148_ = lean_array_uget_borrowed(v_as_4142_, v_i_4143_);
lean_inc(v___x_4148_);
v___x_4149_ = l_Lean_mkAttributeImplOfEntry(v___x_4148_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4150_; lean_object* v___y_4152_; lean_object* v_toAttributeImplCore_4156_; lean_object* v_name_4157_; lean_object* v___y_4159_; lean_object* v_i_4160_; lean_object* v___y_4166_; lean_object* v___y_4176_; lean_object* v_i_4177_; lean_object* v___x_4192_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_a_4150_);
lean_dec_ref_known(v___x_4149_, 1);
v_toAttributeImplCore_4156_ = lean_ctor_get(v_a_4150_, 0);
v_name_4157_ = lean_ctor_get(v_toAttributeImplCore_4156_, 1);
lean_inc(v_name_4157_);
v___x_4192_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_4145_, v_name_4157_);
switch(lean_obj_tag(v___x_4192_))
{
case 0:
{
lean_object* v_index_4193_; lean_object* v_size_4194_; lean_object* v___x_4195_; 
v_index_4193_ = lean_ctor_get(v___x_4192_, 0);
lean_inc(v_index_4193_);
lean_dec_ref_known(v___x_4192_, 3);
v_size_4194_ = lean_ctor_get(v_b_4145_, 0);
lean_inc(v_size_4194_);
v___x_4195_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_4145_, v_size_4194_, v_index_4193_, v_name_4157_, v_a_4150_);
lean_dec(v_index_4193_);
v___y_4152_ = v___x_4195_;
goto v___jp_4151_;
}
case 1:
{
lean_object* v_index_4196_; lean_object* v_size_4197_; lean_object* v_keyArray_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; uint8_t v___x_4202_; 
v_index_4196_ = lean_ctor_get(v___x_4192_, 0);
lean_inc(v_index_4196_);
lean_dec_ref_known(v___x_4192_, 1);
v_size_4197_ = lean_ctor_get(v_b_4145_, 0);
v_keyArray_4198_ = lean_ctor_get(v_b_4145_, 1);
v___x_4199_ = lean_unsigned_to_nat(1u);
v___x_4200_ = lean_nat_add(v_size_4197_, v___x_4199_);
v___x_4201_ = lean_array_get_size(v_keyArray_4198_);
v___x_4202_ = lean_nat_dec_lt(v___x_4200_, v___x_4201_);
if (v___x_4202_ == 0)
{
lean_dec(v___x_4200_);
lean_dec(v_index_4196_);
goto v___jp_4182_;
}
else
{
lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; uint8_t v___x_4207_; 
v___x_4203_ = lean_unsigned_to_nat(4u);
v___x_4204_ = lean_nat_mul(v___x_4200_, v___x_4203_);
v___x_4205_ = lean_unsigned_to_nat(3u);
v___x_4206_ = lean_nat_mul(v___x_4201_, v___x_4205_);
v___x_4207_ = lean_nat_dec_le(v___x_4204_, v___x_4206_);
lean_dec(v___x_4206_);
lean_dec(v___x_4204_);
if (v___x_4207_ == 0)
{
lean_dec(v___x_4200_);
lean_dec(v_index_4196_);
goto v___jp_4182_;
}
else
{
lean_object* v___x_4208_; 
v___x_4208_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_4145_, v___x_4200_, v_index_4196_, v_name_4157_, v_a_4150_);
lean_dec(v_index_4196_);
v___y_4152_ = v___x_4208_;
goto v___jp_4151_;
}
}
}
default: 
{
lean_object* v_size_4209_; lean_object* v_keyArray_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; uint8_t v___x_4214_; 
v_size_4209_ = lean_ctor_get(v_b_4145_, 0);
v_keyArray_4210_ = lean_ctor_get(v_b_4145_, 1);
v___x_4211_ = lean_unsigned_to_nat(1u);
v___x_4212_ = lean_nat_add(v_size_4209_, v___x_4211_);
v___x_4213_ = lean_array_get_size(v_keyArray_4210_);
v___x_4214_ = lean_nat_dec_lt(v___x_4212_, v___x_4213_);
if (v___x_4214_ == 0)
{
lean_object* v___x_4215_; 
lean_dec(v___x_4212_);
v___x_4215_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg(v_b_4145_);
lean_dec_ref(v_b_4145_);
v___y_4166_ = v___x_4215_;
goto v___jp_4165_;
}
else
{
lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; uint8_t v___x_4220_; 
v___x_4216_ = lean_unsigned_to_nat(4u);
v___x_4217_ = lean_nat_mul(v___x_4212_, v___x_4216_);
lean_dec(v___x_4212_);
v___x_4218_ = lean_unsigned_to_nat(3u);
v___x_4219_ = lean_nat_mul(v___x_4213_, v___x_4218_);
v___x_4220_ = lean_nat_dec_le(v___x_4217_, v___x_4219_);
lean_dec(v___x_4219_);
lean_dec(v___x_4217_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4221_; 
v___x_4221_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg(v_b_4145_);
lean_dec_ref(v_b_4145_);
v___y_4166_ = v___x_4221_;
goto v___jp_4165_;
}
else
{
v___y_4166_ = v_b_4145_;
goto v___jp_4165_;
}
}
}
}
v___jp_4151_:
{
size_t v___x_4153_; size_t v___x_4154_; 
v___x_4153_ = ((size_t)1ULL);
v___x_4154_ = lean_usize_add(v_i_4143_, v___x_4153_);
v_i_4143_ = v___x_4154_;
v_b_4145_ = v___y_4152_;
goto _start;
}
v___jp_4158_:
{
lean_object* v_size_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v_size_4161_ = lean_ctor_get(v___y_4159_, 0);
v___x_4162_ = lean_unsigned_to_nat(1u);
v___x_4163_ = lean_nat_add(v_size_4161_, v___x_4162_);
v___x_4164_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4159_, v___x_4163_, v_i_4160_, v_name_4157_, v_a_4150_);
lean_dec(v_i_4160_);
v___y_4152_ = v___x_4164_;
goto v___jp_4151_;
}
v___jp_4165_:
{
lean_object* v___x_4167_; 
v___x_4167_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___y_4166_, v_name_4157_);
switch(lean_obj_tag(v___x_4167_))
{
case 0:
{
lean_object* v_index_4168_; lean_object* v_size_4169_; lean_object* v___x_4170_; 
v_index_4168_ = lean_ctor_get(v___x_4167_, 0);
lean_inc(v_index_4168_);
lean_dec_ref_known(v___x_4167_, 3);
v_size_4169_ = lean_ctor_get(v___y_4166_, 0);
lean_inc(v_size_4169_);
v___x_4170_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4166_, v_size_4169_, v_index_4168_, v_name_4157_, v_a_4150_);
lean_dec(v_index_4168_);
v___y_4152_ = v___x_4170_;
goto v___jp_4151_;
}
case 1:
{
lean_object* v_index_4171_; 
v_index_4171_ = lean_ctor_get(v___x_4167_, 0);
lean_inc(v_index_4171_);
lean_dec_ref_known(v___x_4167_, 1);
v___y_4159_ = v___y_4166_;
v_i_4160_ = v_index_4171_;
goto v___jp_4158_;
}
default: 
{
lean_object* v___x_4172_; lean_object* v___x_4173_; 
v___x_4172_ = lean_unsigned_to_nat(0u);
v___x_4173_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_4166_, v___x_4172_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v_index_4174_; 
v_index_4174_ = lean_ctor_get(v___x_4173_, 0);
lean_inc(v_index_4174_);
lean_dec_ref_known(v___x_4173_, 1);
v___y_4159_ = v___y_4166_;
v_i_4160_ = v_index_4174_;
goto v___jp_4158_;
}
else
{
lean_dec(v_name_4157_);
lean_dec(v_a_4150_);
v___y_4152_ = v___y_4166_;
goto v___jp_4151_;
}
}
}
}
v___jp_4175_:
{
lean_object* v_size_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
v_size_4178_ = lean_ctor_get(v___y_4176_, 0);
v___x_4179_ = lean_unsigned_to_nat(1u);
v___x_4180_ = lean_nat_add(v_size_4178_, v___x_4179_);
v___x_4181_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4176_, v___x_4180_, v_i_4177_, v_name_4157_, v_a_4150_);
lean_dec(v_i_4177_);
v___y_4152_ = v___x_4181_;
goto v___jp_4151_;
}
v___jp_4182_:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; 
v___x_4183_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg(v_b_4145_);
lean_dec_ref(v_b_4145_);
v___x_4184_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_4183_, v_name_4157_);
switch(lean_obj_tag(v___x_4184_))
{
case 0:
{
lean_object* v_index_4185_; lean_object* v_size_4186_; lean_object* v___x_4187_; 
v_index_4185_ = lean_ctor_get(v___x_4184_, 0);
lean_inc(v_index_4185_);
lean_dec_ref_known(v___x_4184_, 3);
v_size_4186_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_size_4186_);
v___x_4187_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_4183_, v_size_4186_, v_index_4185_, v_name_4157_, v_a_4150_);
lean_dec(v_index_4185_);
v___y_4152_ = v___x_4187_;
goto v___jp_4151_;
}
case 1:
{
lean_object* v_index_4188_; 
v_index_4188_ = lean_ctor_get(v___x_4184_, 0);
lean_inc(v_index_4188_);
lean_dec_ref_known(v___x_4184_, 1);
v___y_4176_ = v___x_4183_;
v_i_4177_ = v_index_4188_;
goto v___jp_4175_;
}
default: 
{
lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4189_ = lean_unsigned_to_nat(0u);
v___x_4190_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_4183_, v___x_4189_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_object* v_index_4191_; 
v_index_4191_ = lean_ctor_get(v___x_4190_, 0);
lean_inc(v_index_4191_);
lean_dec_ref_known(v___x_4190_, 1);
v___y_4176_ = v___x_4183_;
v_i_4177_ = v_index_4191_;
goto v___jp_4175_;
}
else
{
lean_dec(v_name_4157_);
lean_dec(v_a_4150_);
v___y_4152_ = v___x_4183_;
goto v___jp_4151_;
}
}
}
}
}
else
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4229_; 
lean_dec_ref(v_b_4145_);
v_a_4222_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4224_ = v___x_4149_;
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4149_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4227_; 
if (v_isShared_4225_ == 0)
{
v___x_4227_ = v___x_4224_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4222_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
}
}
else
{
lean_object* v___x_4230_; 
v___x_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4230_, 0, v_b_4145_);
return v___x_4230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_4231_, lean_object* v_i_4232_, lean_object* v_stop_4233_, lean_object* v_b_4234_, lean_object* v___y_4235_){
_start:
{
size_t v_i_boxed_4236_; size_t v_stop_boxed_4237_; lean_object* v_res_4238_; 
v_i_boxed_4236_ = lean_unbox_usize(v_i_4232_);
lean_dec(v_i_4232_);
v_stop_boxed_4237_ = lean_unbox_usize(v_stop_4233_);
lean_dec(v_stop_4233_);
v_res_4238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4231_, v_i_boxed_4236_, v_stop_boxed_4237_, v_b_4234_);
lean_dec_ref(v_as_4231_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_4239_, size_t v_i_4240_, size_t v_stop_4241_, lean_object* v_b_4242_, lean_object* v___y_4243_){
_start:
{
lean_object* v_a_4246_; lean_object* v___y_4251_; uint8_t v___x_4253_; 
v___x_4253_ = lean_usize_dec_eq(v_i_4240_, v_stop_4241_);
if (v___x_4253_ == 0)
{
lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; uint8_t v___x_4257_; 
v___x_4254_ = lean_array_uget_borrowed(v_as_4239_, v_i_4240_);
v___x_4255_ = lean_unsigned_to_nat(0u);
v___x_4256_ = lean_array_get_size(v___x_4254_);
v___x_4257_ = lean_nat_dec_lt(v___x_4255_, v___x_4256_);
if (v___x_4257_ == 0)
{
v_a_4246_ = v_b_4242_;
goto v___jp_4245_;
}
else
{
uint8_t v___x_4258_; 
v___x_4258_ = lean_nat_dec_le(v___x_4256_, v___x_4256_);
if (v___x_4258_ == 0)
{
if (v___x_4257_ == 0)
{
v_a_4246_ = v_b_4242_;
goto v___jp_4245_;
}
else
{
size_t v___x_4259_; size_t v___x_4260_; lean_object* v___x_4261_; 
v___x_4259_ = ((size_t)0ULL);
v___x_4260_ = lean_usize_of_nat(v___x_4256_);
v___x_4261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4254_, v___x_4259_, v___x_4260_, v_b_4242_);
v___y_4251_ = v___x_4261_;
goto v___jp_4250_;
}
}
else
{
size_t v___x_4262_; size_t v___x_4263_; lean_object* v___x_4264_; 
v___x_4262_ = ((size_t)0ULL);
v___x_4263_ = lean_usize_of_nat(v___x_4256_);
v___x_4264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4254_, v___x_4262_, v___x_4263_, v_b_4242_);
v___y_4251_ = v___x_4264_;
goto v___jp_4250_;
}
}
}
else
{
lean_object* v___x_4265_; 
v___x_4265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4265_, 0, v_b_4242_);
return v___x_4265_;
}
v___jp_4245_:
{
size_t v___x_4247_; size_t v___x_4248_; 
v___x_4247_ = ((size_t)1ULL);
v___x_4248_ = lean_usize_add(v_i_4240_, v___x_4247_);
v_i_4240_ = v___x_4248_;
v_b_4242_ = v_a_4246_;
goto _start;
}
v___jp_4250_:
{
if (lean_obj_tag(v___y_4251_) == 0)
{
lean_object* v_a_4252_; 
v_a_4252_ = lean_ctor_get(v___y_4251_, 0);
lean_inc(v_a_4252_);
lean_dec_ref_known(v___y_4251_, 1);
v_a_4246_ = v_a_4252_;
goto v___jp_4245_;
}
else
{
return v___y_4251_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4266_, lean_object* v_i_4267_, lean_object* v_stop_4268_, lean_object* v_b_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_){
_start:
{
size_t v_i_boxed_4272_; size_t v_stop_boxed_4273_; lean_object* v_res_4274_; 
v_i_boxed_4272_ = lean_unbox_usize(v_i_4267_);
lean_dec(v_i_4267_);
v_stop_boxed_4273_ = lean_unbox_usize(v_stop_4268_);
lean_dec(v_stop_4268_);
v_res_4274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4266_, v_i_boxed_4272_, v_stop_boxed_4273_, v_b_4269_, v___y_4270_);
lean_dec_ref(v___y_4270_);
lean_dec_ref(v_as_4266_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4275_, lean_object* v_a_4276_){
_start:
{
lean_object* v_a_4279_; lean_object* v___y_4284_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; uint8_t v___x_4298_; 
v___x_4294_ = l_Lean_attributeMapRef;
v___x_4295_ = lean_st_ref_get(v___x_4294_);
v___x_4296_ = lean_unsigned_to_nat(0u);
v___x_4297_ = lean_array_get_size(v_es_4275_);
v___x_4298_ = lean_nat_dec_lt(v___x_4296_, v___x_4297_);
if (v___x_4298_ == 0)
{
v_a_4279_ = v___x_4295_;
goto v___jp_4278_;
}
else
{
uint8_t v___x_4299_; 
v___x_4299_ = lean_nat_dec_le(v___x_4297_, v___x_4297_);
if (v___x_4299_ == 0)
{
if (v___x_4298_ == 0)
{
v_a_4279_ = v___x_4295_;
goto v___jp_4278_;
}
else
{
size_t v___x_4300_; size_t v___x_4301_; lean_object* v___x_4302_; 
v___x_4300_ = ((size_t)0ULL);
v___x_4301_ = lean_usize_of_nat(v___x_4297_);
v___x_4302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4275_, v___x_4300_, v___x_4301_, v___x_4295_, v_a_4276_);
v___y_4284_ = v___x_4302_;
goto v___jp_4283_;
}
}
else
{
size_t v___x_4303_; size_t v___x_4304_; lean_object* v___x_4305_; 
v___x_4303_ = ((size_t)0ULL);
v___x_4304_ = lean_usize_of_nat(v___x_4297_);
v___x_4305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4275_, v___x_4303_, v___x_4304_, v___x_4295_, v_a_4276_);
v___y_4284_ = v___x_4305_;
goto v___jp_4283_;
}
}
v___jp_4278_:
{
lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4280_ = lean_box(0);
v___x_4281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4280_);
lean_ctor_set(v___x_4281_, 1, v_a_4279_);
v___x_4282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4282_, 0, v___x_4281_);
return v___x_4282_;
}
v___jp_4283_:
{
if (lean_obj_tag(v___y_4284_) == 0)
{
lean_object* v_a_4285_; 
v_a_4285_ = lean_ctor_get(v___y_4284_, 0);
lean_inc(v_a_4285_);
lean_dec_ref_known(v___y_4284_, 1);
v_a_4279_ = v_a_4285_;
goto v___jp_4278_;
}
else
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4293_; 
v_a_4286_ = lean_ctor_get(v___y_4284_, 0);
v_isSharedCheck_4293_ = !lean_is_exclusive(v___y_4284_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4288_ = v___y_4284_;
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v___y_4284_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4291_; 
if (v_isShared_4289_ == 0)
{
v___x_4291_ = v___x_4288_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_a_4286_);
v___x_4291_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
return v___x_4291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_){
_start:
{
lean_object* v_res_4309_; 
v_res_4309_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4306_, v_a_4307_);
lean_dec_ref(v_a_4307_);
lean_dec_ref(v_es_4306_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4310_, size_t v_i_4311_, size_t v_stop_4312_, lean_object* v_b_4313_, lean_object* v___y_4314_){
_start:
{
lean_object* v___x_4316_; 
v___x_4316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4310_, v_i_4311_, v_stop_4312_, v_b_4313_);
return v___x_4316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4317_, lean_object* v_i_4318_, lean_object* v_stop_4319_, lean_object* v_b_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_){
_start:
{
size_t v_i_boxed_4323_; size_t v_stop_boxed_4324_; lean_object* v_res_4325_; 
v_i_boxed_4323_ = lean_unbox_usize(v_i_4318_);
lean_dec(v_i_4318_);
v_stop_boxed_4324_ = lean_unbox_usize(v_stop_4319_);
lean_dec(v_stop_4319_);
v_res_4325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4317_, v_i_boxed_4323_, v_stop_boxed_4324_, v_b_4320_, v___y_4321_);
lean_dec_ref(v___y_4321_);
lean_dec_ref(v_as_4317_);
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4326_, lean_object* v_e_4327_){
_start:
{
lean_object* v_snd_4328_; lean_object* v_toAttributeImplCore_4329_; lean_object* v_fst_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4418_; 
v_snd_4328_ = lean_ctor_get(v_e_4327_, 1);
lean_inc(v_snd_4328_);
v_toAttributeImplCore_4329_ = lean_ctor_get(v_snd_4328_, 0);
v_fst_4330_ = lean_ctor_get(v_e_4327_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v_e_4327_);
if (v_isSharedCheck_4418_ == 0)
{
lean_object* v_unused_4419_; 
v_unused_4419_ = lean_ctor_get(v_e_4327_, 1);
lean_dec(v_unused_4419_);
v___x_4332_ = v_e_4327_;
v_isShared_4333_ = v_isSharedCheck_4418_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_fst_4330_);
lean_dec(v_e_4327_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4418_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v_newEntries_4334_; lean_object* v_map_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4417_; 
v_newEntries_4334_ = lean_ctor_get(v_s_4326_, 0);
v_map_4335_ = lean_ctor_get(v_s_4326_, 1);
v_isSharedCheck_4417_ = !lean_is_exclusive(v_s_4326_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4337_ = v_s_4326_;
v_isShared_4338_ = v_isSharedCheck_4417_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_map_4335_);
lean_inc(v_newEntries_4334_);
lean_dec(v_s_4326_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4417_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v_name_4339_; lean_object* v___x_4341_; 
v_name_4339_ = lean_ctor_get(v_toAttributeImplCore_4329_, 1);
lean_inc(v_name_4339_);
if (v_isShared_4333_ == 0)
{
lean_ctor_set_tag(v___x_4332_, 1);
lean_ctor_set(v___x_4332_, 1, v_newEntries_4334_);
v___x_4341_ = v___x_4332_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_fst_4330_);
lean_ctor_set(v_reuseFailAlloc_4416_, 1, v_newEntries_4334_);
v___x_4341_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
lean_object* v___y_4343_; lean_object* v_i_4344_; lean_object* v___y_4353_; lean_object* v___y_4365_; lean_object* v_i_4366_; lean_object* v___x_4384_; 
v___x_4384_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4335_, v_name_4339_);
switch(lean_obj_tag(v___x_4384_))
{
case 0:
{
lean_object* v_index_4385_; lean_object* v_size_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
lean_del_object(v___x_4337_);
v_index_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_index_4385_);
lean_dec_ref_known(v___x_4384_, 3);
v_size_4386_ = lean_ctor_get(v_map_4335_, 0);
lean_inc(v_size_4386_);
v___x_4387_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_4335_, v_size_4386_, v_index_4385_, v_name_4339_, v_snd_4328_);
lean_dec(v_index_4385_);
v___x_4388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4341_);
lean_ctor_set(v___x_4388_, 1, v___x_4387_);
return v___x_4388_;
}
case 1:
{
lean_object* v_index_4389_; lean_object* v_size_4390_; lean_object* v_keyArray_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; uint8_t v___x_4395_; 
lean_del_object(v___x_4337_);
v_index_4389_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_index_4389_);
lean_dec_ref_known(v___x_4384_, 1);
v_size_4390_ = lean_ctor_get(v_map_4335_, 0);
v_keyArray_4391_ = lean_ctor_get(v_map_4335_, 1);
v___x_4392_ = lean_unsigned_to_nat(1u);
v___x_4393_ = lean_nat_add(v_size_4390_, v___x_4392_);
v___x_4394_ = lean_array_get_size(v_keyArray_4391_);
v___x_4395_ = lean_nat_dec_lt(v___x_4393_, v___x_4394_);
if (v___x_4395_ == 0)
{
lean_dec(v___x_4393_);
lean_dec(v_index_4389_);
goto v___jp_4372_;
}
else
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; uint8_t v___x_4400_; 
v___x_4396_ = lean_unsigned_to_nat(4u);
v___x_4397_ = lean_nat_mul(v___x_4393_, v___x_4396_);
v___x_4398_ = lean_unsigned_to_nat(3u);
v___x_4399_ = lean_nat_mul(v___x_4394_, v___x_4398_);
v___x_4400_ = lean_nat_dec_le(v___x_4397_, v___x_4399_);
lean_dec(v___x_4399_);
lean_dec(v___x_4397_);
if (v___x_4400_ == 0)
{
lean_dec(v___x_4393_);
lean_dec(v_index_4389_);
goto v___jp_4372_;
}
else
{
lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4401_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_4335_, v___x_4393_, v_index_4389_, v_name_4339_, v_snd_4328_);
lean_dec(v_index_4389_);
v___x_4402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4402_, 0, v___x_4341_);
lean_ctor_set(v___x_4402_, 1, v___x_4401_);
return v___x_4402_;
}
}
}
default: 
{
lean_object* v_size_4403_; lean_object* v_keyArray_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; uint8_t v___x_4408_; 
v_size_4403_ = lean_ctor_get(v_map_4335_, 0);
v_keyArray_4404_ = lean_ctor_get(v_map_4335_, 1);
v___x_4405_ = lean_unsigned_to_nat(1u);
v___x_4406_ = lean_nat_add(v_size_4403_, v___x_4405_);
v___x_4407_ = lean_array_get_size(v_keyArray_4404_);
v___x_4408_ = lean_nat_dec_lt(v___x_4406_, v___x_4407_);
if (v___x_4408_ == 0)
{
lean_object* v___x_4409_; 
lean_dec(v___x_4406_);
v___x_4409_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg(v_map_4335_);
lean_dec_ref(v_map_4335_);
v___y_4353_ = v___x_4409_;
goto v___jp_4352_;
}
else
{
lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; uint8_t v___x_4414_; 
v___x_4410_ = lean_unsigned_to_nat(4u);
v___x_4411_ = lean_nat_mul(v___x_4406_, v___x_4410_);
lean_dec(v___x_4406_);
v___x_4412_ = lean_unsigned_to_nat(3u);
v___x_4413_ = lean_nat_mul(v___x_4407_, v___x_4412_);
v___x_4414_ = lean_nat_dec_le(v___x_4411_, v___x_4413_);
lean_dec(v___x_4413_);
lean_dec(v___x_4411_);
if (v___x_4414_ == 0)
{
lean_object* v___x_4415_; 
v___x_4415_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg(v_map_4335_);
lean_dec_ref(v_map_4335_);
v___y_4353_ = v___x_4415_;
goto v___jp_4352_;
}
else
{
v___y_4353_ = v_map_4335_;
goto v___jp_4352_;
}
}
}
}
v___jp_4342_:
{
lean_object* v_size_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4350_; 
v_size_4345_ = lean_ctor_get(v___y_4343_, 0);
v___x_4346_ = lean_unsigned_to_nat(1u);
v___x_4347_ = lean_nat_add(v_size_4345_, v___x_4346_);
v___x_4348_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4343_, v___x_4347_, v_i_4344_, v_name_4339_, v_snd_4328_);
lean_dec(v_i_4344_);
if (v_isShared_4338_ == 0)
{
lean_ctor_set(v___x_4337_, 1, v___x_4348_);
lean_ctor_set(v___x_4337_, 0, v___x_4341_);
v___x_4350_ = v___x_4337_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4341_);
lean_ctor_set(v_reuseFailAlloc_4351_, 1, v___x_4348_);
v___x_4350_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
return v___x_4350_;
}
}
v___jp_4352_:
{
lean_object* v___x_4354_; 
v___x_4354_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___y_4353_, v_name_4339_);
switch(lean_obj_tag(v___x_4354_))
{
case 0:
{
lean_object* v_index_4355_; lean_object* v_size_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
lean_del_object(v___x_4337_);
v_index_4355_ = lean_ctor_get(v___x_4354_, 0);
lean_inc(v_index_4355_);
lean_dec_ref_known(v___x_4354_, 3);
v_size_4356_ = lean_ctor_get(v___y_4353_, 0);
lean_inc(v_size_4356_);
v___x_4357_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4353_, v_size_4356_, v_index_4355_, v_name_4339_, v_snd_4328_);
lean_dec(v_index_4355_);
v___x_4358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4358_, 0, v___x_4341_);
lean_ctor_set(v___x_4358_, 1, v___x_4357_);
return v___x_4358_;
}
case 1:
{
lean_object* v_index_4359_; 
v_index_4359_ = lean_ctor_get(v___x_4354_, 0);
lean_inc(v_index_4359_);
lean_dec_ref_known(v___x_4354_, 1);
v___y_4343_ = v___y_4353_;
v_i_4344_ = v_index_4359_;
goto v___jp_4342_;
}
default: 
{
lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4360_ = lean_unsigned_to_nat(0u);
v___x_4361_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_4353_, v___x_4360_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v_index_4362_; 
v_index_4362_ = lean_ctor_get(v___x_4361_, 0);
lean_inc(v_index_4362_);
lean_dec_ref_known(v___x_4361_, 1);
v___y_4343_ = v___y_4353_;
v_i_4344_ = v_index_4362_;
goto v___jp_4342_;
}
else
{
lean_object* v___x_4363_; 
lean_dec(v_name_4339_);
lean_del_object(v___x_4337_);
lean_dec(v_snd_4328_);
v___x_4363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4341_);
lean_ctor_set(v___x_4363_, 1, v___y_4353_);
return v___x_4363_;
}
}
}
}
v___jp_4364_:
{
lean_object* v_size_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v_size_4367_ = lean_ctor_get(v___y_4365_, 0);
v___x_4368_ = lean_unsigned_to_nat(1u);
v___x_4369_ = lean_nat_add(v_size_4367_, v___x_4368_);
v___x_4370_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4365_, v___x_4369_, v_i_4366_, v_name_4339_, v_snd_4328_);
lean_dec(v_i_4366_);
v___x_4371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4371_, 0, v___x_4341_);
lean_ctor_set(v___x_4371_, 1, v___x_4370_);
return v___x_4371_;
}
v___jp_4372_:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4373_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg(v_map_4335_);
lean_dec_ref(v_map_4335_);
v___x_4374_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_4373_, v_name_4339_);
switch(lean_obj_tag(v___x_4374_))
{
case 0:
{
lean_object* v_index_4375_; lean_object* v_size_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; 
v_index_4375_ = lean_ctor_get(v___x_4374_, 0);
lean_inc(v_index_4375_);
lean_dec_ref_known(v___x_4374_, 3);
v_size_4376_ = lean_ctor_get(v___x_4373_, 0);
lean_inc(v_size_4376_);
v___x_4377_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_4373_, v_size_4376_, v_index_4375_, v_name_4339_, v_snd_4328_);
lean_dec(v_index_4375_);
v___x_4378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4378_, 0, v___x_4341_);
lean_ctor_set(v___x_4378_, 1, v___x_4377_);
return v___x_4378_;
}
case 1:
{
lean_object* v_index_4379_; 
v_index_4379_ = lean_ctor_get(v___x_4374_, 0);
lean_inc(v_index_4379_);
lean_dec_ref_known(v___x_4374_, 1);
v___y_4365_ = v___x_4373_;
v_i_4366_ = v_index_4379_;
goto v___jp_4364_;
}
default: 
{
lean_object* v___x_4380_; lean_object* v___x_4381_; 
v___x_4380_ = lean_unsigned_to_nat(0u);
v___x_4381_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_4373_, v___x_4380_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_object* v_index_4382_; 
v_index_4382_ = lean_ctor_get(v___x_4381_, 0);
lean_inc(v_index_4382_);
lean_dec_ref_known(v___x_4381_, 1);
v___y_4365_ = v___x_4373_;
v_i_4366_ = v_index_4382_;
goto v___jp_4364_;
}
else
{
lean_object* v___x_4383_; 
lean_dec(v_name_4339_);
lean_dec(v_snd_4328_);
v___x_4383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4341_);
lean_ctor_set(v___x_4383_, 1, v___x_4373_);
return v___x_4383_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4420_, lean_object* v_s_4421_){
_start:
{
lean_object* v_newEntries_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v_newEntries_4422_ = lean_ctor_get(v_s_4421_, 0);
lean_inc(v_newEntries_4422_);
lean_dec_ref(v_s_4421_);
v___x_4423_ = l_List_reverse___redArg(v_newEntries_4422_);
v___x_4424_ = lean_array_mk(v___x_4423_);
lean_inc_ref_n(v___x_4424_, 2);
v___x_4425_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4424_);
lean_ctor_set(v___x_4425_, 1, v___x_4424_);
lean_ctor_set(v___x_4425_, 2, v___x_4424_);
return v___x_4425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4426_, lean_object* v_s_4427_){
_start:
{
lean_object* v_res_4428_; 
v_res_4428_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4426_, v_s_4427_);
lean_dec_ref(v_x_4426_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4429_){
_start:
{
lean_object* v_newEntries_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4441_; 
v_newEntries_4430_ = lean_ctor_get(v_s_4429_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v_s_4429_);
if (v_isSharedCheck_4441_ == 0)
{
lean_object* v_unused_4442_; 
v_unused_4442_ = lean_ctor_get(v_s_4429_, 1);
lean_dec(v_unused_4442_);
v___x_4432_ = v_s_4429_;
v_isShared_4433_ = v_isSharedCheck_4441_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_newEntries_4430_);
lean_dec(v_s_4429_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4441_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4439_; 
v___x_4434_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4435_ = l_List_lengthTR___redArg(v_newEntries_4430_);
lean_dec(v_newEntries_4430_);
v___x_4436_ = l_Nat_reprFast(v___x_4435_);
v___x_4437_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4437_, 0, v___x_4436_);
if (v_isShared_4433_ == 0)
{
lean_ctor_set_tag(v___x_4432_, 5);
lean_ctor_set(v___x_4432_, 1, v___x_4437_);
lean_ctor_set(v___x_4432_, 0, v___x_4434_);
v___x_4439_ = v___x_4432_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4434_);
lean_ctor_set(v_reuseFailAlloc_4440_, 1, v___x_4437_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4443_){
_start:
{
lean_object* v_newEntries_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v_newEntries_4444_ = lean_ctor_get(v_s_4443_, 0);
lean_inc(v_newEntries_4444_);
lean_dec_ref(v_s_4443_);
v___x_4445_ = l_List_reverse___redArg(v_newEntries_4444_);
v___x_4446_ = lean_array_mk(v___x_4445_);
return v___x_4446_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___f_4458_; lean_object* v___f_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; 
v___x_4456_ = lean_box(0);
v___x_4457_ = lean_box(2);
v___f_4458_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4459_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4460_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4461_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4462_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4463_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4464_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4464_, 0, v___x_4463_);
lean_ctor_set(v___x_4464_, 1, v___x_4462_);
lean_ctor_set(v___x_4464_, 2, v___x_4461_);
lean_ctor_set(v___x_4464_, 3, v___x_4460_);
lean_ctor_set(v___x_4464_, 4, v___f_4459_);
lean_ctor_set(v___x_4464_, 5, v___f_4458_);
lean_ctor_set(v___x_4464_, 6, v___x_4457_);
lean_ctor_set(v___x_4464_, 7, v___x_4456_);
return v___x_4464_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; 
v___f_4465_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4466_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4467_, 0, v___x_4466_);
lean_ctor_set(v___x_4467_, 1, v___f_4465_);
return v___x_4467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4469_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4470_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4469_);
return v___x_4470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4471_){
_start:
{
lean_object* v_res_4472_; 
v_res_4472_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4473_){
_start:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; uint8_t v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; 
v___x_4475_ = l_Lean_attributeMapRef;
v___x_4476_ = lean_st_ref_get(v___x_4475_);
v___x_4477_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4476_, v_n_4473_);
lean_dec(v___x_4476_);
v___x_4478_ = lean_box(v___x_4477_);
v___x_4479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4478_);
return v___x_4479_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4480_, lean_object* v_a_4481_){
_start:
{
lean_object* v_res_4482_; 
v_res_4482_ = l_Lean_isBuiltinAttribute(v_n_4480_);
lean_dec(v_n_4480_);
return v_res_4482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_getBuiltinAttributeNames_spec__0_spec__0(lean_object* v_b_4483_, lean_object* v_acc_4484_, lean_object* v_i_4485_){
_start:
{
lean_object* v_keyArray_4490_; lean_object* v_valueArray_4491_; lean_object* v___x_4492_; uint8_t v___x_4493_; 
v_keyArray_4490_ = lean_ctor_get(v_b_4483_, 1);
v_valueArray_4491_ = lean_ctor_get(v_b_4483_, 2);
v___x_4492_ = lean_array_get_size(v_keyArray_4490_);
v___x_4493_ = lean_nat_dec_lt(v_i_4485_, v___x_4492_);
if (v___x_4493_ == 0)
{
lean_dec(v_i_4485_);
return v_acc_4484_;
}
else
{
lean_object* v___x_4494_; uint8_t v_isSome_4495_; 
v___x_4494_ = lean_array_fget_borrowed(v_keyArray_4490_, v_i_4485_);
v_isSome_4495_ = lean_noption_is_some(v___x_4494_);
if (v_isSome_4495_ == 0)
{
goto v___jp_4486_;
}
else
{
lean_object* v___x_4496_; uint8_t v_isSome_4497_; 
v___x_4496_ = lean_array_fget_borrowed(v_valueArray_4491_, v_i_4485_);
v_isSome_4497_ = lean_noption_is_some(v___x_4496_);
if (v_isSome_4497_ == 0)
{
goto v___jp_4486_;
}
else
{
lean_object* v_val_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
lean_inc(v___x_4494_);
v_val_4498_ = lean_noption_get(v___x_4494_);
v___x_4499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4499_, 0, v_val_4498_);
lean_ctor_set(v___x_4499_, 1, v_acc_4484_);
v___x_4500_ = lean_unsigned_to_nat(1u);
v___x_4501_ = lean_nat_add(v_i_4485_, v___x_4500_);
lean_dec(v_i_4485_);
v_acc_4484_ = v___x_4499_;
v_i_4485_ = v___x_4501_;
goto _start;
}
}
}
v___jp_4486_:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4487_ = lean_unsigned_to_nat(1u);
v___x_4488_ = lean_nat_add(v_i_4485_, v___x_4487_);
lean_dec(v_i_4485_);
v_i_4485_ = v___x_4488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_getBuiltinAttributeNames_spec__0_spec__0___boxed(lean_object* v_b_4503_, lean_object* v_acc_4504_, lean_object* v_i_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_getBuiltinAttributeNames_spec__0_spec__0(v_b_4503_, v_acc_4504_, v_i_4505_);
lean_dec_ref(v_b_4503_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_init_4507_, lean_object* v_b_4508_){
_start:
{
lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4509_ = lean_unsigned_to_nat(0u);
v___x_4510_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_getBuiltinAttributeNames_spec__0_spec__0(v_b_4508_, v_init_4507_, v___x_4509_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_init_4511_, lean_object* v_b_4512_){
_start:
{
lean_object* v_res_4513_; 
v_res_4513_ = l_Std_DHashMap_Raw_foldM___at___00Lean_getBuiltinAttributeNames_spec__0(v_init_4511_, v_b_4512_);
lean_dec_ref(v_b_4512_);
return v_res_4513_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4515_ = l_Lean_attributeMapRef;
v___x_4516_ = lean_st_ref_get(v___x_4515_);
v___x_4517_ = lean_box(0);
v___x_4518_ = l_Std_DHashMap_Raw_foldM___at___00Lean_getBuiltinAttributeNames_spec__0(v___x_4517_, v___x_4516_);
lean_dec(v___x_4516_);
v___x_4519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4518_);
return v___x_4519_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4520_){
_start:
{
lean_object* v_res_4521_; 
v_res_4521_ = l_Lean_getBuiltinAttributeNames();
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4523_){
_start:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; 
v___x_4525_ = l_Lean_attributeMapRef;
v___x_4526_ = lean_st_ref_get(v___x_4525_);
v___x_4527_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4526_, v_attrName_4523_);
lean_dec(v___x_4526_);
if (lean_obj_tag(v___x_4527_) == 0)
{
lean_object* v___x_4528_; uint8_t v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; 
v___x_4528_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4529_ = 1;
v___x_4530_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4523_, v___x_4529_);
v___x_4531_ = lean_string_append(v___x_4528_, v___x_4530_);
lean_dec_ref(v___x_4530_);
v___x_4532_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4533_ = lean_string_append(v___x_4531_, v___x_4532_);
v___x_4534_ = lean_mk_io_user_error(v___x_4533_);
v___x_4535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4535_, 0, v___x_4534_);
return v___x_4535_;
}
else
{
lean_object* v_val_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4543_; 
lean_dec(v_attrName_4523_);
v_val_4536_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4538_ = v___x_4527_;
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_val_4536_);
lean_dec(v___x_4527_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
if (v_isShared_4539_ == 0)
{
lean_ctor_set_tag(v___x_4538_, 0);
v___x_4541_ = v___x_4538_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v_val_4536_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
return v___x_4541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4544_, lean_object* v_a_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4544_);
return v_res_4546_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4547_, lean_object* v_attrName_4548_){
_start:
{
lean_object* v___x_4549_; lean_object* v_toEnvExtension_4550_; lean_object* v_asyncMode_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v_map_4555_; uint8_t v___x_4556_; 
v___x_4549_ = l_Lean_attributeExtension;
v_toEnvExtension_4550_ = lean_ctor_get(v___x_4549_, 0);
v_asyncMode_4551_ = lean_ctor_get(v_toEnvExtension_4550_, 2);
v___x_4552_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4553_ = lean_box(0);
v___x_4554_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4552_, v___x_4549_, v_env_4547_, v_asyncMode_4551_, v___x_4553_);
v_map_4555_ = lean_ctor_get(v___x_4554_, 1);
lean_inc_ref(v_map_4555_);
lean_dec(v___x_4554_);
v___x_4556_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4555_, v_attrName_4548_);
lean_dec_ref(v_map_4555_);
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4557_, lean_object* v_attrName_4558_){
_start:
{
uint8_t v_res_4559_; lean_object* v_r_4560_; 
v_res_4559_ = l_Lean_isAttribute(v_env_4557_, v_attrName_4558_);
lean_dec(v_attrName_4558_);
v_r_4560_ = lean_box(v_res_4559_);
return v_r_4560_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4561_){
_start:
{
lean_object* v___x_4562_; lean_object* v_toEnvExtension_4563_; lean_object* v_asyncMode_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v_map_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; 
v___x_4562_ = l_Lean_attributeExtension;
v_toEnvExtension_4563_ = lean_ctor_get(v___x_4562_, 0);
v_asyncMode_4564_ = lean_ctor_get(v_toEnvExtension_4563_, 2);
v___x_4565_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4566_ = lean_box(0);
v___x_4567_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4565_, v___x_4562_, v_env_4561_, v_asyncMode_4564_, v___x_4566_);
v_map_4568_ = lean_ctor_get(v___x_4567_, 1);
lean_inc_ref(v_map_4568_);
lean_dec(v___x_4567_);
v___x_4569_ = lean_box(0);
v___x_4570_ = l_Std_DHashMap_Raw_foldM___at___00Lean_getBuiltinAttributeNames_spec__0(v___x_4569_, v_map_4568_);
lean_dec_ref(v_map_4568_);
return v___x_4570_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4571_, lean_object* v_attrName_4572_){
_start:
{
lean_object* v___x_4573_; lean_object* v_toEnvExtension_4574_; lean_object* v_asyncMode_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v_map_4579_; lean_object* v___x_4580_; 
v___x_4573_ = l_Lean_attributeExtension;
v_toEnvExtension_4574_ = lean_ctor_get(v___x_4573_, 0);
v_asyncMode_4575_ = lean_ctor_get(v_toEnvExtension_4574_, 2);
v___x_4576_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4577_ = lean_box(0);
v___x_4578_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4576_, v___x_4573_, v_env_4571_, v_asyncMode_4575_, v___x_4577_);
v_map_4579_ = lean_ctor_get(v___x_4578_, 1);
lean_inc_ref(v_map_4579_);
lean_dec(v___x_4578_);
v___x_4580_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4579_, v_attrName_4572_);
lean_dec_ref(v_map_4579_);
if (lean_obj_tag(v___x_4580_) == 0)
{
lean_object* v___x_4581_; uint8_t v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; 
v___x_4581_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4582_ = 1;
v___x_4583_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4572_, v___x_4582_);
v___x_4584_ = lean_string_append(v___x_4581_, v___x_4583_);
lean_dec_ref(v___x_4583_);
v___x_4585_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4586_ = lean_string_append(v___x_4584_, v___x_4585_);
v___x_4587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4586_);
return v___x_4587_;
}
else
{
lean_object* v_val_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4595_; 
lean_dec(v_attrName_4572_);
v_val_4588_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4590_ = v___x_4580_;
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_val_4588_);
lean_dec(v___x_4580_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4593_; 
if (v_isShared_4591_ == 0)
{
v___x_4593_ = v___x_4590_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_val_4588_);
v___x_4593_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
return v___x_4593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4596_, lean_object* v_builderId_4597_, lean_object* v_ref_4598_, lean_object* v_args_4599_){
_start:
{
lean_object* v_entry_4601_; lean_object* v___x_4602_; 
v_entry_4601_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4601_, 0, v_builderId_4597_);
lean_ctor_set(v_entry_4601_, 1, v_ref_4598_);
lean_ctor_set(v_entry_4601_, 2, v_args_4599_);
lean_inc_ref(v_entry_4601_);
v___x_4602_ = l_Lean_mkAttributeImplOfEntry(v_entry_4601_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v_a_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4628_; 
v_a_4603_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4605_ = v___x_4602_;
v_isShared_4606_ = v_isSharedCheck_4628_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_a_4603_);
lean_dec(v___x_4602_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4628_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v_toAttributeImplCore_4607_; lean_object* v_name_4608_; uint8_t v___x_4609_; 
v_toAttributeImplCore_4607_ = lean_ctor_get(v_a_4603_, 0);
v_name_4608_ = lean_ctor_get(v_toAttributeImplCore_4607_, 1);
lean_inc_ref(v_env_4596_);
v___x_4609_ = l_Lean_isAttribute(v_env_4596_, v_name_4608_);
if (v___x_4609_ == 0)
{
lean_object* v___x_4610_; lean_object* v_toEnvExtension_4611_; lean_object* v_asyncMode_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4617_; 
v___x_4610_ = l_Lean_attributeExtension;
v_toEnvExtension_4611_ = lean_ctor_get(v___x_4610_, 0);
v_asyncMode_4612_ = lean_ctor_get(v_toEnvExtension_4611_, 2);
v___x_4613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4613_, 0, v_entry_4601_);
lean_ctor_set(v___x_4613_, 1, v_a_4603_);
v___x_4614_ = lean_box(0);
v___x_4615_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4610_, v_env_4596_, v___x_4613_, v_asyncMode_4612_, v___x_4614_);
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 0, v___x_4615_);
v___x_4617_ = v___x_4605_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v___x_4615_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
}
}
else
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4626_; 
lean_inc(v_name_4608_);
lean_dec(v_a_4603_);
lean_dec_ref_known(v_entry_4601_, 3);
lean_dec_ref(v_env_4596_);
v___x_4619_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4620_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4608_, v___x_4609_);
v___x_4621_ = lean_string_append(v___x_4619_, v___x_4620_);
lean_dec_ref(v___x_4620_);
v___x_4622_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4623_ = lean_string_append(v___x_4621_, v___x_4622_);
v___x_4624_ = lean_mk_io_user_error(v___x_4623_);
if (v_isShared_4606_ == 0)
{
lean_ctor_set_tag(v___x_4605_, 1);
lean_ctor_set(v___x_4605_, 0, v___x_4624_);
v___x_4626_ = v___x_4605_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v___x_4624_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
}
}
}
}
else
{
lean_object* v_a_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4636_; 
lean_dec_ref_known(v_entry_4601_, 3);
lean_dec_ref(v_env_4596_);
v_a_4629_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4631_ = v___x_4602_;
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_a_4629_);
lean_dec(v___x_4602_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v___x_4634_; 
if (v_isShared_4632_ == 0)
{
v___x_4634_ = v___x_4631_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v_a_4629_);
v___x_4634_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
return v___x_4634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4637_, lean_object* v_builderId_4638_, lean_object* v_ref_4639_, lean_object* v_args_4640_, lean_object* v_a_4641_){
_start:
{
lean_object* v_res_4642_; 
v_res_4642_ = l_Lean_registerAttributeOfBuilder(v_env_4637_, v_builderId_4638_, v_ref_4639_, v_args_4640_);
return v_res_4642_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_){
_start:
{
if (lean_obj_tag(v_x_4643_) == 0)
{
lean_object* v_a_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v_a_4647_ = lean_ctor_get(v_x_4643_, 0);
lean_inc(v_a_4647_);
lean_dec_ref_known(v_x_4643_, 1);
v___x_4648_ = l_Lean_stringToMessageData(v_a_4647_);
v___x_4649_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4648_, v___y_4644_, v___y_4645_);
return v___x_4649_;
}
else
{
lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4657_; 
v_a_4650_ = lean_ctor_get(v_x_4643_, 0);
v_isSharedCheck_4657_ = !lean_is_exclusive(v_x_4643_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4652_ = v_x_4643_;
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_a_4650_);
lean_dec(v_x_4643_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4655_; 
if (v_isShared_4653_ == 0)
{
lean_ctor_set_tag(v___x_4652_, 0);
v___x_4655_ = v___x_4652_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4650_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
return v___x_4655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4658_, v___y_4659_, v___y_4660_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
return v_res_4662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4663_, lean_object* v_attrName_4664_, lean_object* v_stx_4665_, uint8_t v_kind_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_){
_start:
{
lean_object* v___x_4670_; lean_object* v_env_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4670_ = lean_st_ref_get(v_a_4668_);
v_env_4671_ = lean_ctor_get(v___x_4670_, 0);
lean_inc_ref(v_env_4671_);
lean_dec(v___x_4670_);
v___x_4672_ = l_Lean_getAttributeImpl(v_env_4671_, v_attrName_4664_);
v___x_4673_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4672_, v_a_4667_, v_a_4668_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v_a_4674_; lean_object* v_add_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v_a_4674_ = lean_ctor_get(v___x_4673_, 0);
lean_inc(v_a_4674_);
lean_dec_ref_known(v___x_4673_, 1);
v_add_4675_ = lean_ctor_get(v_a_4674_, 1);
lean_inc_ref(v_add_4675_);
lean_dec(v_a_4674_);
v___x_4676_ = lean_box(v_kind_4666_);
lean_inc(v_a_4668_);
lean_inc_ref(v_a_4667_);
v___x_4677_ = lean_apply_6(v_add_4675_, v_declName_4663_, v_stx_4665_, v___x_4676_, v_a_4667_, v_a_4668_, lean_box(0));
return v___x_4677_;
}
else
{
lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4685_; 
lean_dec(v_stx_4665_);
lean_dec(v_declName_4663_);
v_a_4678_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4680_ = v___x_4673_;
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_dec(v___x_4673_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4683_; 
if (v_isShared_4681_ == 0)
{
v___x_4683_ = v___x_4680_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_a_4678_);
v___x_4683_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
return v___x_4683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4686_, lean_object* v_attrName_4687_, lean_object* v_stx_4688_, lean_object* v_kind_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_){
_start:
{
uint8_t v_kind_boxed_4693_; lean_object* v_res_4694_; 
v_kind_boxed_4693_ = lean_unbox(v_kind_4689_);
v_res_4694_ = l_Lean_Attribute_add(v_declName_4686_, v_attrName_4687_, v_stx_4688_, v_kind_boxed_4693_, v_a_4690_, v_a_4691_);
lean_dec(v_a_4691_);
lean_dec_ref(v_a_4690_);
return v_res_4694_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4695_, lean_object* v_x_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_){
_start:
{
lean_object* v___x_4700_; 
v___x_4700_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4696_, v___y_4697_, v___y_4698_);
return v___x_4700_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4701_, lean_object* v_x_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4701_, v_x_4702_, v___y_4703_, v___y_4704_);
lean_dec(v___y_4704_);
lean_dec_ref(v___y_4703_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4707_, lean_object* v_attrName_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_){
_start:
{
lean_object* v___x_4712_; lean_object* v_env_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; 
v___x_4712_ = lean_st_ref_get(v_a_4710_);
v_env_4713_ = lean_ctor_get(v___x_4712_, 0);
lean_inc_ref(v_env_4713_);
lean_dec(v___x_4712_);
v___x_4714_ = l_Lean_getAttributeImpl(v_env_4713_, v_attrName_4708_);
v___x_4715_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4714_, v_a_4709_, v_a_4710_);
if (lean_obj_tag(v___x_4715_) == 0)
{
lean_object* v_a_4716_; lean_object* v_erase_4717_; lean_object* v___x_4718_; 
v_a_4716_ = lean_ctor_get(v___x_4715_, 0);
lean_inc(v_a_4716_);
lean_dec_ref_known(v___x_4715_, 1);
v_erase_4717_ = lean_ctor_get(v_a_4716_, 2);
lean_inc_ref(v_erase_4717_);
lean_dec(v_a_4716_);
lean_inc(v_a_4710_);
lean_inc_ref(v_a_4709_);
v___x_4718_ = lean_apply_4(v_erase_4717_, v_declName_4707_, v_a_4709_, v_a_4710_, lean_box(0));
return v___x_4718_;
}
else
{
lean_object* v_a_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4726_; 
lean_dec(v_declName_4707_);
v_a_4719_ = lean_ctor_get(v___x_4715_, 0);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___x_4715_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4721_ = v___x_4715_;
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_a_4719_);
lean_dec(v___x_4715_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v___x_4724_; 
if (v_isShared_4722_ == 0)
{
v___x_4724_ = v___x_4721_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v_a_4719_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
return v___x_4724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4727_, lean_object* v_attrName_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l_Lean_Attribute_erase(v_declName_4727_, v_attrName_4728_, v_a_4729_, v_a_4730_);
lean_dec(v_a_4730_);
lean_dec_ref(v_a_4729_);
return v_res_4732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_updateEnvAttributesImpl_spec__0_spec__0(lean_object* v_b_4733_, lean_object* v_acc_4734_, lean_object* v_i_4735_){
_start:
{
lean_object* v___y_4741_; lean_object* v_keyArray_4745_; lean_object* v_valueArray_4746_; lean_object* v___x_4747_; uint8_t v___x_4748_; 
v_keyArray_4745_ = lean_ctor_get(v_b_4733_, 1);
v_valueArray_4746_ = lean_ctor_get(v_b_4733_, 2);
v___x_4747_ = lean_array_get_size(v_keyArray_4745_);
v___x_4748_ = lean_nat_dec_lt(v_i_4735_, v___x_4747_);
if (v___x_4748_ == 0)
{
lean_dec(v_i_4735_);
return v_acc_4734_;
}
else
{
lean_object* v___x_4749_; uint8_t v_isSome_4750_; 
v___x_4749_ = lean_array_fget_borrowed(v_keyArray_4745_, v_i_4735_);
v_isSome_4750_ = lean_noption_is_some(v___x_4749_);
if (v_isSome_4750_ == 0)
{
goto v___jp_4736_;
}
else
{
lean_object* v___x_4751_; uint8_t v_isSome_4752_; 
v___x_4751_ = lean_array_fget_borrowed(v_valueArray_4746_, v_i_4735_);
v_isSome_4752_ = lean_noption_is_some(v___x_4751_);
if (v_isSome_4752_ == 0)
{
goto v___jp_4736_;
}
else
{
lean_object* v_newEntries_4753_; lean_object* v_map_4754_; lean_object* v___y_4756_; lean_object* v_val_4758_; uint8_t v___x_4759_; 
v_newEntries_4753_ = lean_ctor_get(v_acc_4734_, 0);
v_map_4754_ = lean_ctor_get(v_acc_4734_, 1);
lean_inc(v___x_4749_);
v_val_4758_ = lean_noption_get(v___x_4749_);
v___x_4759_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4754_, v_val_4758_);
if (v___x_4759_ == 0)
{
lean_object* v_val_4760_; lean_object* v___y_4762_; lean_object* v_i_4763_; lean_object* v___y_4769_; lean_object* v___y_4779_; lean_object* v_i_4780_; lean_object* v___x_4795_; 
lean_inc_ref(v_map_4754_);
lean_inc(v_newEntries_4753_);
lean_dec_ref(v_acc_4734_);
lean_inc(v___x_4751_);
v_val_4760_ = lean_noption_get(v___x_4751_);
v___x_4795_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4754_, v_val_4758_);
switch(lean_obj_tag(v___x_4795_))
{
case 0:
{
lean_object* v_index_4796_; lean_object* v_size_4797_; lean_object* v___x_4798_; 
v_index_4796_ = lean_ctor_get(v___x_4795_, 0);
lean_inc(v_index_4796_);
lean_dec_ref_known(v___x_4795_, 3);
v_size_4797_ = lean_ctor_get(v_map_4754_, 0);
lean_inc(v_size_4797_);
v___x_4798_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_4754_, v_size_4797_, v_index_4796_, v_val_4758_, v_val_4760_);
lean_dec(v_index_4796_);
v___y_4756_ = v___x_4798_;
goto v___jp_4755_;
}
case 1:
{
lean_object* v_index_4799_; lean_object* v_size_4800_; lean_object* v_keyArray_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; uint8_t v___x_4805_; 
v_index_4799_ = lean_ctor_get(v___x_4795_, 0);
lean_inc(v_index_4799_);
lean_dec_ref_known(v___x_4795_, 1);
v_size_4800_ = lean_ctor_get(v_map_4754_, 0);
v_keyArray_4801_ = lean_ctor_get(v_map_4754_, 1);
v___x_4802_ = lean_unsigned_to_nat(1u);
v___x_4803_ = lean_nat_add(v_size_4800_, v___x_4802_);
v___x_4804_ = lean_array_get_size(v_keyArray_4801_);
v___x_4805_ = lean_nat_dec_lt(v___x_4803_, v___x_4804_);
if (v___x_4805_ == 0)
{
lean_dec(v___x_4803_);
lean_dec(v_index_4799_);
goto v___jp_4785_;
}
else
{
lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; uint8_t v___x_4810_; 
v___x_4806_ = lean_unsigned_to_nat(4u);
v___x_4807_ = lean_nat_mul(v___x_4803_, v___x_4806_);
v___x_4808_ = lean_unsigned_to_nat(3u);
v___x_4809_ = lean_nat_mul(v___x_4804_, v___x_4808_);
v___x_4810_ = lean_nat_dec_le(v___x_4807_, v___x_4809_);
lean_dec(v___x_4809_);
lean_dec(v___x_4807_);
if (v___x_4810_ == 0)
{
lean_dec(v___x_4803_);
lean_dec(v_index_4799_);
goto v___jp_4785_;
}
else
{
lean_object* v___x_4811_; 
v___x_4811_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_4754_, v___x_4803_, v_index_4799_, v_val_4758_, v_val_4760_);
lean_dec(v_index_4799_);
v___y_4756_ = v___x_4811_;
goto v___jp_4755_;
}
}
}
default: 
{
lean_object* v_size_4812_; lean_object* v_keyArray_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; uint8_t v___x_4817_; 
v_size_4812_ = lean_ctor_get(v_map_4754_, 0);
v_keyArray_4813_ = lean_ctor_get(v_map_4754_, 1);
v___x_4814_ = lean_unsigned_to_nat(1u);
v___x_4815_ = lean_nat_add(v_size_4812_, v___x_4814_);
v___x_4816_ = lean_array_get_size(v_keyArray_4813_);
v___x_4817_ = lean_nat_dec_lt(v___x_4815_, v___x_4816_);
if (v___x_4817_ == 0)
{
lean_object* v___x_4818_; 
lean_dec(v___x_4815_);
v___x_4818_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg(v_map_4754_);
lean_dec_ref(v_map_4754_);
v___y_4769_ = v___x_4818_;
goto v___jp_4768_;
}
else
{
lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; uint8_t v___x_4823_; 
v___x_4819_ = lean_unsigned_to_nat(4u);
v___x_4820_ = lean_nat_mul(v___x_4815_, v___x_4819_);
lean_dec(v___x_4815_);
v___x_4821_ = lean_unsigned_to_nat(3u);
v___x_4822_ = lean_nat_mul(v___x_4816_, v___x_4821_);
v___x_4823_ = lean_nat_dec_le(v___x_4820_, v___x_4822_);
lean_dec(v___x_4822_);
lean_dec(v___x_4820_);
if (v___x_4823_ == 0)
{
lean_object* v___x_4824_; 
v___x_4824_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg(v_map_4754_);
lean_dec_ref(v_map_4754_);
v___y_4769_ = v___x_4824_;
goto v___jp_4768_;
}
else
{
v___y_4769_ = v_map_4754_;
goto v___jp_4768_;
}
}
}
}
v___jp_4761_:
{
lean_object* v_size_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; 
v_size_4764_ = lean_ctor_get(v___y_4762_, 0);
v___x_4765_ = lean_unsigned_to_nat(1u);
v___x_4766_ = lean_nat_add(v_size_4764_, v___x_4765_);
v___x_4767_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4762_, v___x_4766_, v_i_4763_, v_val_4758_, v_val_4760_);
lean_dec(v_i_4763_);
v___y_4756_ = v___x_4767_;
goto v___jp_4755_;
}
v___jp_4768_:
{
lean_object* v___x_4770_; 
v___x_4770_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___y_4769_, v_val_4758_);
switch(lean_obj_tag(v___x_4770_))
{
case 0:
{
lean_object* v_index_4771_; lean_object* v_size_4772_; lean_object* v___x_4773_; 
v_index_4771_ = lean_ctor_get(v___x_4770_, 0);
lean_inc(v_index_4771_);
lean_dec_ref_known(v___x_4770_, 3);
v_size_4772_ = lean_ctor_get(v___y_4769_, 0);
lean_inc(v_size_4772_);
v___x_4773_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4769_, v_size_4772_, v_index_4771_, v_val_4758_, v_val_4760_);
lean_dec(v_index_4771_);
v___y_4756_ = v___x_4773_;
goto v___jp_4755_;
}
case 1:
{
lean_object* v_index_4774_; 
v_index_4774_ = lean_ctor_get(v___x_4770_, 0);
lean_inc(v_index_4774_);
lean_dec_ref_known(v___x_4770_, 1);
v___y_4762_ = v___y_4769_;
v_i_4763_ = v_index_4774_;
goto v___jp_4761_;
}
default: 
{
lean_object* v___x_4775_; lean_object* v___x_4776_; 
v___x_4775_ = lean_unsigned_to_nat(0u);
v___x_4776_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_4769_, v___x_4775_);
if (lean_obj_tag(v___x_4776_) == 0)
{
lean_object* v_index_4777_; 
v_index_4777_ = lean_ctor_get(v___x_4776_, 0);
lean_inc(v_index_4777_);
lean_dec_ref_known(v___x_4776_, 1);
v___y_4762_ = v___y_4769_;
v_i_4763_ = v_index_4777_;
goto v___jp_4761_;
}
else
{
lean_dec(v_val_4760_);
lean_dec(v_val_4758_);
v___y_4756_ = v___y_4769_;
goto v___jp_4755_;
}
}
}
}
v___jp_4778_:
{
lean_object* v_size_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
v_size_4781_ = lean_ctor_get(v___y_4779_, 0);
v___x_4782_ = lean_unsigned_to_nat(1u);
v___x_4783_ = lean_nat_add(v_size_4781_, v___x_4782_);
v___x_4784_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4779_, v___x_4783_, v_i_4780_, v_val_4758_, v_val_4760_);
lean_dec(v_i_4780_);
v___y_4756_ = v___x_4784_;
goto v___jp_4755_;
}
v___jp_4785_:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4786_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerBuiltinAttribute_spec__2___redArg(v_map_4754_);
lean_dec_ref(v_map_4754_);
v___x_4787_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_4786_, v_val_4758_);
switch(lean_obj_tag(v___x_4787_))
{
case 0:
{
lean_object* v_index_4788_; lean_object* v_size_4789_; lean_object* v___x_4790_; 
v_index_4788_ = lean_ctor_get(v___x_4787_, 0);
lean_inc(v_index_4788_);
lean_dec_ref_known(v___x_4787_, 3);
v_size_4789_ = lean_ctor_get(v___x_4786_, 0);
lean_inc(v_size_4789_);
v___x_4790_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_4786_, v_size_4789_, v_index_4788_, v_val_4758_, v_val_4760_);
lean_dec(v_index_4788_);
v___y_4756_ = v___x_4790_;
goto v___jp_4755_;
}
case 1:
{
lean_object* v_index_4791_; 
v_index_4791_ = lean_ctor_get(v___x_4787_, 0);
lean_inc(v_index_4791_);
lean_dec_ref_known(v___x_4787_, 1);
v___y_4779_ = v___x_4786_;
v_i_4780_ = v_index_4791_;
goto v___jp_4778_;
}
default: 
{
lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4792_ = lean_unsigned_to_nat(0u);
v___x_4793_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_4786_, v___x_4792_);
if (lean_obj_tag(v___x_4793_) == 0)
{
lean_object* v_index_4794_; 
v_index_4794_ = lean_ctor_get(v___x_4793_, 0);
lean_inc(v_index_4794_);
lean_dec_ref_known(v___x_4793_, 1);
v___y_4779_ = v___x_4786_;
v_i_4780_ = v_index_4794_;
goto v___jp_4778_;
}
else
{
lean_dec(v_val_4760_);
lean_dec(v_val_4758_);
v___y_4756_ = v___x_4786_;
goto v___jp_4755_;
}
}
}
}
}
else
{
lean_dec(v_val_4758_);
v___y_4741_ = v_acc_4734_;
goto v___jp_4740_;
}
v___jp_4755_:
{
lean_object* v___x_4757_; 
v___x_4757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4757_, 0, v_newEntries_4753_);
lean_ctor_set(v___x_4757_, 1, v___y_4756_);
v___y_4741_ = v___x_4757_;
goto v___jp_4740_;
}
}
}
}
v___jp_4736_:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; 
v___x_4737_ = lean_unsigned_to_nat(1u);
v___x_4738_ = lean_nat_add(v_i_4735_, v___x_4737_);
lean_dec(v_i_4735_);
v_i_4735_ = v___x_4738_;
goto _start;
}
v___jp_4740_:
{
lean_object* v___x_4742_; lean_object* v___x_4743_; 
v___x_4742_ = lean_unsigned_to_nat(1u);
v___x_4743_ = lean_nat_add(v_i_4735_, v___x_4742_);
lean_dec(v_i_4735_);
v_acc_4734_ = v___y_4741_;
v_i_4735_ = v___x_4743_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_updateEnvAttributesImpl_spec__0_spec__0___boxed(lean_object* v_b_4825_, lean_object* v_acc_4826_, lean_object* v_i_4827_){
_start:
{
lean_object* v_res_4828_; 
v_res_4828_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_updateEnvAttributesImpl_spec__0_spec__0(v_b_4825_, v_acc_4826_, v_i_4827_);
lean_dec_ref(v_b_4825_);
return v_res_4828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_init_4829_, lean_object* v_b_4830_){
_start:
{
lean_object* v___x_4831_; lean_object* v___x_4832_; 
v___x_4831_ = lean_unsigned_to_nat(0u);
v___x_4832_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_updateEnvAttributesImpl_spec__0_spec__0(v_b_4830_, v_init_4829_, v___x_4831_);
return v___x_4832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_updateEnvAttributesImpl_spec__0___boxed(lean_object* v_init_4833_, lean_object* v_b_4834_){
_start:
{
lean_object* v_res_4835_; 
v_res_4835_ = l_Std_DHashMap_Raw_foldM___at___00Lean_updateEnvAttributesImpl_spec__0(v_init_4833_, v_b_4834_);
lean_dec_ref(v_b_4834_);
return v_res_4835_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4836_){
_start:
{
lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v_toEnvExtension_4841_; lean_object* v_asyncMode_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; 
v___x_4838_ = l_Lean_attributeMapRef;
v___x_4839_ = lean_st_ref_get(v___x_4838_);
v___x_4840_ = l_Lean_attributeExtension;
v_toEnvExtension_4841_ = lean_ctor_get(v___x_4840_, 0);
v_asyncMode_4842_ = lean_ctor_get(v_toEnvExtension_4841_, 2);
v___x_4843_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4844_ = lean_box(0);
lean_inc_ref(v_env_4836_);
v___x_4845_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4843_, v___x_4840_, v_env_4836_, v_asyncMode_4842_, v___x_4844_);
v___x_4846_ = l_Std_DHashMap_Raw_foldM___at___00Lean_updateEnvAttributesImpl_spec__0(v___x_4845_, v___x_4839_);
lean_dec(v___x_4839_);
v___x_4847_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4840_, v_env_4836_, v___x_4846_);
v___x_4848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4848_, 0, v___x_4847_);
return v___x_4848_;
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4849_, lean_object* v_a_4850_){
_start:
{
lean_object* v_res_4851_; 
v_res_4851_ = lean_update_env_attributes(v_env_4849_);
return v_res_4851_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v_size_4855_; lean_object* v___x_4856_; 
v___x_4853_ = l_Lean_attributeMapRef;
v___x_4854_ = lean_st_ref_get(v___x_4853_);
v_size_4855_ = lean_ctor_get(v___x_4854_, 0);
lean_inc(v_size_4855_);
lean_dec(v___x_4854_);
v___x_4856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4856_, 0, v_size_4855_);
return v___x_4856_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4857_){
_start:
{
lean_object* v_res_4858_; 
v_res_4858_ = lean_get_num_attributes();
return v_res_4858_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedAttributeApplicationTime_default = _init_l_Lean_instInhabitedAttributeApplicationTime_default();
l_Lean_instInhabitedAttributeApplicationTime = _init_l_Lean_instInhabitedAttributeApplicationTime();
l_Lean_instInhabitedAttributeKind_default = _init_l_Lean_instInhabitedAttributeKind_default();
l_Lean_instInhabitedAttributeKind = _init_l_Lean_instInhabitedAttributeKind();
res = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_attributeMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_attributeMapRef);
lean_dec_ref(res);
l_Lean_instInhabitedTagAttribute_default = _init_l_Lean_instInhabitedTagAttribute_default();
lean_mark_persistent(l_Lean_instInhabitedTagAttribute_default);
l_Lean_instInhabitedTagAttribute = _init_l_Lean_instInhabitedTagAttribute();
lean_mark_persistent(l_Lean_instInhabitedTagAttribute);
res = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_attributeImplBuilderTableRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_attributeImplBuilderTableRef);
lean_dec_ref(res);
l_Lean_instInhabitedAttributeExtensionState_default = _init_l_Lean_instInhabitedAttributeExtensionState_default();
lean_mark_persistent(l_Lean_instInhabitedAttributeExtensionState_default);
l_Lean_instInhabitedAttributeExtensionState = _init_l_Lean_instInhabitedAttributeExtensionState();
lean_mark_persistent(l_Lean_instInhabitedAttributeExtensionState);
res = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_attributeExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_attributeExtension);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_AttributeImplCore_ref___autoParam = _init_l_Lean_AttributeImplCore_ref___autoParam();
lean_mark_persistent(l_Lean_AttributeImplCore_ref___autoParam);
l_Lean_registerTagAttribute___auto__1 = _init_l_Lean_registerTagAttribute___auto__1();
lean_mark_persistent(l_Lean_registerTagAttribute___auto__1);
l_Lean_registerEnumAttributes___auto__1 = _init_l_Lean_registerEnumAttributes___auto__1();
lean_mark_persistent(l_Lean_registerEnumAttributes___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Attributes(builtin);
}
#ifdef __cplusplus
}
#endif
