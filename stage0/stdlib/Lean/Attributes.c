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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_initializing();
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_instInhabitedEnvExtension_default___redArg();
extern lean_object* l_Lean_instInhabitedMessageData_default;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findByName_x3f___redArg(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Environment_logDeclChange(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_reverse___redArg(lean_object*);
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
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_containsSortedName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_attributeMapRef;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2586810433____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2586810433____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_automationAttrsRef;
LEAN_EXPORT lean_object* l_Lean_registerAutomationAttr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerAutomationAttr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAutomationAttr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAutomationAttr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAutomationAttrGuardedBy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAutomationAttrGuardedBy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3_value;
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4;
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object*, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2_value;
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2_value;
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3;
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__6___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkAttributeImplOfEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Unknown attribute implementation builder `"};
static const lean_object* l_Lean_mkAttributeImplOfEntry___closed__0 = (const lean_object*)&l_Lean_mkAttributeImplOfEntry___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___lam__0(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_num_attributes();
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_AttributeApplicationTime_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_AttributeApplicationTime_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_AttributeApplicationTime_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(lean_object* v_afterTypeChecking_22_){
_start:
{
lean_inc(v_afterTypeChecking_22_);
return v_afterTypeChecking_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg___boxed(lean_object* v_afterTypeChecking_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(v_afterTypeChecking_23_);
lean_dec(v_afterTypeChecking_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_afterTypeChecking_28_){
_start:
{
lean_inc(v_afterTypeChecking_28_);
return v_afterTypeChecking_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_afterTypeChecking_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_AttributeApplicationTime_afterTypeChecking_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_afterTypeChecking_32_);
lean_dec(v_afterTypeChecking_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(lean_object* v_afterCompilation_35_){
_start:
{
lean_inc(v_afterCompilation_35_);
return v_afterCompilation_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg___boxed(lean_object* v_afterCompilation_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(v_afterCompilation_36_);
lean_dec(v_afterCompilation_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_afterCompilation_41_){
_start:
{
lean_inc(v_afterCompilation_41_);
return v_afterCompilation_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_afterCompilation_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_AttributeApplicationTime_afterCompilation_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_afterCompilation_45_);
lean_dec(v_afterCompilation_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(lean_object* v_beforeElaboration_48_){
_start:
{
lean_inc(v_beforeElaboration_48_);
return v_beforeElaboration_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg___boxed(lean_object* v_beforeElaboration_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(v_beforeElaboration_49_);
lean_dec(v_beforeElaboration_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_beforeElaboration_54_){
_start:
{
lean_inc(v_beforeElaboration_54_);
return v_beforeElaboration_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_beforeElaboration_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_AttributeApplicationTime_beforeElaboration_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_beforeElaboration_58_);
lean_dec(v_beforeElaboration_58_);
return v_res_60_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeApplicationTime_default(void){
_start:
{
uint8_t v___x_61_; 
v___x_61_ = 0;
return v___x_61_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeApplicationTime(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeApplicationTime_beq(uint8_t v_x_63_, uint8_t v_y_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_65_ = lean_box(v_x_63_);
v___x_66_ = lean_obj_tag_nat(v___x_65_);
lean_dec(v___x_65_);
v___x_67_ = lean_box(v_y_64_);
v___x_68_ = lean_obj_tag_nat(v___x_67_);
lean_dec(v___x_67_);
v___x_69_ = lean_nat_dec_eq(v___x_66_, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeApplicationTime_beq___boxed(lean_object* v_x_70_, lean_object* v_y_71_){
_start:
{
uint8_t v_x_24__boxed_72_; uint8_t v_y_25__boxed_73_; uint8_t v_res_74_; lean_object* v_r_75_; 
v_x_24__boxed_72_ = lean_unbox(v_x_70_);
v_y_25__boxed_73_ = lean_unbox(v_y_71_);
v_res_74_ = l_Lean_instBEqAttributeApplicationTime_beq(v_x_24__boxed_72_, v_y_25__boxed_73_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0(lean_object* v_00_u03b1_78_, lean_object* v_x_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v___x_83_; lean_object* v_env_84_; lean_object* v_ref_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_83_ = lean_st_ref_get(v___y_81_);
v_env_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc_ref(v_env_84_);
lean_dec(v___x_83_);
v_ref_85_ = lean_ctor_get(v___y_80_, 2);
v___x_86_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_80_);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v_env_84_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = lean_apply_2(v_x_79_, v___x_87_, lean_box(0));
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_96_ == 0)
{
v___x_91_ = v___x_88_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
else
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_108_; 
v_a_97_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_108_ == 0)
{
v___x_99_ = v___x_88_;
v_isShared_100_ = v_isSharedCheck_108_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_88_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_108_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_101_ = lean_io_error_to_string(v_a_97_);
v___x_102_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
v___x_103_ = l_Lean_MessageData_ofFormat(v___x_102_);
lean_inc(v_ref_85_);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v_ref_85_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_104_);
v___x_106_ = v___x_99_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0___boxed(lean_object* v_00_u03b1_109_, lean_object* v_x_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_instMonadLiftImportMAttrM___lam__0(v_00_u03b1_109_, v_x_110_, v___y_111_, v___y_112_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_114_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__10));
v___x_144_ = l_Lean_mkAtom(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__12, &l_Lean_AttributeImplCore_ref___autoParam___closed__12_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12);
v___x_146_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_147_ = lean_array_push(v___x_146_, v___x_145_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__17));
v___x_157_ = l_Lean_mkAtom(v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__18, &l_Lean_AttributeImplCore_ref___autoParam___closed__18_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18);
v___x_159_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_160_ = lean_array_push(v___x_159_, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_161_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__19, &l_Lean_AttributeImplCore_ref___autoParam___closed__19_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19);
v___x_162_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__16));
v___x_163_ = lean_box(2);
v___x_164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
lean_ctor_set(v___x_164_, 2, v___x_161_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__20, &l_Lean_AttributeImplCore_ref___autoParam___closed__20_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20);
v___x_166_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__13, &l_Lean_AttributeImplCore_ref___autoParam___closed__13_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13);
v___x_167_ = lean_array_push(v___x_166_, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__21, &l_Lean_AttributeImplCore_ref___autoParam___closed__21_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21);
v___x_169_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__11));
v___x_170_ = lean_box(2);
v___x_171_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
lean_ctor_set(v___x_171_, 2, v___x_168_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__22, &l_Lean_AttributeImplCore_ref___autoParam___closed__22_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22);
v___x_173_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_174_ = lean_array_push(v___x_173_, v___x_172_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__23, &l_Lean_AttributeImplCore_ref___autoParam___closed__23_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23);
v___x_176_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__9));
v___x_177_ = lean_box(2);
v___x_178_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___x_176_);
lean_ctor_set(v___x_178_, 2, v___x_175_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__24, &l_Lean_AttributeImplCore_ref___autoParam___closed__24_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24);
v___x_180_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_181_ = lean_array_push(v___x_180_, v___x_179_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_182_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__25, &l_Lean_AttributeImplCore_ref___autoParam___closed__25_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25);
v___x_183_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__7));
v___x_184_ = lean_box(2);
v___x_185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_183_);
lean_ctor_set(v___x_185_, 2, v___x_182_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__26, &l_Lean_AttributeImplCore_ref___autoParam___closed__26_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26);
v___x_187_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_188_ = lean_array_push(v___x_187_, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_189_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__27, &l_Lean_AttributeImplCore_ref___autoParam___closed__27_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27);
v___x_190_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__4));
v___x_191_ = lean_box(2);
v___x_192_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_190_);
lean_ctor_set(v___x_192_, 2, v___x_189_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam(void){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx___impl(uint8_t v_x_208_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_box(v_x_208_);
v___x_210_ = lean_obj_tag_nat(v___x_209_);
lean_dec(v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx___impl___boxed(lean_object* v_x_211_){
_start:
{
uint8_t v_x_4__boxed_212_; lean_object* v_res_213_; 
v_x_4__boxed_212_ = lean_unbox(v_x_211_);
v_res_213_ = l_Lean_AttributeKind_ctorIdx___impl(v_x_4__boxed_212_);
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
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_270_ = lean_box(v_x_268_);
v___x_271_ = lean_obj_tag_nat(v___x_270_);
lean_dec(v___x_270_);
v___x_272_ = lean_box(v_y_269_);
v___x_273_ = lean_obj_tag_nat(v___x_272_);
lean_dec(v___x_272_);
v___x_274_ = lean_nat_dec_eq(v___x_271_, v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeKind_beq___boxed(lean_object* v_x_275_, lean_object* v_y_276_){
_start:
{
uint8_t v_x_24__boxed_277_; uint8_t v_y_25__boxed_278_; uint8_t v_res_279_; lean_object* v_r_280_; 
v_x_24__boxed_277_ = lean_unbox(v_x_275_);
v_y_25__boxed_278_ = lean_unbox(v_y_276_);
v_res_279_ = l_Lean_instBEqAttributeKind_beq(v_x_24__boxed_277_, v_y_25__boxed_278_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind_default(void){
_start:
{
uint8_t v___x_283_; 
v___x_283_ = 0;
return v___x_283_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind(void){
_start:
{
uint8_t v___x_284_; 
v___x_284_ = 0;
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0(uint8_t v_x_288_){
_start:
{
switch(v_x_288_)
{
case 0:
{
lean_object* v___x_289_; 
v___x_289_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
return v___x_289_;
}
case 1:
{
lean_object* v___x_290_; 
v___x_290_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
return v___x_290_;
}
default: 
{
lean_object* v___x_291_; 
v___x_291_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
return v___x_291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0___boxed(lean_object* v_x_292_){
_start:
{
uint8_t v_x_36__boxed_293_; lean_object* v_res_294_; 
v_x_36__boxed_293_ = lean_unbox(v_x_292_);
v_res_294_ = l_Lean_instToStringAttributeKind___lam__0(v_x_36__boxed_293_);
return v_res_294_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = l_Lean_instInhabitedMessageData_default;
v___x_298_ = lean_box(0);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_297_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0(lean_object* v_x_300_, lean_object* v___y_301_, uint8_t v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0, &l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0);
v___x_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed(lean_object* v_x_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
uint8_t v___y_1029__boxed_314_; lean_object* v_res_315_; 
v___y_1029__boxed_314_ = lean_unbox(v___y_310_);
v_res_315_ = l_Lean_instInhabitedAttributeImpl_default___lam__0(v_x_308_, v___y_309_, v___y_1029__boxed_314_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_309_);
lean_dec(v_x_308_);
return v_res_315_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_316_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
lean_ctor_set(v___x_321_, 2, v___x_320_);
lean_ctor_set(v___x_321_, 3, v___x_320_);
lean_ctor_set(v___x_321_, 4, v___x_319_);
lean_ctor_set(v___x_321_, 5, v___x_319_);
lean_ctor_set(v___x_321_, 6, v___x_319_);
lean_ctor_set(v___x_321_, 7, v___x_319_);
lean_ctor_set(v___x_321_, 8, v___x_319_);
lean_ctor_set(v___x_321_, 9, v___x_319_);
lean_ctor_set(v___x_321_, 10, v___x_319_);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_unsigned_to_nat(32u);
v___x_323_ = lean_mk_empty_array_with_capacity(v___x_322_);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_325_ = ((size_t)5ULL);
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = lean_unsigned_to_nat(32u);
v___x_328_ = lean_mk_empty_array_with_capacity(v___x_327_);
v___x_329_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3);
v___x_330_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_328_);
lean_ctor_set(v___x_330_, 2, v___x_326_);
lean_ctor_set(v___x_330_, 3, v___x_326_);
lean_ctor_set_usize(v___x_330_, 4, v___x_325_);
return v___x_330_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_331_ = lean_box(1);
v___x_332_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4);
v___x_333_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_334_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___x_332_);
lean_ctor_set(v___x_334_, 2, v___x_331_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(lean_object* v_msgData_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___x_339_; lean_object* v_toCold_340_; lean_object* v_env_341_; lean_object* v_options_342_; uint8_t v___x_343_; lean_object* v_env_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_339_ = lean_st_ref_get(v___y_337_);
v_toCold_340_ = lean_ctor_get(v___y_336_, 0);
v_env_341_ = lean_ctor_get(v___x_339_, 0);
lean_inc_ref(v_env_341_);
lean_dec(v___x_339_);
v_options_342_ = lean_ctor_get(v_toCold_340_, 2);
v___x_343_ = 0;
v_env_344_ = l_Lean_Environment_setRecordingDeps(v_env_341_, v___x_343_);
v___x_345_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2);
v___x_346_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_342_);
v___x_347_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_347_, 0, v_env_344_);
lean_ctor_set(v___x_347_, 1, v___x_345_);
lean_ctor_set(v___x_347_, 2, v___x_346_);
lean_ctor_set(v___x_347_, 3, v_options_342_);
v___x_348_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v_msgData_335_);
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___boxed(lean_object* v_msgData_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msgData_350_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(lean_object* v_msg_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_ref_359_; lean_object* v___x_360_; lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_369_; 
v_ref_359_ = lean_ctor_get(v___y_356_, 2);
v___x_360_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msg_355_, v___y_356_, v___y_357_);
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_369_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_369_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_369_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_367_; 
lean_inc(v_ref_359_);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v_ref_359_);
lean_ctor_set(v___x_365_, 1, v_a_361_);
if (v_isShared_364_ == 0)
{
lean_ctor_set_tag(v___x_363_, 1);
lean_ctor_set(v___x_363_, 0, v___x_365_);
v___x_367_ = v___x_363_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg___boxed(lean_object* v_msg_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_374_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2));
v___x_380_ = l_Lean_stringToMessageData(v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1(lean_object* v___x_381_, lean_object* v_decl_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_name_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_name_386_ = lean_ctor_get(v___x_381_, 1);
lean_inc(v_name_386_);
lean_dec_ref(v___x_381_);
v___x_387_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_388_ = l_Lean_MessageData_ofName(v_name_386_);
v___x_389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_389_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_391_, v___y_383_, v___y_384_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed(lean_object* v___x_393_, lean_object* v_decl_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_instInhabitedAttributeImpl_default___lam__1(v___x_393_, v_decl_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v_decl_394_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(lean_object* v_00_u03b1_407_, lean_object* v_msg_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_408_, v___y_409_, v___y_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___boxed(lean_object* v_00_u03b1_413_, lean_object* v_msg_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(v_00_u03b1_413_, v_msg_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_418_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_box(0);
v___x_421_ = lean_unsigned_to_nat(16u);
v___x_422_ = lean_mk_array(v___x_421_, v___x_420_);
return v___x_422_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v___x_423_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_428_ = lean_st_mk_ref(v___x_427_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
return v_res_431_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object* v_a_432_, lean_object* v_x_433_){
_start:
{
if (lean_obj_tag(v_x_433_) == 0)
{
uint8_t v___x_434_; 
v___x_434_ = 0;
return v___x_434_;
}
else
{
lean_object* v_key_435_; lean_object* v_tail_436_; uint8_t v___x_437_; 
v_key_435_ = lean_ctor_get(v_x_433_, 0);
v_tail_436_ = lean_ctor_get(v_x_433_, 2);
v___x_437_ = lean_name_eq(v_key_435_, v_a_432_);
if (v___x_437_ == 0)
{
v_x_433_ = v_tail_436_;
goto _start;
}
else
{
return v___x_437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg___boxed(lean_object* v_a_439_, lean_object* v_x_440_){
_start:
{
uint8_t v_res_441_; lean_object* v_r_442_; 
v_res_441_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_439_, v_x_440_);
lean_dec(v_x_440_);
lean_dec(v_a_439_);
v_r_442_ = lean_box(v_res_441_);
return v_r_442_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(lean_object* v_m_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_buckets_445_; lean_object* v___x_446_; uint64_t v___y_448_; 
v_buckets_445_ = lean_ctor_get(v_m_443_, 1);
v___x_446_ = lean_array_get_size(v_buckets_445_);
if (lean_obj_tag(v_a_444_) == 0)
{
uint64_t v___x_462_; 
v___x_462_ = 1723ULL;
v___y_448_ = v___x_462_;
goto v___jp_447_;
}
else
{
uint64_t v_hash_463_; 
v_hash_463_ = lean_ctor_get_uint64(v_a_444_, sizeof(void*)*2);
v___y_448_ = v_hash_463_;
goto v___jp_447_;
}
v___jp_447_:
{
uint64_t v___x_449_; uint64_t v___x_450_; uint64_t v_fold_451_; uint64_t v___x_452_; uint64_t v___x_453_; uint64_t v___x_454_; size_t v___x_455_; size_t v___x_456_; size_t v___x_457_; size_t v___x_458_; size_t v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_449_ = 32ULL;
v___x_450_ = lean_uint64_shift_right(v___y_448_, v___x_449_);
v_fold_451_ = lean_uint64_xor(v___y_448_, v___x_450_);
v___x_452_ = 16ULL;
v___x_453_ = lean_uint64_shift_right(v_fold_451_, v___x_452_);
v___x_454_ = lean_uint64_xor(v_fold_451_, v___x_453_);
v___x_455_ = lean_uint64_to_usize(v___x_454_);
v___x_456_ = lean_usize_of_nat(v___x_446_);
v___x_457_ = ((size_t)1ULL);
v___x_458_ = lean_usize_sub(v___x_456_, v___x_457_);
v___x_459_ = lean_usize_land(v___x_455_, v___x_458_);
v___x_460_ = lean_array_uget_borrowed(v_buckets_445_, v___x_459_);
v___x_461_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_444_, v___x_460_);
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___boxed(lean_object* v_m_464_, lean_object* v_a_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_464_, v_a_465_);
lean_dec(v_a_465_);
lean_dec_ref(v_m_464_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(lean_object* v_a_468_, lean_object* v_b_469_, lean_object* v_x_470_){
_start:
{
if (lean_obj_tag(v_x_470_) == 0)
{
lean_dec(v_b_469_);
lean_dec(v_a_468_);
return v_x_470_;
}
else
{
lean_object* v_key_471_; lean_object* v_value_472_; lean_object* v_tail_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_485_; 
v_key_471_ = lean_ctor_get(v_x_470_, 0);
v_value_472_ = lean_ctor_get(v_x_470_, 1);
v_tail_473_ = lean_ctor_get(v_x_470_, 2);
v_isSharedCheck_485_ = !lean_is_exclusive(v_x_470_);
if (v_isSharedCheck_485_ == 0)
{
v___x_475_ = v_x_470_;
v_isShared_476_ = v_isSharedCheck_485_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_tail_473_);
lean_inc(v_value_472_);
lean_inc(v_key_471_);
lean_dec(v_x_470_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_485_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
uint8_t v___x_477_; 
v___x_477_ = lean_name_eq(v_key_471_, v_a_468_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_478_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_468_, v_b_469_, v_tail_473_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 2, v___x_478_);
v___x_480_ = v___x_475_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_key_471_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_value_472_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
else
{
lean_object* v___x_483_; 
lean_dec(v_value_472_);
lean_dec(v_key_471_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 1, v_b_469_);
lean_ctor_set(v___x_475_, 0, v_a_468_);
v___x_483_ = v___x_475_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_468_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_b_469_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_tail_473_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_486_, lean_object* v_x_487_){
_start:
{
if (lean_obj_tag(v_x_487_) == 0)
{
return v_x_486_;
}
else
{
lean_object* v_key_488_; lean_object* v_value_489_; lean_object* v_tail_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_516_; 
v_key_488_ = lean_ctor_get(v_x_487_, 0);
v_value_489_ = lean_ctor_get(v_x_487_, 1);
v_tail_490_ = lean_ctor_get(v_x_487_, 2);
v_isSharedCheck_516_ = !lean_is_exclusive(v_x_487_);
if (v_isSharedCheck_516_ == 0)
{
v___x_492_ = v_x_487_;
v_isShared_493_ = v_isSharedCheck_516_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_tail_490_);
lean_inc(v_value_489_);
lean_inc(v_key_488_);
lean_dec(v_x_487_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_516_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; uint64_t v___y_496_; 
v___x_494_ = lean_array_get_size(v_x_486_);
if (lean_obj_tag(v_key_488_) == 0)
{
uint64_t v___x_514_; 
v___x_514_ = 1723ULL;
v___y_496_ = v___x_514_;
goto v___jp_495_;
}
else
{
uint64_t v_hash_515_; 
v_hash_515_ = lean_ctor_get_uint64(v_key_488_, sizeof(void*)*2);
v___y_496_ = v_hash_515_;
goto v___jp_495_;
}
v___jp_495_:
{
uint64_t v___x_497_; uint64_t v___x_498_; uint64_t v_fold_499_; uint64_t v___x_500_; uint64_t v___x_501_; uint64_t v___x_502_; size_t v___x_503_; size_t v___x_504_; size_t v___x_505_; size_t v___x_506_; size_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_497_ = 32ULL;
v___x_498_ = lean_uint64_shift_right(v___y_496_, v___x_497_);
v_fold_499_ = lean_uint64_xor(v___y_496_, v___x_498_);
v___x_500_ = 16ULL;
v___x_501_ = lean_uint64_shift_right(v_fold_499_, v___x_500_);
v___x_502_ = lean_uint64_xor(v_fold_499_, v___x_501_);
v___x_503_ = lean_uint64_to_usize(v___x_502_);
v___x_504_ = lean_usize_of_nat(v___x_494_);
v___x_505_ = ((size_t)1ULL);
v___x_506_ = lean_usize_sub(v___x_504_, v___x_505_);
v___x_507_ = lean_usize_land(v___x_503_, v___x_506_);
v___x_508_ = lean_array_uget_borrowed(v_x_486_, v___x_507_);
lean_inc(v___x_508_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 2, v___x_508_);
v___x_510_ = v___x_492_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_key_488_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_value_489_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v___x_508_);
v___x_510_ = v_reuseFailAlloc_513_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_511_; 
v___x_511_ = lean_array_uset(v_x_486_, v___x_507_, v___x_510_);
v_x_486_ = v___x_511_;
v_x_487_ = v_tail_490_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(lean_object* v_i_517_, lean_object* v_source_518_, lean_object* v_target_519_){
_start:
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = lean_array_get_size(v_source_518_);
v___x_521_ = lean_nat_dec_lt(v_i_517_, v___x_520_);
if (v___x_521_ == 0)
{
lean_dec_ref(v_source_518_);
lean_dec(v_i_517_);
return v_target_519_;
}
else
{
lean_object* v_es_522_; lean_object* v___x_523_; lean_object* v_source_524_; lean_object* v_target_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v_es_522_ = lean_array_fget(v_source_518_, v_i_517_);
v___x_523_ = lean_box(0);
v_source_524_ = lean_array_fset(v_source_518_, v_i_517_, v___x_523_);
v_target_525_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_target_519_, v_es_522_);
v___x_526_ = lean_unsigned_to_nat(1u);
v___x_527_ = lean_nat_add(v_i_517_, v___x_526_);
lean_dec(v_i_517_);
v_i_517_ = v___x_527_;
v_source_518_ = v_source_524_;
v_target_519_ = v_target_525_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(lean_object* v_data_529_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v_nbuckets_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_530_ = lean_array_get_size(v_data_529_);
v___x_531_ = lean_unsigned_to_nat(2u);
v_nbuckets_532_ = lean_nat_mul(v___x_530_, v___x_531_);
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = lean_box(0);
v___x_535_ = lean_mk_array(v_nbuckets_532_, v___x_534_);
v___x_536_ = lean_array_propagate_mark(v_data_529_, v___x_535_);
v___x_537_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v___x_533_, v_data_529_, v___x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(lean_object* v_m_538_, lean_object* v_a_539_, lean_object* v_b_540_){
_start:
{
lean_object* v_size_541_; lean_object* v_buckets_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_588_; 
v_size_541_ = lean_ctor_get(v_m_538_, 0);
v_buckets_542_ = lean_ctor_get(v_m_538_, 1);
v_isSharedCheck_588_ = !lean_is_exclusive(v_m_538_);
if (v_isSharedCheck_588_ == 0)
{
v___x_544_ = v_m_538_;
v_isShared_545_ = v_isSharedCheck_588_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_buckets_542_);
lean_inc(v_size_541_);
lean_dec(v_m_538_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_588_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; uint64_t v___y_548_; 
v___x_546_ = lean_array_get_size(v_buckets_542_);
if (lean_obj_tag(v_a_539_) == 0)
{
uint64_t v___x_586_; 
v___x_586_ = 1723ULL;
v___y_548_ = v___x_586_;
goto v___jp_547_;
}
else
{
uint64_t v_hash_587_; 
v_hash_587_ = lean_ctor_get_uint64(v_a_539_, sizeof(void*)*2);
v___y_548_ = v_hash_587_;
goto v___jp_547_;
}
v___jp_547_:
{
uint64_t v___x_549_; uint64_t v___x_550_; uint64_t v_fold_551_; uint64_t v___x_552_; uint64_t v___x_553_; uint64_t v___x_554_; size_t v___x_555_; size_t v___x_556_; size_t v___x_557_; size_t v___x_558_; size_t v___x_559_; lean_object* v_bkt_560_; uint8_t v___x_561_; 
v___x_549_ = 32ULL;
v___x_550_ = lean_uint64_shift_right(v___y_548_, v___x_549_);
v_fold_551_ = lean_uint64_xor(v___y_548_, v___x_550_);
v___x_552_ = 16ULL;
v___x_553_ = lean_uint64_shift_right(v_fold_551_, v___x_552_);
v___x_554_ = lean_uint64_xor(v_fold_551_, v___x_553_);
v___x_555_ = lean_uint64_to_usize(v___x_554_);
v___x_556_ = lean_usize_of_nat(v___x_546_);
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_sub(v___x_556_, v___x_557_);
v___x_559_ = lean_usize_land(v___x_555_, v___x_558_);
v_bkt_560_ = lean_array_uget_borrowed(v_buckets_542_, v___x_559_);
v___x_561_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_539_, v_bkt_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v_size_x27_563_; lean_object* v___x_564_; lean_object* v_buckets_x27_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_562_ = lean_unsigned_to_nat(1u);
v_size_x27_563_ = lean_nat_add(v_size_541_, v___x_562_);
lean_dec(v_size_541_);
lean_inc(v_bkt_560_);
v___x_564_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_564_, 0, v_a_539_);
lean_ctor_set(v___x_564_, 1, v_b_540_);
lean_ctor_set(v___x_564_, 2, v_bkt_560_);
v_buckets_x27_565_ = lean_array_uset(v_buckets_542_, v___x_559_, v___x_564_);
v___x_566_ = lean_unsigned_to_nat(4u);
v___x_567_ = lean_nat_mul(v_size_x27_563_, v___x_566_);
v___x_568_ = lean_unsigned_to_nat(3u);
v___x_569_ = lean_nat_div(v___x_567_, v___x_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_array_get_size(v_buckets_x27_565_);
v___x_571_ = lean_nat_dec_le(v___x_569_, v___x_570_);
lean_dec(v___x_569_);
if (v___x_571_ == 0)
{
lean_object* v_val_572_; lean_object* v___x_574_; 
v_val_572_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_buckets_x27_565_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 1, v_val_572_);
lean_ctor_set(v___x_544_, 0, v_size_x27_563_);
v___x_574_ = v___x_544_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_size_x27_563_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_val_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
else
{
lean_object* v___x_577_; 
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 1, v_buckets_x27_565_);
lean_ctor_set(v___x_544_, 0, v_size_x27_563_);
v___x_577_ = v___x_544_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_size_x27_563_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_buckets_x27_565_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
else
{
lean_object* v___x_579_; lean_object* v_buckets_x27_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_584_; 
lean_inc(v_bkt_560_);
v___x_579_ = lean_box(0);
v_buckets_x27_580_ = lean_array_uset(v_buckets_542_, v___x_559_, v___x_579_);
v___x_581_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_539_, v_b_540_, v_bkt_560_);
v___x_582_ = lean_array_uset(v_buckets_x27_580_, v___x_559_, v___x_581_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 1, v___x_582_);
v___x_584_ = v___x_544_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_size_541_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_registerBuiltinAttribute___closed__1(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__0));
v___x_591_ = lean_mk_io_user_error(v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute(lean_object* v_attr_594_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v_toAttributeImplCore_598_; lean_object* v_name_599_; uint8_t v___x_600_; 
v___x_596_ = l_Lean_attributeMapRef;
v___x_597_ = lean_st_ref_get(v___x_596_);
v_toAttributeImplCore_598_ = lean_ctor_get(v_attr_594_, 0);
v_name_599_ = lean_ctor_get(v_toAttributeImplCore_598_, 1);
lean_inc(v_name_599_);
v___x_600_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_597_, v_name_599_);
lean_dec(v___x_597_);
if (v___x_600_ == 0)
{
uint8_t v___x_601_; 
v___x_601_ = l_Lean_initializing();
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec(v_name_599_);
lean_dec_ref(v_attr_594_);
v___x_602_ = lean_obj_once(&l_Lean_registerBuiltinAttribute___closed__1, &l_Lean_registerBuiltinAttribute___closed__1_once, _init_l_Lean_registerBuiltinAttribute___closed__1);
v___x_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
return v___x_603_;
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_604_ = lean_st_ref_take(v___x_596_);
v___x_605_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_604_, v_name_599_, v_attr_594_);
v___x_606_ = lean_st_ref_put(v___x_596_, v___x_605_);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
}
else
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec_ref(v_attr_594_);
v___x_608_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_609_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_599_, v___x_600_);
v___x_610_ = lean_string_append(v___x_608_, v___x_609_);
lean_dec_ref(v___x_609_);
v___x_611_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_612_ = lean_string_append(v___x_610_, v___x_611_);
v___x_613_ = lean_mk_io_user_error(v___x_612_);
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
return v___x_614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute___boxed(lean_object* v_attr_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_registerBuiltinAttribute(v_attr_615_);
return v_res_617_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(lean_object* v_00_u03b2_618_, lean_object* v_m_619_, lean_object* v_a_620_){
_start:
{
uint8_t v___x_621_; 
v___x_621_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_619_, v_a_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___boxed(lean_object* v_00_u03b2_622_, lean_object* v_m_623_, lean_object* v_a_624_){
_start:
{
uint8_t v_res_625_; lean_object* v_r_626_; 
v_res_625_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(v_00_u03b2_622_, v_m_623_, v_a_624_);
lean_dec(v_a_624_);
lean_dec_ref(v_m_623_);
v_r_626_ = lean_box(v_res_625_);
return v_r_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1(lean_object* v_00_u03b2_627_, lean_object* v_m_628_, lean_object* v_a_629_, lean_object* v_b_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_m_628_, v_a_629_, v_b_630_);
return v___x_631_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_object* v_00_u03b2_632_, lean_object* v_a_633_, lean_object* v_x_634_){
_start:
{
uint8_t v___x_635_; 
v___x_635_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_633_, v_x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___boxed(lean_object* v_00_u03b2_636_, lean_object* v_a_637_, lean_object* v_x_638_){
_start:
{
uint8_t v_res_639_; lean_object* v_r_640_; 
v_res_639_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(v_00_u03b2_636_, v_a_637_, v_x_638_);
lean_dec(v_x_638_);
lean_dec(v_a_637_);
v_r_640_ = lean_box(v_res_639_);
return v_r_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(lean_object* v_00_u03b2_641_, lean_object* v_data_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_data_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3(lean_object* v_00_u03b2_644_, lean_object* v_a_645_, lean_object* v_b_646_, lean_object* v_x_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_645_, v_b_646_, v_x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_649_, lean_object* v_i_650_, lean_object* v_source_651_, lean_object* v_target_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v_i_650_, v_source_651_, v_target_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_x_655_, v_x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2586810433____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = lean_box(1);
v___x_660_ = lean_st_mk_ref(v___x_659_);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2586810433____hygCtx___hyg_2____boxed(lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2586810433____hygCtx___hyg_2_();
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAutomationAttr(lean_object* v_attrName_664_, lean_object* v_isGuardedBy_665_){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_667_ = l_Lean_automationAttrsRef;
v___x_668_ = lean_st_ref_take(v___x_667_);
v___x_669_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_attrName_664_, v_isGuardedBy_665_, v___x_668_);
v___x_670_ = lean_st_ref_put(v___x_667_, v___x_669_);
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAutomationAttr___boxed(lean_object* v_attrName_672_, lean_object* v_isGuardedBy_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_registerAutomationAttr(v_attrName_672_, v_isGuardedBy_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAutomationAttr(lean_object* v_attrName_676_){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_678_ = l_Lean_automationAttrsRef;
v___x_679_ = lean_st_ref_get(v___x_678_);
v___x_680_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_attrName_676_, v___x_679_);
lean_dec(v___x_679_);
v___x_681_ = lean_box(v___x_680_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAutomationAttr___boxed(lean_object* v_attrName_683_, lean_object* v_a_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_isAutomationAttr(v_attrName_683_);
lean_dec(v_attrName_683_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAutomationAttrGuardedBy(lean_object* v_attrName_686_, lean_object* v_p_687_, lean_object* v_declName_688_, lean_object* v_stx_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_693_ = l_Lean_automationAttrsRef;
v___x_694_ = lean_st_ref_get(v___x_693_);
v___x_695_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_694_, v_attrName_686_);
lean_dec(v___x_694_);
if (lean_obj_tag(v___x_695_) == 1)
{
lean_object* v_val_696_; lean_object* v___x_697_; 
v_val_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_val_696_);
lean_dec_ref_known(v___x_695_, 1);
lean_inc(v_a_691_);
lean_inc_ref(v_a_690_);
v___x_697_ = lean_apply_6(v_val_696_, v_p_687_, v_declName_688_, v_stx_689_, v_a_690_, v_a_691_, lean_box(0));
return v___x_697_;
}
else
{
uint8_t v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
lean_dec(v___x_695_);
lean_dec(v_stx_689_);
lean_dec(v_declName_688_);
lean_dec_ref(v_p_687_);
v___x_698_ = 0;
v___x_699_ = lean_box(v___x_698_);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isAutomationAttrGuardedBy___boxed(lean_object* v_attrName_701_, lean_object* v_p_702_, lean_object* v_declName_703_, lean_object* v_stx_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_isAutomationAttrGuardedBy(v_attrName_701_, v_p_702_, v_declName_703_, v_stx_704_, v_a_705_, v_a_706_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_attrName_701_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object* v_ref_709_, lean_object* v_msg_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_toCold_714_; lean_object* v_currRecDepth_715_; lean_object* v_ref_716_; uint16_t v_optionFlags_717_; uint8_t v_suppressElabErrors_718_; uint8_t v_checkDeprecated_719_; uint8_t v_isRecordingDeps_720_; lean_object* v_ref_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_toCold_714_ = lean_ctor_get(v___y_711_, 0);
v_currRecDepth_715_ = lean_ctor_get(v___y_711_, 1);
v_ref_716_ = lean_ctor_get(v___y_711_, 2);
v_optionFlags_717_ = lean_ctor_get_uint16(v___y_711_, sizeof(void*)*3);
v_suppressElabErrors_718_ = lean_ctor_get_uint8(v___y_711_, sizeof(void*)*3 + 2);
v_checkDeprecated_719_ = lean_ctor_get_uint8(v___y_711_, sizeof(void*)*3 + 3);
v_isRecordingDeps_720_ = lean_ctor_get_uint8(v___y_711_, sizeof(void*)*3 + 4);
v_ref_721_ = l_Lean_replaceRef(v_ref_709_, v_ref_716_);
lean_inc(v_currRecDepth_715_);
lean_inc_ref(v_toCold_714_);
v___x_722_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_722_, 0, v_toCold_714_);
lean_ctor_set(v___x_722_, 1, v_currRecDepth_715_);
lean_ctor_set(v___x_722_, 2, v_ref_721_);
lean_ctor_set_uint16(v___x_722_, sizeof(void*)*3, v_optionFlags_717_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*3 + 2, v_suppressElabErrors_718_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*3 + 3, v_checkDeprecated_719_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*3 + 4, v_isRecordingDeps_720_);
v___x_723_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_710_, v___x_722_, v___y_712_);
lean_dec_ref_known(v___x_722_, 3);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object* v_ref_724_, lean_object* v_msg_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_724_, v_msg_725_, v___y_726_, v___y_727_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v_ref_724_);
return v_res_729_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__3));
v___x_739_ = l_Lean_stringToMessageData(v___x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object* v_stx_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_760_; uint8_t v___x_761_; 
lean_inc(v_stx_746_);
v___x_750_ = l_Lean_Syntax_getKind(v_stx_746_);
v___x_760_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_761_ = lean_name_eq(v___x_750_, v___x_760_);
if (v___x_761_ == 0)
{
goto v___jp_751_;
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = l_Lean_Syntax_getArg(v_stx_746_, v___x_762_);
v___x_764_ = l_Lean_Syntax_isNone(v___x_763_);
lean_dec(v___x_763_);
if (v___x_764_ == 0)
{
goto v___jp_751_;
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_765_ = lean_unsigned_to_nat(2u);
v___x_766_ = l_Lean_Syntax_getArg(v_stx_746_, v___x_765_);
v___x_767_ = l_Lean_Syntax_isNone(v___x_766_);
lean_dec(v___x_766_);
if (v___x_767_ == 0)
{
goto v___jp_751_;
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; 
lean_dec(v___x_750_);
lean_dec(v_stx_746_);
v___x_768_ = lean_box(0);
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
return v___x_769_;
}
}
}
v___jp_751_:
{
lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_752_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__2));
v___x_753_ = lean_name_eq(v___x_750_, v___x_752_);
lean_dec(v___x_750_);
if (v___x_753_ == 0)
{
if (lean_obj_tag(v_stx_746_) == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_box(0);
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
return v___x_755_;
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_obj_once(&l_Lean_Attribute_Builtin_ensureNoArgs___closed__4, &l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once, _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4);
v___x_757_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_746_, v___x_756_, v_a_747_, v_a_748_);
lean_dec(v_stx_746_);
return v___x_757_;
}
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec(v_stx_746_);
v___x_758_ = lean_box(0);
v___x_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
return v___x_759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object* v_stx_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_770_, v_a_771_, v_a_772_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object* v_00_u03b1_775_, lean_object* v_ref_776_, lean_object* v_msg_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_776_, v_msg_777_, v___y_778_, v___y_779_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object* v_00_u03b1_782_, lean_object* v_ref_783_, lean_object* v_msg_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(v_00_u03b1_782_, v_ref_783_, v_msg_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v_ref_783_);
return v_res_788_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__4));
v___x_803_ = l_Lean_stringToMessageData(v___x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object* v_stx_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
lean_inc(v_stx_804_);
v___x_816_ = l_Lean_Syntax_getKind(v_stx_804_);
v___x_817_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_818_ = lean_name_eq(v___x_816_, v___x_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_819_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_820_ = lean_name_eq(v___x_816_, v___x_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_821_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_822_ = lean_name_eq(v___x_816_, v___x_821_);
lean_dec(v___x_816_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_824_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_804_, v___x_823_, v_a_805_, v_a_806_);
lean_dec(v_stx_804_);
return v___x_824_;
}
else
{
goto v___jp_808_;
}
}
else
{
lean_dec(v___x_816_);
goto v___jp_808_;
}
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
lean_dec(v___x_816_);
v___x_825_ = lean_unsigned_to_nat(1u);
v___x_826_ = l_Lean_Syntax_getArg(v_stx_804_, v___x_825_);
lean_dec(v_stx_804_);
v___x_827_ = l_Lean_Syntax_isNone(v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = l_Lean_Syntax_getArg(v___x_826_, v___x_828_);
lean_dec(v___x_826_);
v___x_830_ = l_Lean_Syntax_isIdent(v___x_829_);
if (v___x_830_ == 0)
{
lean_dec(v___x_829_);
goto v___jp_813_;
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
else
{
lean_dec(v___x_826_);
goto v___jp_813_;
}
}
v___jp_808_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = l_Lean_Syntax_getArg(v_stx_804_, v___x_809_);
lean_dec(v_stx_804_);
v___x_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
v___jp_813_:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_box(0);
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
return v___x_815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object* v_stx_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_833_, v_a_834_, v_a_835_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
return v_res_837_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent___closed__1(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent___closed__0));
v___x_840_ = l_Lean_stringToMessageData(v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v___x_845_; 
lean_inc(v_stx_841_);
v___x_845_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_859_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_859_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_859_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_859_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
if (lean_obj_tag(v_a_846_) == 0)
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
lean_del_object(v___x_848_);
v___x_850_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent___closed__1, &l_Lean_Attribute_Builtin_getIdent___closed__1_once, _init_l_Lean_Attribute_Builtin_getIdent___closed__1);
lean_inc(v_stx_841_);
v___x_851_ = l_Lean_MessageData_ofSyntax(v_stx_841_);
v___x_852_ = l_Lean_indentD(v___x_851_);
v___x_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_850_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_841_, v___x_853_, v_a_842_, v_a_843_);
lean_dec(v_stx_841_);
return v___x_854_;
}
else
{
lean_object* v_val_855_; lean_object* v___x_857_; 
lean_dec(v_stx_841_);
v_val_855_ = lean_ctor_get(v_a_846_, 0);
lean_inc(v_val_855_);
lean_dec_ref_known(v_a_846_, 1);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v_val_855_);
v___x_857_ = v___x_848_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_val_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec(v_stx_841_);
v_a_860_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_845_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_845_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_Attribute_Builtin_getIdent(v_stx_868_, v_a_869_, v_a_870_);
lean_dec(v_a_870_);
lean_dec_ref(v_a_869_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_873_, v_a_874_, v_a_875_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_898_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_898_ == 0)
{
v___x_880_ = v___x_877_;
v_isShared_881_ = v_isSharedCheck_898_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_877_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_898_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
if (lean_obj_tag(v_a_878_) == 0)
{
lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_882_ = lean_box(0);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_882_);
v___x_884_ = v___x_880_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
else
{
lean_object* v_val_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_897_; 
v_val_886_ = lean_ctor_get(v_a_878_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v_a_878_);
if (v_isSharedCheck_897_ == 0)
{
v___x_888_ = v_a_878_;
v_isShared_889_ = v_isSharedCheck_897_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_val_886_);
lean_dec(v_a_878_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_897_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = l_Lean_Syntax_getId(v_val_886_);
lean_dec(v_val_886_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_890_);
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_896_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_894_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_892_);
v___x_894_ = v___x_880_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
v_a_899_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_877_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_877_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_907_, v_a_908_, v_a_909_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_Lean_Attribute_Builtin_getIdent(v_stx_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_925_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_925_ == 0)
{
v___x_919_ = v___x_916_;
v_isShared_920_ = v_isSharedCheck_925_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_916_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_925_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_921_ = l_Lean_Syntax_getId(v_a_917_);
lean_dec(v_a_917_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v___x_921_);
v___x_923_ = v___x_919_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
v_a_926_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_916_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_916_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_Attribute_Builtin_getId(v_stx_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
return v_res_938_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_941_ = l_Lean_stringToMessageData(v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = l_Lean_Syntax_isNone(v_optPrioStx_942_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = l_Lean_Syntax_getArg(v_optPrioStx_942_, v___x_947_);
v___x_949_ = l_Lean_Syntax_isNatLit_x3f(v___x_948_);
lean_dec(v___x_948_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_950_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_942_);
v___x_951_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_942_);
v___x_952_ = l_Lean_indentD(v___x_951_);
v___x_953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_950_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_942_, v___x_953_, v_a_943_, v_a_944_);
lean_dec(v_optPrioStx_942_);
return v___x_954_;
}
else
{
lean_object* v_val_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_dec(v_optPrioStx_942_);
v_val_955_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_949_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_val_955_);
lean_dec(v___x_949_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set_tag(v___x_957_, 0);
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_val_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec(v_optPrioStx_942_);
v___x_963_ = lean_unsigned_to_nat(1000u);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object* v_optPrioStx_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_965_, v_a_966_, v_a_967_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
return v_res_969_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getPrio___closed__1(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = ((lean_object*)(l_Lean_Attribute_Builtin_getPrio___closed__0));
v___x_972_ = l_Lean_stringToMessageData(v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
lean_inc(v_stx_973_);
v___x_977_ = l_Lean_Syntax_getKind(v_stx_973_);
v___x_978_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_979_ = lean_name_eq(v___x_977_, v___x_978_);
lean_dec(v___x_977_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_980_ = lean_obj_once(&l_Lean_Attribute_Builtin_getPrio___closed__1, &l_Lean_Attribute_Builtin_getPrio___closed__1_once, _init_l_Lean_Attribute_Builtin_getPrio___closed__1);
lean_inc(v_stx_973_);
v___x_981_ = l_Lean_MessageData_ofSyntax(v_stx_973_);
v___x_982_ = l_Lean_indentD(v___x_981_);
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_980_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_973_, v___x_983_, v_a_974_, v_a_975_);
lean_dec(v_stx_973_);
return v___x_984_;
}
else
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_985_ = lean_unsigned_to_nat(1u);
v___x_986_ = l_Lean_Syntax_getArg(v_stx_973_, v___x_985_);
lean_dec(v_stx_973_);
v___x_987_ = l_Lean_getAttrParamOptPrio(v___x_986_, v_a_974_, v_a_975_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_Attribute_Builtin_getPrio(v_stx_988_, v_a_989_, v_a_990_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
return v_res_992_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_995_ = l_Lean_stringToMessageData(v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_998_ = l_Lean_stringToMessageData(v___x_997_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_1001_ = l_Lean_stringToMessageData(v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_1002_, lean_object* v_inst_1003_, lean_object* v_name_1004_, uint8_t v_kind_1005_){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___y_1012_; 
v___x_1006_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1007_ = l_Lean_MessageData_ofName(v_name_1004_);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
switch(v_kind_1005_)
{
case 0:
{
lean_object* v___x_1019_; 
v___x_1019_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1012_ = v___x_1019_;
goto v___jp_1011_;
}
case 1:
{
lean_object* v___x_1020_; 
v___x_1020_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1012_ = v___x_1020_;
goto v___jp_1011_;
}
default: 
{
lean_object* v___x_1021_; 
v___x_1021_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1012_ = v___x_1021_;
goto v___jp_1011_;
}
}
v___jp_1011_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_inc_ref(v___y_1012_);
v___x_1013_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___y_1012_);
v___x_1014_ = l_Lean_MessageData_ofFormat(v___x_1013_);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1010_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = l_Lean_throwError___redArg(v_inst_1002_, v_inst_1003_, v___x_1017_);
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_1022_, lean_object* v_inst_1023_, lean_object* v_name_1024_, lean_object* v_kind_1025_){
_start:
{
uint8_t v_kind_boxed_1026_; lean_object* v_res_1027_; 
v_kind_boxed_1026_ = lean_unbox(v_kind_1025_);
v_res_1027_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_1022_, v_inst_1023_, v_name_1024_, v_kind_boxed_1026_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_00_u03b1_1031_, lean_object* v_name_1032_, uint8_t v_kind_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_1029_, v_inst_1030_, v_name_1032_, v_kind_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_1035_, lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_00_u03b1_1038_, lean_object* v_name_1039_, lean_object* v_kind_1040_){
_start:
{
uint8_t v_kind_boxed_1041_; lean_object* v_res_1042_; 
v_kind_boxed_1041_ = lean_unbox(v_kind_1040_);
v_res_1042_ = l_Lean_throwAttrMustBeGlobal(v_m_1035_, v_inst_1036_, v_inst_1037_, v_00_u03b1_1038_, v_name_1039_, v_kind_boxed_1041_);
return v_res_1042_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_1045_ = l_Lean_stringToMessageData(v___x_1044_);
return v___x_1045_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_1048_ = l_Lean_stringToMessageData(v___x_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_1051_ = l_Lean_stringToMessageData(v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_attrName_1054_, lean_object* v_declName_1055_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1056_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1057_ = l_Lean_MessageData_ofName(v_attrName_1054_);
v___x_1058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = 0;
v___x_1062_ = l_Lean_MessageData_ofConstName(v_declName_1055_, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1060_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = l_Lean_throwError___redArg(v_inst_1052_, v_inst_1053_, v___x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1067_, lean_object* v_inst_1068_, lean_object* v_inst_1069_, lean_object* v_00_u03b1_1070_, lean_object* v_attrName_1071_, lean_object* v_declName_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1068_, v_inst_1069_, v_attrName_1071_, v_declName_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1076_ = l_Lean_stringToMessageData(v___x_1075_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1079_ = l_Lean_stringToMessageData(v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v_attrName_1082_, lean_object* v_declName_1083_, lean_object* v_asyncPrefix_x3f_1084_){
_start:
{
lean_object* v___y_1086_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1084_) == 0)
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_MessageData_nil;
v___y_1086_ = v___x_1099_;
goto v___jp_1085_;
}
else
{
lean_object* v_val_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_val_1100_ = lean_ctor_get(v_asyncPrefix_x3f_1084_, 0);
lean_inc(v_val_1100_);
lean_dec_ref_known(v_asyncPrefix_x3f_1084_, 1);
v___x_1101_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1102_ = l_Lean_MessageData_ofName(v_val_1100_);
v___x_1103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1103_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___y_1086_ = v___x_1105_;
goto v___jp_1085_;
}
v___jp_1085_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1087_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1088_ = l_Lean_MessageData_ofName(v_attrName_1082_);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = 0;
v___x_1093_ = l_Lean_MessageData_ofConstName(v_declName_1083_, v___x_1092_);
v___x_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1091_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
lean_ctor_set(v___x_1097_, 1, v___y_1086_);
v___x_1098_ = l_Lean_throwError___redArg(v_inst_1080_, v_inst_1081_, v___x_1097_);
return v___x_1098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1106_, lean_object* v_inst_1107_, lean_object* v_inst_1108_, lean_object* v_00_u03b1_1109_, lean_object* v_attrName_1110_, lean_object* v_declName_1111_, lean_object* v_asyncPrefix_x3f_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1107_, v_inst_1108_, v_attrName_1110_, v_declName_1111_, v_asyncPrefix_x3f_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1116_ = l_Lean_stringToMessageData(v___x_1115_);
return v___x_1116_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1119_ = l_Lean_stringToMessageData(v___x_1118_);
return v___x_1119_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1122_ = l_Lean_stringToMessageData(v___x_1121_);
return v___x_1122_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1125_ = l_Lean_stringToMessageData(v___x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_attrName_1128_, lean_object* v_declName_1129_, lean_object* v_givenType_1130_, lean_object* v_expectedType_1131_){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1132_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1133_ = l_Lean_MessageData_ofName(v_attrName_1128_);
lean_inc_ref(v___x_1133_);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = 0;
v___x_1138_ = l_Lean_MessageData_ofConstName(v_declName_1129_, v___x_1137_);
v___x_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1136_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1139_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = l_Lean_indentExpr(v_givenType_1130_);
v___x_1143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1141_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1143_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
lean_ctor_set(v___x_1146_, 1, v___x_1133_);
v___x_1147_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1146_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = l_Lean_indentExpr(v_expectedType_1131_);
v___x_1150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1148_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = l_Lean_throwError___redArg(v_inst_1126_, v_inst_1127_, v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1152_, lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v_00_u03b1_1155_, lean_object* v_attrName_1156_, lean_object* v_declName_1157_, lean_object* v_givenType_1158_, lean_object* v_expectedType_1159_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1153_, v_inst_1154_, v_attrName_1156_, v_declName_1157_, v_givenType_1158_, v_expectedType_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1161_, uint8_t v_skipRealize_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v___x_1165_; lean_object* v_env_1166_; uint8_t v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1165_ = lean_st_ref_get(v___y_1163_);
v_env_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc_ref(v_env_1166_);
lean_dec(v___x_1165_);
v___x_1167_ = l_Lean_Environment_contains(v_env_1166_, v_constName_1161_, v_skipRealize_1162_);
v___x_1168_ = lean_box(v___x_1167_);
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object* v_constName_1170_, lean_object* v_skipRealize_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
uint8_t v_skipRealize_boxed_1174_; lean_object* v_res_1175_; 
v_skipRealize_boxed_1174_ = lean_unbox(v_skipRealize_1171_);
v_res_1175_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1170_, v_skipRealize_boxed_1174_, v___y_1172_);
lean_dec(v___y_1172_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1176_, uint8_t v_skipRealize_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1176_, v_skipRealize_1177_, v___y_1179_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1182_, lean_object* v_skipRealize_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
uint8_t v_skipRealize_boxed_1187_; lean_object* v_res_1188_; 
v_skipRealize_boxed_1187_ = lean_unbox(v_skipRealize_1183_);
v_res_1188_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1182_, v_skipRealize_boxed_1187_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1189_, uint8_t v_isExporting_1190_, lean_object* v___x_1191_, lean_object* v_a_x3f_1192_){
_start:
{
lean_object* v___x_1194_; lean_object* v_env_1195_; lean_object* v_nextMacroScope_1196_; lean_object* v_ngen_1197_; lean_object* v_auxDeclNGen_1198_; lean_object* v_traceState_1199_; lean_object* v_recordedDeps_1200_; lean_object* v_messages_1201_; lean_object* v_infoState_1202_; lean_object* v_snapshotTasks_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1214_; 
v___x_1194_ = lean_st_ref_take(v___y_1189_);
v_env_1195_ = lean_ctor_get(v___x_1194_, 0);
v_nextMacroScope_1196_ = lean_ctor_get(v___x_1194_, 1);
v_ngen_1197_ = lean_ctor_get(v___x_1194_, 2);
v_auxDeclNGen_1198_ = lean_ctor_get(v___x_1194_, 3);
v_traceState_1199_ = lean_ctor_get(v___x_1194_, 4);
v_recordedDeps_1200_ = lean_ctor_get(v___x_1194_, 6);
v_messages_1201_ = lean_ctor_get(v___x_1194_, 7);
v_infoState_1202_ = lean_ctor_get(v___x_1194_, 8);
v_snapshotTasks_1203_ = lean_ctor_get(v___x_1194_, 9);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1214_ == 0)
{
lean_object* v_unused_1215_; 
v_unused_1215_ = lean_ctor_get(v___x_1194_, 5);
lean_dec(v_unused_1215_);
v___x_1205_ = v___x_1194_;
v_isShared_1206_ = v_isSharedCheck_1214_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_snapshotTasks_1203_);
lean_inc(v_infoState_1202_);
lean_inc(v_messages_1201_);
lean_inc(v_recordedDeps_1200_);
lean_inc(v_traceState_1199_);
lean_inc(v_auxDeclNGen_1198_);
lean_inc(v_ngen_1197_);
lean_inc(v_nextMacroScope_1196_);
lean_inc(v_env_1195_);
lean_dec(v___x_1194_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1214_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1207_ = lean_box(0);
v___x_1208_ = l_Lean_Environment_setExporting(v_env_1195_, v_isExporting_1190_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 5, v___x_1191_);
lean_ctor_set(v___x_1205_, 0, v___x_1208_);
v___x_1210_ = v___x_1205_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_nextMacroScope_1196_);
lean_ctor_set(v_reuseFailAlloc_1213_, 2, v_ngen_1197_);
lean_ctor_set(v_reuseFailAlloc_1213_, 3, v_auxDeclNGen_1198_);
lean_ctor_set(v_reuseFailAlloc_1213_, 4, v_traceState_1199_);
lean_ctor_set(v_reuseFailAlloc_1213_, 5, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1213_, 6, v_recordedDeps_1200_);
lean_ctor_set(v_reuseFailAlloc_1213_, 7, v_messages_1201_);
lean_ctor_set(v_reuseFailAlloc_1213_, 8, v_infoState_1202_);
lean_ctor_set(v_reuseFailAlloc_1213_, 9, v_snapshotTasks_1203_);
v___x_1210_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_st_ref_put(v___y_1189_, v___x_1210_);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1207_);
return v___x_1212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1216_, lean_object* v_isExporting_1217_, lean_object* v___x_1218_, lean_object* v_a_x3f_1219_, lean_object* v___y_1220_){
_start:
{
uint8_t v_isExporting_boxed_1221_; lean_object* v_res_1222_; 
v_isExporting_boxed_1221_ = lean_unbox(v_isExporting_1217_);
v_res_1222_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1216_, v_isExporting_boxed_1221_, v___x_1218_, v_a_x3f_1219_);
lean_dec(v_a_x3f_1219_);
lean_dec(v___y_1216_);
return v_res_1222_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1227_, uint8_t v_isExporting_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v___x_1232_; lean_object* v_env_1233_; lean_object* v___x_1234_; uint8_t v_isModule_1235_; 
v___x_1232_ = lean_st_ref_get(v___y_1230_);
v_env_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc_ref(v_env_1233_);
lean_dec(v___x_1232_);
v___x_1234_ = l_Lean_Environment_header(v_env_1233_);
v_isModule_1235_ = lean_ctor_get_uint8(v___x_1234_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1234_);
if (v_isModule_1235_ == 0)
{
lean_object* v___x_1236_; 
lean_dec_ref(v_env_1233_);
lean_inc(v___y_1230_);
lean_inc_ref(v___y_1229_);
v___x_1236_ = lean_apply_3(v_x_1227_, v___y_1229_, v___y_1230_, lean_box(0));
return v___x_1236_;
}
else
{
uint8_t v_isExporting_1237_; 
v_isExporting_1237_ = lean_ctor_get_uint8(v_env_1233_, sizeof(void*)*13);
lean_dec_ref(v_env_1233_);
if (v_isExporting_1228_ == 0)
{
if (v_isExporting_1237_ == 0)
{
lean_object* v___x_1289_; 
lean_inc(v___y_1230_);
lean_inc_ref(v___y_1229_);
v___x_1289_ = lean_apply_3(v_x_1227_, v___y_1229_, v___y_1230_, lean_box(0));
return v___x_1289_;
}
else
{
goto v___jp_1238_;
}
}
else
{
if (v_isExporting_1237_ == 0)
{
goto v___jp_1238_;
}
else
{
lean_object* v___x_1290_; 
lean_inc(v___y_1230_);
lean_inc_ref(v___y_1229_);
v___x_1290_ = lean_apply_3(v_x_1227_, v___y_1229_, v___y_1230_, lean_box(0));
return v___x_1290_;
}
}
v___jp_1238_:
{
lean_object* v___x_1239_; lean_object* v_env_1240_; lean_object* v_nextMacroScope_1241_; lean_object* v_ngen_1242_; lean_object* v_auxDeclNGen_1243_; lean_object* v_traceState_1244_; lean_object* v_recordedDeps_1245_; lean_object* v_messages_1246_; lean_object* v_infoState_1247_; lean_object* v_snapshotTasks_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1287_; 
v___x_1239_ = lean_st_ref_take(v___y_1230_);
v_env_1240_ = lean_ctor_get(v___x_1239_, 0);
v_nextMacroScope_1241_ = lean_ctor_get(v___x_1239_, 1);
v_ngen_1242_ = lean_ctor_get(v___x_1239_, 2);
v_auxDeclNGen_1243_ = lean_ctor_get(v___x_1239_, 3);
v_traceState_1244_ = lean_ctor_get(v___x_1239_, 4);
v_recordedDeps_1245_ = lean_ctor_get(v___x_1239_, 6);
v_messages_1246_ = lean_ctor_get(v___x_1239_, 7);
v_infoState_1247_ = lean_ctor_get(v___x_1239_, 8);
v_snapshotTasks_1248_ = lean_ctor_get(v___x_1239_, 9);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1287_ == 0)
{
lean_object* v_unused_1288_; 
v_unused_1288_ = lean_ctor_get(v___x_1239_, 5);
lean_dec(v_unused_1288_);
v___x_1250_ = v___x_1239_;
v_isShared_1251_ = v_isSharedCheck_1287_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_snapshotTasks_1248_);
lean_inc(v_infoState_1247_);
lean_inc(v_messages_1246_);
lean_inc(v_recordedDeps_1245_);
lean_inc(v_traceState_1244_);
lean_inc(v_auxDeclNGen_1243_);
lean_inc(v_ngen_1242_);
lean_inc(v_nextMacroScope_1241_);
lean_inc(v_env_1240_);
lean_dec(v___x_1239_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1287_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1252_ = l_Lean_Environment_setExporting(v_env_1240_, v_isExporting_1228_);
v___x_1253_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 5, v___x_1253_);
lean_ctor_set(v___x_1250_, 0, v___x_1252_);
v___x_1255_ = v___x_1250_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_nextMacroScope_1241_);
lean_ctor_set(v_reuseFailAlloc_1286_, 2, v_ngen_1242_);
lean_ctor_set(v_reuseFailAlloc_1286_, 3, v_auxDeclNGen_1243_);
lean_ctor_set(v_reuseFailAlloc_1286_, 4, v_traceState_1244_);
lean_ctor_set(v_reuseFailAlloc_1286_, 5, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1286_, 6, v_recordedDeps_1245_);
lean_ctor_set(v_reuseFailAlloc_1286_, 7, v_messages_1246_);
lean_ctor_set(v_reuseFailAlloc_1286_, 8, v_infoState_1247_);
lean_ctor_set(v_reuseFailAlloc_1286_, 9, v_snapshotTasks_1248_);
v___x_1255_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; lean_object* v_r_1257_; 
v___x_1256_ = lean_st_ref_put(v___y_1230_, v___x_1255_);
lean_inc(v___y_1230_);
lean_inc_ref(v___y_1229_);
v_r_1257_ = lean_apply_3(v_x_1227_, v___y_1229_, v___y_1230_, lean_box(0));
if (lean_obj_tag(v_r_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1274_; 
v_a_1258_ = lean_ctor_get(v_r_1257_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_r_1257_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1260_ = v_r_1257_;
v_isShared_1261_ = v_isSharedCheck_1274_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v_r_1257_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1274_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
lean_inc(v_a_1258_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set_tag(v___x_1260_, 1);
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
v___x_1264_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1230_, v_isExporting_1237_, v___x_1253_, v___x_1263_);
lean_dec_ref(v___x_1263_);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1271_ == 0)
{
lean_object* v_unused_1272_; 
v_unused_1272_ = lean_ctor_get(v___x_1264_, 0);
lean_dec(v_unused_1272_);
v___x_1266_ = v___x_1264_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_dec(v___x_1264_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v_a_1258_);
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1258_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
v_a_1275_ = lean_ctor_get(v_r_1257_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v_r_1257_, 1);
v___x_1276_ = lean_box(0);
v___x_1277_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1230_, v_isExporting_1237_, v___x_1253_, v___x_1276_);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1284_ == 0)
{
lean_object* v_unused_1285_; 
v_unused_1285_ = lean_ctor_get(v___x_1277_, 0);
lean_dec(v_unused_1285_);
v___x_1279_ = v___x_1277_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_dec(v___x_1277_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set_tag(v___x_1279_, 1);
lean_ctor_set(v___x_1279_, 0, v_a_1275_);
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1275_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1291_, lean_object* v_isExporting_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
uint8_t v_isExporting_boxed_1296_; lean_object* v_res_1297_; 
v_isExporting_boxed_1296_ = lean_unbox(v_isExporting_1292_);
v_res_1297_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1291_, v_isExporting_boxed_1296_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1298_, lean_object* v_x_1299_, uint8_t v_isExporting_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1299_, v_isExporting_1300_, v___y_1301_, v___y_1302_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1305_, lean_object* v_x_1306_, lean_object* v_isExporting_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
uint8_t v_isExporting_boxed_1311_; lean_object* v_res_1312_; 
v_isExporting_boxed_1311_ = lean_unbox(v_isExporting_1307_);
v_res_1312_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1305_, v_x_1306_, v_isExporting_boxed_1311_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
return v_res_1312_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1313_, lean_object* v_opt_1314_){
_start:
{
lean_object* v_name_1315_; lean_object* v_defValue_1316_; lean_object* v_map_1317_; lean_object* v___x_1318_; 
v_name_1315_ = lean_ctor_get(v_opt_1314_, 0);
v_defValue_1316_ = lean_ctor_get(v_opt_1314_, 1);
v_map_1317_ = lean_ctor_get(v_opts_1313_, 0);
v___x_1318_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1317_, v_name_1315_);
if (lean_obj_tag(v___x_1318_) == 0)
{
uint8_t v___x_1319_; 
v___x_1319_ = lean_unbox(v_defValue_1316_);
return v___x_1319_;
}
else
{
lean_object* v_val_1320_; 
v_val_1320_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_val_1320_);
lean_dec_ref_known(v___x_1318_, 1);
if (lean_obj_tag(v_val_1320_) == 1)
{
uint8_t v_v_1321_; 
v_v_1321_ = lean_ctor_get_uint8(v_val_1320_, 0);
lean_dec_ref_known(v_val_1320_, 0);
return v_v_1321_;
}
else
{
uint8_t v___x_1322_; 
lean_dec(v_val_1320_);
v___x_1322_ = lean_unbox(v_defValue_1316_);
return v___x_1322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1323_, lean_object* v_opt_1324_){
_start:
{
uint8_t v_res_1325_; lean_object* v_r_1326_; 
v_res_1325_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1323_, v_opt_1324_);
lean_dec_ref(v_opt_1324_);
lean_dec_ref(v_opts_1323_);
v_r_1326_ = lean_box(v_res_1325_);
return v_r_1326_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_1334_, lean_object* v_x_1335_){
_start:
{
if (lean_obj_tag(v_x_1335_) == 1)
{
lean_object* v_pre_1336_; 
v_pre_1336_ = lean_ctor_get(v_x_1335_, 0);
switch(lean_obj_tag(v_pre_1336_))
{
case 1:
{
lean_object* v_pre_1337_; 
v_pre_1337_ = lean_ctor_get(v_pre_1336_, 0);
switch(lean_obj_tag(v_pre_1337_))
{
case 0:
{
lean_object* v_str_1338_; lean_object* v_str_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v_str_1338_ = lean_ctor_get(v_x_1335_, 1);
v_str_1339_ = lean_ctor_get(v_pre_1336_, 1);
v___x_1340_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1341_ = lean_string_dec_eq(v_str_1339_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; uint8_t v___x_1343_; 
v___x_1342_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1343_ = lean_string_dec_eq(v_str_1339_, v___x_1342_);
if (v___x_1343_ == 0)
{
return v___x_1343_;
}
else
{
lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1344_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1345_ = lean_string_dec_eq(v_str_1338_, v___x_1344_);
if (v___x_1345_ == 0)
{
return v___x_1345_;
}
else
{
return v_suppressElabErrors_1334_;
}
}
}
else
{
lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1346_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1347_ = lean_string_dec_eq(v_str_1338_, v___x_1346_);
if (v___x_1347_ == 0)
{
return v___x_1347_;
}
else
{
return v_suppressElabErrors_1334_;
}
}
}
case 1:
{
lean_object* v_pre_1348_; 
v_pre_1348_ = lean_ctor_get(v_pre_1337_, 0);
if (lean_obj_tag(v_pre_1348_) == 0)
{
lean_object* v_str_1349_; lean_object* v_str_1350_; lean_object* v_str_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v_str_1349_ = lean_ctor_get(v_x_1335_, 1);
v_str_1350_ = lean_ctor_get(v_pre_1336_, 1);
v_str_1351_ = lean_ctor_get(v_pre_1337_, 1);
v___x_1352_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1353_ = lean_string_dec_eq(v_str_1351_, v___x_1352_);
if (v___x_1353_ == 0)
{
return v___x_1353_;
}
else
{
lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1354_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1355_ = lean_string_dec_eq(v_str_1350_, v___x_1354_);
if (v___x_1355_ == 0)
{
return v___x_1355_;
}
else
{
lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1356_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1357_ = lean_string_dec_eq(v_str_1349_, v___x_1356_);
if (v___x_1357_ == 0)
{
return v___x_1357_;
}
else
{
return v_suppressElabErrors_1334_;
}
}
}
}
else
{
uint8_t v___x_1358_; 
v___x_1358_ = 0;
return v___x_1358_;
}
}
default: 
{
uint8_t v___x_1359_; 
v___x_1359_ = 0;
return v___x_1359_;
}
}
}
case 0:
{
lean_object* v_str_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v_str_1360_ = lean_ctor_get(v_x_1335_, 1);
v___x_1361_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1362_ = lean_string_dec_eq(v_str_1360_, v___x_1361_);
if (v___x_1362_ == 0)
{
return v___x_1362_;
}
else
{
return v_suppressElabErrors_1334_;
}
}
default: 
{
uint8_t v___x_1363_; 
v___x_1363_ = 0;
return v___x_1363_;
}
}
}
else
{
uint8_t v___x_1364_; 
v___x_1364_ = 0;
return v___x_1364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_1365_, lean_object* v_x_1366_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1367_; uint8_t v_res_1368_; lean_object* v_r_1369_; 
v_suppressElabErrors_boxed_1367_ = lean_unbox(v_suppressElabErrors_1365_);
v_res_1368_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_1367_, v_x_1366_);
lean_dec(v_x_1366_);
v_r_1369_ = lean_box(v_res_1368_);
return v_r_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1370_, lean_object* v_msgData_1371_, uint8_t v_severity_1372_, uint8_t v_isSilent_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v___y_1378_; lean_object* v___y_1379_; uint8_t v___y_1380_; lean_object* v___y_1381_; uint8_t v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v_toCold_1385_; lean_object* v___y_1386_; lean_object* v___y_1415_; lean_object* v___y_1416_; uint8_t v___y_1417_; uint8_t v___y_1418_; uint8_t v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; uint8_t v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; uint8_t v___y_1446_; uint8_t v___y_1447_; lean_object* v___y_1448_; uint8_t v___y_1452_; uint8_t v___y_1453_; uint8_t v___x_1463_; uint8_t v___y_1465_; uint8_t v___x_1471_; 
v___x_1463_ = 2;
v___x_1471_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1372_, v___x_1463_);
if (v___x_1471_ == 0)
{
v___y_1465_ = v___x_1471_;
goto v___jp_1464_;
}
else
{
uint8_t v___x_1472_; 
lean_inc_ref(v_msgData_1371_);
v___x_1472_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1371_);
if (v___x_1472_ == 0)
{
v___y_1465_ = v___x_1472_;
goto v___jp_1464_;
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_dec_ref(v_msgData_1371_);
v___x_1473_ = lean_box(0);
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
return v___x_1474_;
}
}
v___jp_1377_:
{
lean_object* v_currNamespace_1387_; lean_object* v_openDecls_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v_env_1393_; lean_object* v_nextMacroScope_1394_; lean_object* v_ngen_1395_; lean_object* v_auxDeclNGen_1396_; lean_object* v_traceState_1397_; lean_object* v_cache_1398_; lean_object* v_recordedDeps_1399_; lean_object* v_messages_1400_; lean_object* v_infoState_1401_; lean_object* v_snapshotTasks_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1413_; 
v_currNamespace_1387_ = lean_ctor_get(v_toCold_1385_, 4);
v_openDecls_1388_ = lean_ctor_get(v_toCold_1385_, 5);
lean_inc(v_openDecls_1388_);
lean_inc(v_currNamespace_1387_);
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v_currNamespace_1387_);
lean_ctor_set(v___x_1389_, 1, v_openDecls_1388_);
v___x_1390_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
lean_ctor_set(v___x_1390_, 1, v___y_1383_);
lean_inc_ref(v___y_1384_);
lean_inc_ref(v___y_1379_);
v___x_1391_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1391_, 0, v___y_1379_);
lean_ctor_set(v___x_1391_, 1, v___y_1381_);
lean_ctor_set(v___x_1391_, 2, v___y_1378_);
lean_ctor_set(v___x_1391_, 3, v___y_1384_);
lean_ctor_set(v___x_1391_, 4, v___x_1390_);
lean_ctor_set_uint8(v___x_1391_, sizeof(void*)*5, v___y_1380_);
lean_ctor_set_uint8(v___x_1391_, sizeof(void*)*5 + 1, v___y_1382_);
lean_ctor_set_uint8(v___x_1391_, sizeof(void*)*5 + 2, v_isSilent_1373_);
v___x_1392_ = lean_st_ref_take(v___y_1386_);
v_env_1393_ = lean_ctor_get(v___x_1392_, 0);
v_nextMacroScope_1394_ = lean_ctor_get(v___x_1392_, 1);
v_ngen_1395_ = lean_ctor_get(v___x_1392_, 2);
v_auxDeclNGen_1396_ = lean_ctor_get(v___x_1392_, 3);
v_traceState_1397_ = lean_ctor_get(v___x_1392_, 4);
v_cache_1398_ = lean_ctor_get(v___x_1392_, 5);
v_recordedDeps_1399_ = lean_ctor_get(v___x_1392_, 6);
v_messages_1400_ = lean_ctor_get(v___x_1392_, 7);
v_infoState_1401_ = lean_ctor_get(v___x_1392_, 8);
v_snapshotTasks_1402_ = lean_ctor_get(v___x_1392_, 9);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1404_ = v___x_1392_;
v_isShared_1405_ = v_isSharedCheck_1413_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_snapshotTasks_1402_);
lean_inc(v_infoState_1401_);
lean_inc(v_messages_1400_);
lean_inc(v_recordedDeps_1399_);
lean_inc(v_cache_1398_);
lean_inc(v_traceState_1397_);
lean_inc(v_auxDeclNGen_1396_);
lean_inc(v_ngen_1395_);
lean_inc(v_nextMacroScope_1394_);
lean_inc(v_env_1393_);
lean_dec(v___x_1392_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1413_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1406_ = lean_box(0);
v___x_1407_ = l_Lean_MessageLog_add(v___x_1391_, v_messages_1400_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 7, v___x_1407_);
v___x_1409_ = v___x_1404_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_env_1393_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_nextMacroScope_1394_);
lean_ctor_set(v_reuseFailAlloc_1412_, 2, v_ngen_1395_);
lean_ctor_set(v_reuseFailAlloc_1412_, 3, v_auxDeclNGen_1396_);
lean_ctor_set(v_reuseFailAlloc_1412_, 4, v_traceState_1397_);
lean_ctor_set(v_reuseFailAlloc_1412_, 5, v_cache_1398_);
lean_ctor_set(v_reuseFailAlloc_1412_, 6, v_recordedDeps_1399_);
lean_ctor_set(v_reuseFailAlloc_1412_, 7, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1412_, 8, v_infoState_1401_);
lean_ctor_set(v_reuseFailAlloc_1412_, 9, v_snapshotTasks_1402_);
v___x_1409_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = lean_st_ref_put(v___y_1386_, v___x_1409_);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1406_);
return v___x_1411_;
}
}
}
v___jp_1414_:
{
lean_object* v_fileName_1423_; lean_object* v_fileMap_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1440_; 
v_fileName_1423_ = lean_ctor_get(v___y_1421_, 0);
v_fileMap_1424_ = lean_ctor_get(v___y_1421_, 1);
v___x_1425_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1371_);
v___x_1426_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v___x_1425_, v___y_1374_, v___y_1375_);
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1429_ = v___x_1426_;
v_isShared_1430_ = v_isSharedCheck_1440_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1440_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_inc_ref_n(v_fileMap_1424_, 2);
v___x_1431_ = l_Lean_FileMap_toPosition(v_fileMap_1424_, v___y_1420_);
lean_dec(v___y_1420_);
v___x_1432_ = l_Lean_FileMap_toPosition(v_fileMap_1424_, v___y_1422_);
lean_dec(v___y_1422_);
v___x_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
v___x_1434_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1417_ == 0)
{
lean_del_object(v___x_1429_);
lean_dec_ref(v___y_1415_);
v___y_1378_ = v___x_1433_;
v___y_1379_ = v_fileName_1423_;
v___y_1380_ = v___y_1418_;
v___y_1381_ = v___x_1431_;
v___y_1382_ = v___y_1419_;
v___y_1383_ = v_a_1427_;
v___y_1384_ = v___x_1434_;
v_toCold_1385_ = v___y_1416_;
v___y_1386_ = v___y_1375_;
goto v___jp_1377_;
}
else
{
uint8_t v___x_1435_; 
lean_inc(v_a_1427_);
v___x_1435_ = l_Lean_MessageData_hasTag(v___y_1415_, v_a_1427_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
lean_dec_ref_known(v___x_1433_, 1);
lean_dec_ref(v___x_1431_);
lean_dec(v_a_1427_);
v___x_1436_ = lean_box(0);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v___x_1436_);
v___x_1438_ = v___x_1429_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
else
{
lean_del_object(v___x_1429_);
v___y_1378_ = v___x_1433_;
v___y_1379_ = v_fileName_1423_;
v___y_1380_ = v___y_1418_;
v___y_1381_ = v___x_1431_;
v___y_1382_ = v___y_1419_;
v___y_1383_ = v_a_1427_;
v___y_1384_ = v___x_1434_;
v_toCold_1385_ = v___y_1416_;
v___y_1386_ = v___y_1375_;
goto v___jp_1377_;
}
}
}
}
v___jp_1441_:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_Syntax_getTailPos_x3f(v___y_1445_, v___y_1446_);
lean_dec(v___y_1445_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_inc(v___y_1448_);
v___y_1415_ = v___y_1443_;
v___y_1416_ = v___y_1444_;
v___y_1417_ = v___y_1442_;
v___y_1418_ = v___y_1446_;
v___y_1419_ = v___y_1447_;
v___y_1420_ = v___y_1448_;
v___y_1421_ = v___y_1444_;
v___y_1422_ = v___y_1448_;
goto v___jp_1414_;
}
else
{
lean_object* v_val_1450_; 
v_val_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_val_1450_);
lean_dec_ref_known(v___x_1449_, 1);
v___y_1415_ = v___y_1443_;
v___y_1416_ = v___y_1444_;
v___y_1417_ = v___y_1442_;
v___y_1418_ = v___y_1446_;
v___y_1419_ = v___y_1447_;
v___y_1420_ = v___y_1448_;
v___y_1421_ = v___y_1444_;
v___y_1422_ = v_val_1450_;
goto v___jp_1414_;
}
}
v___jp_1451_:
{
lean_object* v_toCold_1454_; lean_object* v_ref_1455_; uint8_t v_suppressElabErrors_1456_; lean_object* v___x_1457_; lean_object* v___f_1458_; lean_object* v_ref_1459_; lean_object* v___x_1460_; 
v_toCold_1454_ = lean_ctor_get(v___y_1374_, 0);
v_ref_1455_ = lean_ctor_get(v___y_1374_, 2);
v_suppressElabErrors_1456_ = lean_ctor_get_uint8(v___y_1374_, sizeof(void*)*3 + 2);
v___x_1457_ = lean_box(v_suppressElabErrors_1456_);
v___f_1458_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1458_, 0, v___x_1457_);
v_ref_1459_ = l_Lean_replaceRef(v_ref_1370_, v_ref_1455_);
v___x_1460_ = l_Lean_Syntax_getPos_x3f(v_ref_1459_, v___y_1452_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_unsigned_to_nat(0u);
v___y_1442_ = v_suppressElabErrors_1456_;
v___y_1443_ = v___f_1458_;
v___y_1444_ = v_toCold_1454_;
v___y_1445_ = v_ref_1459_;
v___y_1446_ = v___y_1452_;
v___y_1447_ = v___y_1453_;
v___y_1448_ = v___x_1461_;
goto v___jp_1441_;
}
else
{
lean_object* v_val_1462_; 
v_val_1462_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_val_1462_);
lean_dec_ref_known(v___x_1460_, 1);
v___y_1442_ = v_suppressElabErrors_1456_;
v___y_1443_ = v___f_1458_;
v___y_1444_ = v_toCold_1454_;
v___y_1445_ = v_ref_1459_;
v___y_1446_ = v___y_1452_;
v___y_1447_ = v___y_1453_;
v___y_1448_ = v_val_1462_;
goto v___jp_1441_;
}
}
v___jp_1464_:
{
uint8_t v___x_1466_; uint8_t v___x_1467_; 
v___x_1466_ = 1;
v___x_1467_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1372_, v___x_1466_);
if (v___x_1467_ == 0)
{
v___y_1452_ = v___y_1465_;
v___y_1453_ = v_severity_1372_;
goto v___jp_1451_;
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1468_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1374_);
v___x_1469_ = l_Lean_warningAsError;
v___x_1470_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v___x_1468_, v___x_1469_);
lean_dec_ref(v___x_1468_);
if (v___x_1470_ == 0)
{
v___y_1452_ = v___y_1465_;
v___y_1453_ = v_severity_1372_;
goto v___jp_1451_;
}
else
{
v___y_1452_ = v___y_1465_;
v___y_1453_ = v___x_1463_;
goto v___jp_1451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1475_, lean_object* v_msgData_1476_, lean_object* v_severity_1477_, lean_object* v_isSilent_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
uint8_t v_severity_boxed_1482_; uint8_t v_isSilent_boxed_1483_; lean_object* v_res_1484_; 
v_severity_boxed_1482_ = lean_unbox(v_severity_1477_);
v_isSilent_boxed_1483_ = lean_unbox(v_isSilent_1478_);
v_res_1484_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1475_, v_msgData_1476_, v_severity_boxed_1482_, v_isSilent_boxed_1483_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v_ref_1475_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1485_, uint8_t v_severity_1486_, uint8_t v_isSilent_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_ref_1491_; lean_object* v___x_1492_; 
v_ref_1491_ = lean_ctor_get(v___y_1488_, 2);
v___x_1492_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1491_, v_msgData_1485_, v_severity_1486_, v_isSilent_1487_, v___y_1488_, v___y_1489_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1493_, lean_object* v_severity_1494_, lean_object* v_isSilent_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
uint8_t v_severity_boxed_1499_; uint8_t v_isSilent_boxed_1500_; lean_object* v_res_1501_; 
v_severity_boxed_1499_ = lean_unbox(v_severity_1494_);
v_isSilent_boxed_1500_ = lean_unbox(v_isSilent_1495_);
v_res_1501_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1493_, v_severity_boxed_1499_, v_isSilent_boxed_1500_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
uint8_t v___x_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = 1;
v___x_1507_ = 0;
v___x_1508_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1502_, v___x_1506_, v___x_1507_, v___y_1503_, v___y_1504_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v___x_1517_; uint8_t v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1517_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1515_);
v___x_1518_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v___x_1517_, v_opt_1514_);
lean_dec_ref(v___x_1517_);
v___x_1519_ = lean_box(v___x_1518_);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1521_, v___y_1522_);
lean_dec_ref(v___y_1522_);
lean_dec_ref(v_opt_1521_);
return v_res_1524_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1527_ = l_Lean_stringToMessageData(v___x_1526_);
return v___x_1527_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1530_ = l_Lean_stringToMessageData(v___x_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v___x_1535_; lean_object* v_env_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1558_; 
v___x_1535_ = lean_st_ref_get(v___y_1533_);
v_env_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc_ref(v_env_1536_);
lean_dec(v___x_1535_);
v___x_1537_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1538_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1537_, v___y_1532_);
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1558_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1558_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
uint8_t v_isExporting_1548_; 
v_isExporting_1548_ = lean_ctor_get_uint8(v_env_1536_, sizeof(void*)*13);
lean_dec_ref(v_env_1536_);
if (v_isExporting_1548_ == 0)
{
lean_dec(v_a_1539_);
lean_dec(v_id_1531_);
goto v___jp_1543_;
}
else
{
uint8_t v___x_1549_; 
v___x_1549_ = l_Lean_isPrivateName(v_id_1531_);
if (v___x_1549_ == 0)
{
lean_dec(v_a_1539_);
lean_dec(v_id_1531_);
goto v___jp_1543_;
}
else
{
uint8_t v___x_1550_; 
v___x_1550_ = lean_unbox(v_a_1539_);
lean_dec(v_a_1539_);
if (v___x_1550_ == 0)
{
lean_dec(v_id_1531_);
goto v___jp_1543_;
}
else
{
lean_object* v___x_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_del_object(v___x_1541_);
v___x_1551_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1552_ = 0;
v___x_1553_ = l_Lean_MessageData_ofConstName(v_id_1531_, v___x_1552_);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1551_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1556_, v___y_1532_, v___y_1533_);
return v___x_1557_;
}
}
}
v___jp_1543_:
{
lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1544_ = lean_box(0);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1544_);
v___x_1546_ = v___x_1541_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1544_);
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
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
return v_res_1563_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1566_ = l_Lean_stringToMessageData(v___x_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1567_, uint8_t v_isModule_1568_, lean_object* v_attrName_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___x_1573_; 
lean_inc(v_declName_1567_);
v___x_1573_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1567_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v___x_1574_; lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1595_; 
lean_dec_ref_known(v___x_1573_, 1);
lean_inc(v_declName_1567_);
v___x_1574_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1567_, v_isModule_1568_, v___y_1571_);
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1577_ = v___x_1574_;
v_isShared_1578_ = v_isSharedCheck_1595_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1574_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1595_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
uint8_t v___x_1579_; 
v___x_1579_ = lean_unbox(v_a_1575_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_del_object(v___x_1577_);
v___x_1580_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1581_ = l_Lean_MessageData_ofName(v_attrName_1569_);
v___x_1582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1580_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = lean_unbox(v_a_1575_);
lean_dec(v_a_1575_);
v___x_1586_ = l_Lean_MessageData_ofConstName(v_declName_1567_, v___x_1585_);
v___x_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1584_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1589_, v___y_1570_, v___y_1571_);
return v___x_1590_;
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1593_; 
lean_dec(v_a_1575_);
lean_dec(v_attrName_1569_);
lean_dec(v_declName_1567_);
v___x_1591_ = lean_box(0);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v___x_1591_);
v___x_1593_ = v___x_1577_;
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
lean_dec(v_attrName_1569_);
lean_dec(v_declName_1567_);
return v___x_1573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1596_, lean_object* v_isModule_1597_, lean_object* v_attrName_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
uint8_t v_isModule_boxed_1602_; lean_object* v_res_1603_; 
v_isModule_boxed_1602_ = lean_unbox(v_isModule_1597_);
v_res_1603_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1596_, v_isModule_boxed_1602_, v_attrName_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1604_, lean_object* v_declName_1605_, uint8_t v_attrKind_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v___x_1610_; lean_object* v_env_1614_; lean_object* v___x_1615_; uint8_t v_isModule_1616_; 
v___x_1610_ = lean_st_ref_get(v_a_1608_);
v_env_1614_ = lean_ctor_get(v___x_1610_, 0);
lean_inc_ref(v_env_1614_);
lean_dec(v___x_1610_);
v___x_1615_ = l_Lean_Environment_header(v_env_1614_);
lean_dec_ref(v_env_1614_);
v_isModule_1616_ = lean_ctor_get_uint8(v___x_1615_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1615_);
if (v_isModule_1616_ == 0)
{
lean_dec(v_declName_1605_);
lean_dec(v_attrName_1604_);
goto v___jp_1611_;
}
else
{
uint8_t v___x_1617_; uint8_t v___x_1618_; 
v___x_1617_ = 1;
v___x_1618_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1606_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; lean_object* v___f_1620_; lean_object* v___x_1621_; 
v___x_1619_ = lean_box(v_isModule_1616_);
v___f_1620_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1620_, 0, v_declName_1605_);
lean_closure_set(v___f_1620_, 1, v___x_1619_);
lean_closure_set(v___f_1620_, 2, v_attrName_1604_);
v___x_1621_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1620_, v_isModule_1616_, v_a_1607_, v_a_1608_);
return v___x_1621_;
}
else
{
lean_dec(v_declName_1605_);
lean_dec(v_attrName_1604_);
goto v___jp_1611_;
}
}
v___jp_1611_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = lean_box(0);
v___x_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
return v___x_1613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1622_, lean_object* v_declName_1623_, lean_object* v_attrKind_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_){
_start:
{
uint8_t v_attrKind_boxed_1628_; lean_object* v_res_1629_; 
v_attrKind_boxed_1628_ = lean_unbox(v_attrKind_1624_);
v_res_1629_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1622_, v_declName_1623_, v_attrKind_boxed_1628_, v_a_1625_, v_a_1626_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1630_, v___y_1631_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec_ref(v_opt_1635_);
return v_res_1639_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1642_ = l_Lean_stringToMessageData(v___x_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1643_, lean_object* v_declName_1644_, uint8_t v_attrKind_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v___x_1649_; lean_object* v_env_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v_isModule_1653_; 
v___x_1649_ = lean_st_ref_get(v_a_1647_);
v_env_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc_ref(v_env_1650_);
lean_dec(v___x_1649_);
v___x_1651_ = lean_st_ref_get(v_a_1647_);
v___x_1652_ = l_Lean_Environment_header(v_env_1650_);
lean_dec_ref(v_env_1650_);
v_isModule_1653_ = lean_ctor_get_uint8(v___x_1652_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1652_);
if (v_isModule_1653_ == 0)
{
lean_object* v___x_1654_; 
lean_dec(v___x_1651_);
v___x_1654_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1643_, v_declName_1644_, v_attrKind_1645_, v_a_1646_, v_a_1647_);
return v___x_1654_;
}
else
{
lean_object* v_env_1655_; uint8_t v___x_1656_; 
v_env_1655_ = lean_ctor_get(v___x_1651_, 0);
lean_inc_ref(v_env_1655_);
lean_dec(v___x_1651_);
lean_inc(v_declName_1644_);
v___x_1656_ = l_Lean_isMarkedMeta(v_env_1655_, v_declName_1644_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1657_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1658_ = l_Lean_MessageData_ofName(v_attrName_1643_);
v___x_1659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1657_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
v___x_1660_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1659_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
v___x_1662_ = l_Lean_MessageData_ofConstName(v_declName_1644_, v___x_1656_);
v___x_1663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1661_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1665_, v_a_1646_, v_a_1647_);
return v___x_1666_;
}
else
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1643_, v_declName_1644_, v_attrKind_1645_, v_a_1646_, v_a_1647_);
return v___x_1667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1668_, lean_object* v_declName_1669_, lean_object* v_attrKind_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
uint8_t v_attrKind_boxed_1674_; lean_object* v_res_1675_; 
v_attrKind_boxed_1674_ = lean_unbox(v_attrKind_1670_);
v_res_1675_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1668_, v_declName_1669_, v_attrKind_boxed_1674_, v_a_1671_, v_a_1672_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1684_, v___y_1685_);
lean_dec_ref(v___y_1685_);
lean_dec_ref(v_x_1684_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1688_, lean_object* v_x_1689_){
_start:
{
lean_inc(v_s_1688_);
return v_s_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1690_, lean_object* v_x_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1690_, v_x_1691_);
lean_dec(v_x_1691_);
lean_dec(v_s_1690_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1697_, lean_object* v_x_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1700_, lean_object* v_x_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1700_, v_x_1701_);
lean_dec(v_x_1701_);
lean_dec_ref(v_x_1700_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1703_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_box(0);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1705_);
lean_dec(v_x_1705_);
return v_res_1706_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_1711_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1712_; lean_object* v___f_1713_; lean_object* v___f_1714_; lean_object* v___f_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___f_1712_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1713_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1714_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1715_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1716_ = lean_box(0);
v___x_1717_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1718_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
lean_ctor_set(v___x_1718_, 1, v___x_1716_);
lean_ctor_set(v___x_1718_, 2, v___f_1715_);
lean_ctor_set(v___x_1718_, 3, v___f_1714_);
lean_ctor_set(v___x_1718_, 4, v___f_1713_);
lean_ctor_set(v___x_1718_, 5, v___f_1712_);
return v___x_1718_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1720_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
lean_ctor_set(v___x_1721_, 1, v___x_1719_);
return v___x_1721_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1722_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1723_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lean_registerTagAttribute___lam__0(v_x_1727_);
lean_dec(v_x_1727_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1729_, lean_object* v_x_1730_, lean_object* v_x_1731_){
_start:
{
if (lean_obj_tag(v_x_1731_) == 0)
{
return v_x_1730_;
}
else
{
lean_object* v_head_1732_; lean_object* v_tail_1733_; uint8_t v___x_1734_; 
v_head_1732_ = lean_ctor_get(v_x_1731_, 0);
lean_inc(v_head_1732_);
v_tail_1733_ = lean_ctor_get(v_x_1731_, 1);
lean_inc(v_tail_1733_);
lean_dec_ref_known(v_x_1731_, 2);
v___x_1734_ = l_Lean_NameSet_contains(v_newState_1729_, v_head_1732_);
if (v___x_1734_ == 0)
{
lean_dec(v_head_1732_);
v_x_1731_ = v_tail_1733_;
goto _start;
}
else
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Lean_NameSet_insert(v_x_1730_, v_head_1732_);
v_x_1730_ = v___x_1736_;
v_x_1731_ = v_tail_1733_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1738_, lean_object* v_x_1739_, lean_object* v_x_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1738_, v_x_1739_, v_x_1740_);
lean_dec(v_newState_1738_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1742_, lean_object* v_newState_1743_, lean_object* v_newConsts_1744_, lean_object* v_s_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1743_, v_s_1745_, v_newConsts_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1747_, lean_object* v_newState_1748_, lean_object* v_newConsts_1749_, lean_object* v_s_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_registerTagAttribute___lam__1(v_x_1747_, v_newState_1748_, v_newConsts_1749_, v_s_1750_);
lean_dec(v_newState_1748_);
lean_dec(v_x_1747_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1764_){
_start:
{
lean_object* v___x_1765_; lean_object* v___y_1767_; 
v___x_1765_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1764_) == 0)
{
lean_object* v_size_1771_; 
v_size_1771_ = lean_ctor_get(v_s_1764_, 0);
lean_inc(v_size_1771_);
lean_dec_ref_known(v_s_1764_, 5);
v___y_1767_ = v_size_1771_;
goto v___jp_1766_;
}
else
{
lean_object* v___x_1772_; 
v___x_1772_ = lean_unsigned_to_nat(0u);
v___y_1767_ = v___x_1772_;
goto v___jp_1766_;
}
v___jp_1766_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1768_ = l_Nat_reprFast(v___y_1767_);
v___x_1769_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
v___x_1770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1765_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
return v___x_1770_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1773_, lean_object* v_pivot_1774_, lean_object* v_as_1775_, lean_object* v_i_1776_, lean_object* v_k_1777_){
_start:
{
uint8_t v___x_1778_; 
v___x_1778_ = lean_nat_dec_lt(v_k_1777_, v_hi_1773_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec(v_k_1777_);
v___x_1779_ = lean_array_fswap(v_as_1775_, v_i_1776_, v_hi_1773_);
v___x_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1780_, 0, v_i_1776_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
return v___x_1780_;
}
else
{
lean_object* v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = lean_array_fget_borrowed(v_as_1775_, v_k_1777_);
v___x_1782_ = l_Lean_Name_quickLt(v___x_1781_, v_pivot_1774_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = lean_unsigned_to_nat(1u);
v___x_1784_ = lean_nat_add(v_k_1777_, v___x_1783_);
lean_dec(v_k_1777_);
v_k_1777_ = v___x_1784_;
goto _start;
}
else
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1786_ = lean_array_fswap(v_as_1775_, v_i_1776_, v_k_1777_);
v___x_1787_ = lean_unsigned_to_nat(1u);
v___x_1788_ = lean_nat_add(v_i_1776_, v___x_1787_);
lean_dec(v_i_1776_);
v___x_1789_ = lean_nat_add(v_k_1777_, v___x_1787_);
lean_dec(v_k_1777_);
v_as_1775_ = v___x_1786_;
v_i_1776_ = v___x_1788_;
v_k_1777_ = v___x_1789_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1791_, lean_object* v_pivot_1792_, lean_object* v_as_1793_, lean_object* v_i_1794_, lean_object* v_k_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1791_, v_pivot_1792_, v_as_1793_, v_i_1794_, v_k_1795_);
lean_dec(v_pivot_1792_);
lean_dec(v_hi_1791_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1797_, lean_object* v_as_1798_, lean_object* v_lo_1799_, lean_object* v_hi_1800_){
_start:
{
lean_object* v___y_1802_; uint8_t v___x_1812_; 
v___x_1812_ = lean_nat_dec_lt(v_lo_1799_, v_hi_1800_);
if (v___x_1812_ == 0)
{
lean_dec(v_lo_1799_);
return v_as_1798_;
}
else
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v_mid_1815_; lean_object* v___y_1817_; lean_object* v___y_1823_; lean_object* v___x_1828_; lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1813_ = lean_nat_add(v_lo_1799_, v_hi_1800_);
v___x_1814_ = lean_unsigned_to_nat(1u);
v_mid_1815_ = lean_nat_shiftr(v___x_1813_, v___x_1814_);
lean_dec(v___x_1813_);
v___x_1828_ = lean_array_fget_borrowed(v_as_1798_, v_mid_1815_);
v___x_1829_ = lean_array_fget_borrowed(v_as_1798_, v_lo_1799_);
v___x_1830_ = l_Lean_Name_quickLt(v___x_1828_, v___x_1829_);
if (v___x_1830_ == 0)
{
v___y_1823_ = v_as_1798_;
goto v___jp_1822_;
}
else
{
lean_object* v___x_1831_; 
v___x_1831_ = lean_array_fswap(v_as_1798_, v_lo_1799_, v_mid_1815_);
v___y_1823_ = v___x_1831_;
goto v___jp_1822_;
}
v___jp_1816_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1818_ = lean_array_fget_borrowed(v___y_1817_, v_mid_1815_);
v___x_1819_ = lean_array_fget_borrowed(v___y_1817_, v_hi_1800_);
v___x_1820_ = l_Lean_Name_quickLt(v___x_1818_, v___x_1819_);
if (v___x_1820_ == 0)
{
lean_dec(v_mid_1815_);
v___y_1802_ = v___y_1817_;
goto v___jp_1801_;
}
else
{
lean_object* v___x_1821_; 
v___x_1821_ = lean_array_fswap(v___y_1817_, v_mid_1815_, v_hi_1800_);
lean_dec(v_mid_1815_);
v___y_1802_ = v___x_1821_;
goto v___jp_1801_;
}
}
v___jp_1822_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1824_ = lean_array_fget_borrowed(v___y_1823_, v_hi_1800_);
v___x_1825_ = lean_array_fget_borrowed(v___y_1823_, v_lo_1799_);
v___x_1826_ = l_Lean_Name_quickLt(v___x_1824_, v___x_1825_);
if (v___x_1826_ == 0)
{
v___y_1817_ = v___y_1823_;
goto v___jp_1816_;
}
else
{
lean_object* v___x_1827_; 
v___x_1827_ = lean_array_fswap(v___y_1823_, v_lo_1799_, v_hi_1800_);
v___y_1817_ = v___x_1827_;
goto v___jp_1816_;
}
}
}
v___jp_1801_:
{
lean_object* v_pivot_1803_; lean_object* v___x_1804_; lean_object* v_fst_1805_; lean_object* v_snd_1806_; uint8_t v___x_1807_; 
v_pivot_1803_ = lean_array_fget(v___y_1802_, v_hi_1800_);
lean_inc_n(v_lo_1799_, 2);
v___x_1804_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1800_, v_pivot_1803_, v___y_1802_, v_lo_1799_, v_lo_1799_);
lean_dec(v_pivot_1803_);
v_fst_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_fst_1805_);
v_snd_1806_ = lean_ctor_get(v___x_1804_, 1);
lean_inc(v_snd_1806_);
lean_dec_ref(v___x_1804_);
v___x_1807_ = lean_nat_dec_le(v_hi_1800_, v_fst_1805_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1797_, v_snd_1806_, v_lo_1799_, v_fst_1805_);
v___x_1809_ = lean_unsigned_to_nat(1u);
v___x_1810_ = lean_nat_add(v_fst_1805_, v___x_1809_);
lean_dec(v_fst_1805_);
v_as_1798_ = v___x_1808_;
v_lo_1799_ = v___x_1810_;
goto _start;
}
else
{
lean_dec(v_fst_1805_);
lean_dec(v_lo_1799_);
return v_snd_1806_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1832_, lean_object* v_as_1833_, lean_object* v_lo_1834_, lean_object* v_hi_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1832_, v_as_1833_, v_lo_1834_, v_hi_1835_);
lean_dec(v_hi_1835_);
lean_dec(v_n_1832_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1837_, lean_object* v_as_1838_, size_t v_i_1839_, size_t v_stop_1840_, lean_object* v_b_1841_){
_start:
{
lean_object* v___y_1843_; uint8_t v___x_1847_; 
v___x_1847_ = lean_usize_dec_eq(v_i_1839_, v_stop_1840_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; uint8_t v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1848_ = lean_array_uget_borrowed(v_as_1838_, v_i_1839_);
v___x_1849_ = 1;
lean_inc_ref(v_env_1837_);
v___x_1850_ = l_Lean_Environment_setExporting(v_env_1837_, v___x_1849_);
lean_inc(v___x_1848_);
v___x_1851_ = l_Lean_Environment_contains(v___x_1850_, v___x_1848_, v___x_1849_);
if (v___x_1851_ == 0)
{
v___y_1843_ = v_b_1841_;
goto v___jp_1842_;
}
else
{
lean_object* v___x_1852_; 
lean_inc(v___x_1848_);
v___x_1852_ = lean_array_push(v_b_1841_, v___x_1848_);
v___y_1843_ = v___x_1852_;
goto v___jp_1842_;
}
}
else
{
lean_dec_ref(v_env_1837_);
return v_b_1841_;
}
v___jp_1842_:
{
size_t v___x_1844_; size_t v___x_1845_; 
v___x_1844_ = ((size_t)1ULL);
v___x_1845_ = lean_usize_add(v_i_1839_, v___x_1844_);
v_i_1839_ = v___x_1845_;
v_b_1841_ = v___y_1843_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1853_, lean_object* v_as_1854_, lean_object* v_i_1855_, lean_object* v_stop_1856_, lean_object* v_b_1857_){
_start:
{
size_t v_i_boxed_1858_; size_t v_stop_boxed_1859_; lean_object* v_res_1860_; 
v_i_boxed_1858_ = lean_unbox_usize(v_i_1855_);
lean_dec(v_i_1855_);
v_stop_boxed_1859_ = lean_unbox_usize(v_stop_1856_);
lean_dec(v_stop_1856_);
v_res_1860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1853_, v_as_1854_, v_i_boxed_1858_, v_stop_boxed_1859_, v_b_1857_);
lean_dec_ref(v_as_1854_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1861_, lean_object* v_x_1862_){
_start:
{
if (lean_obj_tag(v_x_1862_) == 0)
{
lean_object* v_k_1863_; lean_object* v_l_1864_; lean_object* v_r_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_k_1863_ = lean_ctor_get(v_x_1862_, 1);
lean_inc(v_k_1863_);
v_l_1864_ = lean_ctor_get(v_x_1862_, 3);
lean_inc(v_l_1864_);
v_r_1865_ = lean_ctor_get(v_x_1862_, 4);
lean_inc(v_r_1865_);
lean_dec_ref_known(v_x_1862_, 5);
v___x_1866_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1861_, v_l_1864_);
v___x_1867_ = lean_array_push(v___x_1866_, v_k_1863_);
v_init_1861_ = v___x_1867_;
v_x_1862_ = v_r_1865_;
goto _start;
}
else
{
return v_init_1861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1869_, lean_object* v_es_1870_){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___y_1874_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___y_1885_; lean_object* v___y_1886_; uint8_t v___x_1888_; 
v___x_1871_ = lean_unsigned_to_nat(0u);
v___x_1872_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1882_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1872_, v_es_1870_);
v___x_1883_ = lean_array_get_size(v___x_1882_);
v___x_1888_ = lean_nat_dec_eq(v___x_1883_, v___x_1871_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___y_1892_; uint8_t v___x_1894_; 
v___x_1889_ = lean_unsigned_to_nat(1u);
v___x_1890_ = lean_nat_sub(v___x_1883_, v___x_1889_);
v___x_1894_ = lean_nat_dec_le(v___x_1871_, v___x_1890_);
if (v___x_1894_ == 0)
{
lean_inc(v___x_1890_);
v___y_1892_ = v___x_1890_;
goto v___jp_1891_;
}
else
{
v___y_1892_ = v___x_1871_;
goto v___jp_1891_;
}
v___jp_1891_:
{
uint8_t v___x_1893_; 
v___x_1893_ = lean_nat_dec_le(v___y_1892_, v___x_1890_);
if (v___x_1893_ == 0)
{
lean_dec(v___x_1890_);
lean_inc(v___y_1892_);
v___y_1885_ = v___y_1892_;
v___y_1886_ = v___y_1892_;
goto v___jp_1884_;
}
else
{
v___y_1885_ = v___y_1892_;
v___y_1886_ = v___x_1890_;
goto v___jp_1884_;
}
}
}
else
{
v___y_1874_ = v___x_1882_;
goto v___jp_1873_;
}
v___jp_1873_:
{
lean_object* v___x_1875_; uint8_t v___x_1876_; 
v___x_1875_ = lean_array_get_size(v___y_1874_);
v___x_1876_ = lean_nat_dec_lt(v___x_1871_, v___x_1875_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1877_; 
lean_dec_ref(v_env_1869_);
v___x_1877_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1872_);
lean_ctor_set(v___x_1877_, 1, v___x_1872_);
lean_ctor_set(v___x_1877_, 2, v___y_1874_);
return v___x_1877_;
}
else
{
size_t v___x_1878_; size_t v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1878_ = ((size_t)0ULL);
v___x_1879_ = lean_usize_of_nat(v___x_1875_);
v___x_1880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1869_, v___y_1874_, v___x_1878_, v___x_1879_, v___x_1872_);
lean_inc_ref(v___x_1880_);
v___x_1881_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
lean_ctor_set(v___x_1881_, 2, v___y_1874_);
return v___x_1881_;
}
}
v___jp_1884_:
{
lean_object* v___x_1887_; 
v___x_1887_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1883_, v___x_1882_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
v___y_1874_ = v___x_1887_;
goto v___jp_1873_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v_name_1895_, lean_object* v_decl_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1900_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1901_ = l_Lean_MessageData_ofName(v_name_1895_);
v___x_1902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1900_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v___x_1903_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1902_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1904_, v___y_1897_, v___y_1898_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v_name_1906_, lean_object* v_decl_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lean_registerTagAttribute___lam__4(v_name_1906_, v_decl_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v_decl_1907_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1912_, lean_object* v_x_1913_, lean_object* v_x_1914_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1912_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1917_, lean_object* v_x_1918_, lean_object* v_x_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_registerTagAttribute___lam__5(v___x_1917_, v_x_1918_, v_x_1919_);
lean_dec_ref(v_x_1919_);
lean_dec_ref(v_x_1918_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v___x_1922_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v___x_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_registerTagAttribute___lam__6(v___x_1925_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_a_1928_, lean_object* v_decl_1929_, lean_object* v_s_1930_){
_start:
{
lean_object* v_addEntryFn_1931_; lean_object* v_importedEntries_1932_; lean_object* v_state_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1941_; 
v_addEntryFn_1931_ = lean_ctor_get(v_a_1928_, 3);
lean_inc(v_addEntryFn_1931_);
lean_dec_ref(v_a_1928_);
v_importedEntries_1932_ = lean_ctor_get(v_s_1930_, 0);
v_state_1933_ = lean_ctor_get(v_s_1930_, 1);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_s_1930_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1935_ = v_s_1930_;
v_isShared_1936_ = v_isSharedCheck_1941_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_state_1933_);
lean_inc(v_importedEntries_1932_);
lean_dec(v_s_1930_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1941_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v_state_1937_; lean_object* v___x_1939_; 
v_state_1937_ = lean_apply_2(v_addEntryFn_1931_, v_state_1933_, v_decl_1929_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 1, v_state_1937_);
v___x_1939_ = v___x_1935_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_importedEntries_1932_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_state_1937_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1942_, lean_object* v_declName_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1947_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1948_ = l_Lean_MessageData_ofName(v_attrName_1942_);
v___x_1949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = 0;
v___x_1953_ = l_Lean_MessageData_ofConstName(v_declName_1943_, v___x_1952_);
v___x_1954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1951_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
v___x_1955_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1954_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1956_, v___y_1944_, v___y_1945_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1958_, lean_object* v_declName_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1958_, v_declName_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1964_, lean_object* v_declName_1965_, lean_object* v_asyncPrefix_x3f_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v___y_1971_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1966_) == 0)
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_MessageData_nil;
v___y_1971_ = v___x_1984_;
goto v___jp_1970_;
}
else
{
lean_object* v_val_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v_val_1985_ = lean_ctor_get(v_asyncPrefix_x3f_1966_, 0);
lean_inc(v_val_1985_);
lean_dec_ref_known(v_asyncPrefix_x3f_1966_, 1);
v___x_1986_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1987_ = l_Lean_MessageData_ofName(v_val_1985_);
v___x_1988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1988_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___y_1971_ = v___x_1990_;
goto v___jp_1970_;
}
v___jp_1970_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1972_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1973_ = l_Lean_MessageData_ofName(v_attrName_1964_);
v___x_1974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1972_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1974_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = 0;
v___x_1978_ = l_Lean_MessageData_ofConstName(v_declName_1965_, v___x_1977_);
v___x_1979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1976_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
v___x_1980_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1979_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
lean_ctor_set(v___x_1982_, 1, v___y_1971_);
v___x_1983_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1982_, v___y_1967_, v___y_1968_);
return v___x_1983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1991_, lean_object* v_declName_1992_, lean_object* v_asyncPrefix_x3f_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1991_, v_declName_1992_, v_asyncPrefix_x3f_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1998_, uint8_t v_kind_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___y_2009_; 
v___x_2003_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_2004_ = l_Lean_MessageData_ofName(v_name_1998_);
v___x_2005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2003_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_2007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2005_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
switch(v_kind_1999_)
{
case 0:
{
lean_object* v___x_2016_; 
v___x_2016_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_2009_ = v___x_2016_;
goto v___jp_2008_;
}
case 1:
{
lean_object* v___x_2017_; 
v___x_2017_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_2009_ = v___x_2017_;
goto v___jp_2008_;
}
default: 
{
lean_object* v___x_2018_; 
v___x_2018_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_2009_ = v___x_2018_;
goto v___jp_2008_;
}
}
v___jp_2008_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_inc_ref(v___y_2009_);
v___x_2010_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2010_, 0, v___y_2009_);
v___x_2011_ = l_Lean_MessageData_ofFormat(v___x_2010_);
v___x_2012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2007_);
lean_ctor_set(v___x_2012_, 1, v___x_2011_);
v___x_2013_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_2014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2012_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
v___x_2015_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2014_, v___y_2000_, v___y_2001_);
return v___x_2015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_2019_, lean_object* v_kind_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
uint8_t v_kind_boxed_2024_; lean_object* v_res_2025_; 
v_kind_boxed_2024_ = lean_unbox(v_kind_2020_);
v_res_2025_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2019_, v_kind_boxed_2024_, v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__8(lean_object* v_a_2026_, lean_object* v_validate_2027_, lean_object* v_name_2028_, lean_object* v_decl_2029_, lean_object* v_stx_2030_, uint8_t v_kind_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v___y_2036_; lean_object* v_nextMacroScope_2037_; lean_object* v_ngen_2038_; lean_object* v_auxDeclNGen_2039_; lean_object* v_traceState_2040_; lean_object* v_recordedDeps_2041_; lean_object* v_messages_2042_; lean_object* v_infoState_2043_; lean_object* v_snapshotTasks_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___f_2051_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___x_2088_; 
lean_inc(v_decl_2029_);
lean_inc_ref(v_a_2026_);
v___f_2051_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7), 3, 2);
lean_closure_set(v___f_2051_, 0, v_a_2026_);
lean_closure_set(v___f_2051_, 1, v_decl_2029_);
v___x_2088_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2030_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2088_) == 0)
{
uint8_t v___x_2089_; uint8_t v___x_2090_; 
lean_dec_ref_known(v___x_2088_, 1);
v___x_2089_ = 0;
v___x_2090_ = l_Lean_instBEqAttributeKind_beq(v_kind_2031_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
lean_dec_ref(v___f_2051_);
lean_dec(v_decl_2029_);
lean_dec_ref(v_validate_2027_);
lean_dec_ref(v_a_2026_);
v___x_2091_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2028_, v_kind_2031_, v___y_2032_, v___y_2033_);
return v___x_2091_;
}
else
{
goto v___jp_2083_;
}
}
else
{
lean_dec_ref(v___f_2051_);
lean_dec(v_decl_2029_);
lean_dec(v_name_2028_);
lean_dec_ref(v_validate_2027_);
lean_dec_ref(v_a_2026_);
return v___x_2088_;
}
v___jp_2035_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2047_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_2048_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2048_, 0, v___y_2046_);
lean_ctor_set(v___x_2048_, 1, v_nextMacroScope_2037_);
lean_ctor_set(v___x_2048_, 2, v_ngen_2038_);
lean_ctor_set(v___x_2048_, 3, v_auxDeclNGen_2039_);
lean_ctor_set(v___x_2048_, 4, v_traceState_2040_);
lean_ctor_set(v___x_2048_, 5, v___x_2047_);
lean_ctor_set(v___x_2048_, 6, v_recordedDeps_2041_);
lean_ctor_set(v___x_2048_, 7, v_messages_2042_);
lean_ctor_set(v___x_2048_, 8, v_infoState_2043_);
lean_ctor_set(v___x_2048_, 9, v_snapshotTasks_2044_);
v___x_2049_ = lean_st_ref_put(v___y_2036_, v___x_2048_);
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v___y_2045_);
return v___x_2050_;
}
v___jp_2052_:
{
lean_object* v___x_2055_; 
lean_inc(v___y_2054_);
lean_inc_ref(v___y_2053_);
lean_inc(v_decl_2029_);
v___x_2055_ = lean_apply_4(v_validate_2027_, v_decl_2029_, v___y_2053_, v___y_2054_, lean_box(0));
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v___x_2056_; lean_object* v_toEnvExtension_2057_; lean_object* v_env_2058_; lean_object* v_nextMacroScope_2059_; lean_object* v_ngen_2060_; lean_object* v_auxDeclNGen_2061_; lean_object* v_traceState_2062_; lean_object* v_recordedDeps_2063_; lean_object* v_messages_2064_; lean_object* v_infoState_2065_; lean_object* v_snapshotTasks_2066_; lean_object* v_asyncMode_2067_; uint8_t v_logWrites_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
lean_dec_ref_known(v___x_2055_, 1);
v___x_2056_ = lean_st_ref_take(v___y_2054_);
v_toEnvExtension_2057_ = lean_ctor_get(v_a_2026_, 0);
lean_inc_ref(v_toEnvExtension_2057_);
lean_dec_ref(v_a_2026_);
v_env_2058_ = lean_ctor_get(v___x_2056_, 0);
lean_inc_ref(v_env_2058_);
v_nextMacroScope_2059_ = lean_ctor_get(v___x_2056_, 1);
lean_inc(v_nextMacroScope_2059_);
v_ngen_2060_ = lean_ctor_get(v___x_2056_, 2);
lean_inc_ref(v_ngen_2060_);
v_auxDeclNGen_2061_ = lean_ctor_get(v___x_2056_, 3);
lean_inc_ref(v_auxDeclNGen_2061_);
v_traceState_2062_ = lean_ctor_get(v___x_2056_, 4);
lean_inc_ref(v_traceState_2062_);
v_recordedDeps_2063_ = lean_ctor_get(v___x_2056_, 6);
lean_inc_ref(v_recordedDeps_2063_);
v_messages_2064_ = lean_ctor_get(v___x_2056_, 7);
lean_inc_ref(v_messages_2064_);
v_infoState_2065_ = lean_ctor_get(v___x_2056_, 8);
lean_inc_ref(v_infoState_2065_);
v_snapshotTasks_2066_ = lean_ctor_get(v___x_2056_, 9);
lean_inc_ref(v_snapshotTasks_2066_);
lean_dec(v___x_2056_);
v_asyncMode_2067_ = lean_ctor_get(v_toEnvExtension_2057_, 2);
lean_inc(v_asyncMode_2067_);
v_logWrites_2068_ = lean_ctor_get_uint8(v_toEnvExtension_2057_, sizeof(void*)*6);
v___x_2069_ = lean_box(0);
v___x_2070_ = 1;
if (v_logWrites_2068_ == 0)
{
lean_object* v___x_2071_; 
v___x_2071_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2057_, v_env_2058_, v___f_2051_, v_asyncMode_2067_, v_decl_2029_, v___x_2070_);
lean_dec(v_asyncMode_2067_);
v___y_2036_ = v___y_2054_;
v_nextMacroScope_2037_ = v_nextMacroScope_2059_;
v_ngen_2038_ = v_ngen_2060_;
v_auxDeclNGen_2039_ = v_auxDeclNGen_2061_;
v_traceState_2040_ = v_traceState_2062_;
v_recordedDeps_2041_ = v_recordedDeps_2063_;
v_messages_2042_ = v_messages_2064_;
v_infoState_2043_ = v_infoState_2065_;
v_snapshotTasks_2044_ = v_snapshotTasks_2066_;
v___y_2045_ = v___x_2069_;
v___y_2046_ = v___x_2071_;
goto v___jp_2035_;
}
else
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_inc(v_decl_2029_);
v___x_2072_ = l_Lean_Environment_logDeclChange(v_env_2058_, v_decl_2029_);
v___x_2073_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2057_, v___x_2072_, v___f_2051_, v_asyncMode_2067_, v_decl_2029_, v___x_2070_);
lean_dec(v_asyncMode_2067_);
v___y_2036_ = v___y_2054_;
v_nextMacroScope_2037_ = v_nextMacroScope_2059_;
v_ngen_2038_ = v_ngen_2060_;
v_auxDeclNGen_2039_ = v_auxDeclNGen_2061_;
v_traceState_2040_ = v_traceState_2062_;
v_recordedDeps_2041_ = v_recordedDeps_2063_;
v_messages_2042_ = v_messages_2064_;
v_infoState_2043_ = v_infoState_2065_;
v_snapshotTasks_2044_ = v_snapshotTasks_2066_;
v___y_2045_ = v___x_2069_;
v___y_2046_ = v___x_2073_;
goto v___jp_2035_;
}
}
else
{
lean_dec_ref(v___f_2051_);
lean_dec(v_decl_2029_);
lean_dec_ref(v_a_2026_);
return v___x_2055_;
}
}
v___jp_2074_:
{
lean_object* v_toEnvExtension_2078_; lean_object* v_asyncMode_2079_; uint8_t v___x_2080_; 
v_toEnvExtension_2078_ = lean_ctor_get(v_a_2026_, 0);
v_asyncMode_2079_ = lean_ctor_get(v_toEnvExtension_2078_, 2);
lean_inc(v_decl_2029_);
lean_inc_ref(v___y_2075_);
v___x_2080_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2075_, v_decl_2029_, v_asyncMode_2079_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
lean_dec_ref(v___f_2051_);
lean_dec_ref(v_validate_2027_);
lean_dec_ref(v_a_2026_);
v___x_2081_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2075_);
v___x_2082_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_2028_, v_decl_2029_, v___x_2081_, v___y_2076_, v___y_2077_);
return v___x_2082_;
}
else
{
lean_dec_ref(v___y_2075_);
lean_dec(v_name_2028_);
v___y_2053_ = v___y_2076_;
v___y_2054_ = v___y_2077_;
goto v___jp_2052_;
}
}
v___jp_2083_:
{
lean_object* v___x_2084_; lean_object* v_env_2085_; lean_object* v___x_2086_; 
v___x_2084_ = lean_st_ref_get(v___y_2033_);
v_env_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc_ref(v_env_2085_);
lean_dec(v___x_2084_);
v___x_2086_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2085_, v_decl_2029_);
if (lean_obj_tag(v___x_2086_) == 0)
{
v___y_2075_ = v_env_2085_;
v___y_2076_ = v___y_2032_;
v___y_2077_ = v___y_2033_;
goto v___jp_2074_;
}
else
{
lean_object* v___x_2087_; 
lean_dec_ref_known(v___x_2086_, 1);
lean_dec_ref(v_env_2085_);
lean_dec_ref(v___f_2051_);
lean_dec_ref(v_validate_2027_);
lean_dec_ref(v_a_2026_);
v___x_2087_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2028_, v_decl_2029_, v___y_2032_, v___y_2033_);
return v___x_2087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__8___boxed(lean_object* v_a_2092_, lean_object* v_validate_2093_, lean_object* v_name_2094_, lean_object* v_decl_2095_, lean_object* v_stx_2096_, lean_object* v_kind_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
uint8_t v_kind_boxed_2101_; lean_object* v_res_2102_; 
v_kind_boxed_2101_ = lean_unbox(v_kind_2097_);
v_res_2102_ = l_Lean_registerTagAttribute___lam__8(v_a_2092_, v_validate_2093_, v_name_2094_, v_decl_2095_, v_stx_2096_, v_kind_boxed_2101_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
return v_res_2102_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___f_2109_; 
v___x_2108_ = l_Lean_NameSet_empty;
v___f_2109_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 4, 1);
lean_closure_set(v___f_2109_, 0, v___x_2108_);
return v___f_2109_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2110_; lean_object* v___f_2111_; 
v___x_2110_ = l_Lean_NameSet_empty;
v___f_2111_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 2, 1);
lean_closure_set(v___f_2111_, 0, v___x_2110_);
return v___f_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2114_, lean_object* v_descr_2115_, lean_object* v_validate_2116_, lean_object* v_ref_2117_, uint8_t v_applicationTime_2118_, lean_object* v_asyncMode_2119_, uint8_t v_logWrites_2120_){
_start:
{
lean_object* v___f_2122_; lean_object* v___f_2123_; lean_object* v___f_2124_; lean_object* v___f_2125_; lean_object* v___f_2126_; lean_object* v___f_2127_; lean_object* v___f_2128_; lean_object* v___x_2129_; uint8_t v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___f_2122_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2123_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2124_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2125_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
lean_inc(v_name_2114_);
v___f_2126_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 5, 1);
lean_closure_set(v___f_2126_, 0, v_name_2114_);
v___f_2127_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2128_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2129_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
v___x_2130_ = 0;
lean_inc(v_ref_2117_);
v___x_2131_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2131_, 0, v_ref_2117_);
lean_ctor_set(v___x_2131_, 1, v___f_2128_);
lean_ctor_set(v___x_2131_, 2, v___f_2127_);
lean_ctor_set(v___x_2131_, 3, v___f_2125_);
lean_ctor_set(v___x_2131_, 4, v___f_2124_);
lean_ctor_set(v___x_2131_, 5, v___f_2123_);
lean_ctor_set(v___x_2131_, 6, v_asyncMode_2119_);
lean_ctor_set(v___x_2131_, 7, v___x_2129_);
lean_ctor_set_uint8(v___x_2131_, sizeof(void*)*8, v___x_2130_);
lean_ctor_set_uint8(v___x_2131_, sizeof(void*)*8 + 1, v_logWrites_2120_);
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
lean_ctor_set(v___x_2132_, 1, v___f_2122_);
v___x_2133_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2132_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___f_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc_n(v_a_2134_, 2);
lean_dec_ref_known(v___x_2133_, 1);
lean_inc(v_name_2114_);
v___f_2135_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__8___boxed), 9, 3);
lean_closure_set(v___f_2135_, 0, v_a_2134_);
lean_closure_set(v___f_2135_, 1, v_validate_2116_);
lean_closure_set(v___f_2135_, 2, v_name_2114_);
v___x_2136_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2136_, 0, v_ref_2117_);
lean_ctor_set(v___x_2136_, 1, v_name_2114_);
lean_ctor_set(v___x_2136_, 2, v_descr_2115_);
lean_ctor_set_uint8(v___x_2136_, sizeof(void*)*3, v_applicationTime_2118_);
v___x_2137_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
lean_ctor_set(v___x_2137_, 1, v___f_2135_);
lean_ctor_set(v___x_2137_, 2, v___f_2126_);
lean_inc_ref(v___x_2137_);
v___x_2138_ = l_Lean_registerBuiltinAttribute(v___x_2137_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2146_; 
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2146_ == 0)
{
lean_object* v_unused_2147_; 
v_unused_2147_ = lean_ctor_get(v___x_2138_, 0);
lean_dec(v_unused_2147_);
v___x_2140_ = v___x_2138_;
v_isShared_2141_ = v_isSharedCheck_2146_;
goto v_resetjp_2139_;
}
else
{
lean_dec(v___x_2138_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2146_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2137_);
lean_ctor_set(v___x_2142_, 1, v_a_2134_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2142_);
v___x_2144_ = v___x_2140_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec_ref_known(v___x_2137_, 3);
lean_dec(v_a_2134_);
v_a_2148_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2138_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2138_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec_ref(v___f_2126_);
lean_dec(v_ref_2117_);
lean_dec_ref(v_validate_2116_);
lean_dec_ref(v_descr_2115_);
lean_dec(v_name_2114_);
v_a_2156_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2133_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2133_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2164_, lean_object* v_descr_2165_, lean_object* v_validate_2166_, lean_object* v_ref_2167_, lean_object* v_applicationTime_2168_, lean_object* v_asyncMode_2169_, lean_object* v_logWrites_2170_, lean_object* v_a_2171_){
_start:
{
uint8_t v_applicationTime_boxed_2172_; uint8_t v_logWrites_boxed_2173_; lean_object* v_res_2174_; 
v_applicationTime_boxed_2172_ = lean_unbox(v_applicationTime_2168_);
v_logWrites_boxed_2173_ = lean_unbox(v_logWrites_2170_);
v_res_2174_ = l_Lean_registerTagAttribute(v_name_2164_, v_descr_2165_, v_validate_2166_, v_ref_2167_, v_applicationTime_boxed_2172_, v_asyncMode_2169_, v_logWrites_boxed_2173_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2175_, lean_object* v_t_2176_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2175_, v_t_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2178_, lean_object* v_as_2179_, lean_object* v_lo_2180_, lean_object* v_hi_2181_, lean_object* v_w_2182_, lean_object* v_hlo_2183_, lean_object* v_hhi_2184_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2178_, v_as_2179_, v_lo_2180_, v_hi_2181_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2186_, lean_object* v_as_2187_, lean_object* v_lo_2188_, lean_object* v_hi_2189_, lean_object* v_w_2190_, lean_object* v_hlo_2191_, lean_object* v_hhi_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2186_, v_as_2187_, v_lo_2188_, v_hi_2189_, v_w_2190_, v_hlo_2191_, v_hhi_2192_);
lean_dec(v_hi_2189_);
lean_dec(v_n_2186_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2194_, lean_object* v_attrName_2195_, lean_object* v_declName_2196_, lean_object* v_asyncPrefix_x3f_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2195_, v_declName_2196_, v_asyncPrefix_x3f_2197_, v___y_2198_, v___y_2199_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2202_, lean_object* v_attrName_2203_, lean_object* v_declName_2204_, lean_object* v_asyncPrefix_x3f_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2202_, v_attrName_2203_, v_declName_2204_, v_asyncPrefix_x3f_2205_, v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2210_, lean_object* v_attrName_2211_, lean_object* v_declName_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2211_, v_declName_2212_, v___y_2213_, v___y_2214_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2217_, lean_object* v_attrName_2218_, lean_object* v_declName_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2217_, v_attrName_2218_, v_declName_2219_, v___y_2220_, v___y_2221_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2224_, lean_object* v_name_2225_, uint8_t v_kind_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2225_, v_kind_2226_, v___y_2227_, v___y_2228_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2231_, lean_object* v_name_2232_, lean_object* v_kind_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
uint8_t v_kind_boxed_2237_; lean_object* v_res_2238_; 
v_kind_boxed_2237_ = lean_unbox(v_kind_2233_);
v_res_2238_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2231_, v_name_2232_, v_kind_boxed_2237_, v___y_2234_, v___y_2235_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2239_, lean_object* v_lo_2240_, lean_object* v_hi_2241_, lean_object* v_hhi_2242_, lean_object* v_pivot_2243_, lean_object* v_as_2244_, lean_object* v_i_2245_, lean_object* v_k_2246_, lean_object* v_ilo_2247_, lean_object* v_ik_2248_, lean_object* v_w_2249_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2241_, v_pivot_2243_, v_as_2244_, v_i_2245_, v_k_2246_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2251_, lean_object* v_lo_2252_, lean_object* v_hi_2253_, lean_object* v_hhi_2254_, lean_object* v_pivot_2255_, lean_object* v_as_2256_, lean_object* v_i_2257_, lean_object* v_k_2258_, lean_object* v_ilo_2259_, lean_object* v_ik_2260_, lean_object* v_w_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2251_, v_lo_2252_, v_hi_2253_, v_hhi_2254_, v_pivot_2255_, v_as_2256_, v_i_2257_, v_k_2258_, v_ilo_2259_, v_ik_2260_, v_w_2261_);
lean_dec(v_pivot_2255_);
lean_dec(v_hi_2253_);
lean_dec(v_lo_2252_);
lean_dec(v_n_2251_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_addEntryFn_2263_, lean_object* v_decl_2264_, lean_object* v_s_2265_){
_start:
{
lean_object* v_importedEntries_2266_; lean_object* v_state_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2275_; 
v_importedEntries_2266_ = lean_ctor_get(v_s_2265_, 0);
v_state_2267_ = lean_ctor_get(v_s_2265_, 1);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_s_2265_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2269_ = v_s_2265_;
v_isShared_2270_ = v_isSharedCheck_2275_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_state_2267_);
lean_inc(v_importedEntries_2266_);
lean_dec(v_s_2265_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2275_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v_state_2271_; lean_object* v___x_2273_; 
v_state_2271_ = lean_apply_2(v_addEntryFn_2263_, v_state_2267_, v_decl_2264_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 1, v_state_2271_);
v___x_2273_ = v___x_2269_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_importedEntries_2266_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_state_2271_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_attr_2276_, lean_object* v_decl_2277_, lean_object* v_env_2278_){
_start:
{
lean_object* v_ext_2279_; lean_object* v_toEnvExtension_2280_; lean_object* v_addEntryFn_2281_; lean_object* v_asyncMode_2282_; uint8_t v_logWrites_2283_; lean_object* v___f_2284_; uint8_t v___x_2285_; 
v_ext_2279_ = lean_ctor_get(v_attr_2276_, 1);
lean_inc_ref(v_ext_2279_);
lean_dec_ref(v_attr_2276_);
v_toEnvExtension_2280_ = lean_ctor_get(v_ext_2279_, 0);
lean_inc_ref(v_toEnvExtension_2280_);
v_addEntryFn_2281_ = lean_ctor_get(v_ext_2279_, 3);
lean_inc(v_addEntryFn_2281_);
lean_dec_ref(v_ext_2279_);
v_asyncMode_2282_ = lean_ctor_get(v_toEnvExtension_2280_, 2);
lean_inc(v_asyncMode_2282_);
v_logWrites_2283_ = lean_ctor_get_uint8(v_toEnvExtension_2280_, sizeof(void*)*6);
lean_inc(v_decl_2277_);
v___f_2284_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2284_, 0, v_addEntryFn_2281_);
lean_closure_set(v___f_2284_, 1, v_decl_2277_);
v___x_2285_ = 1;
if (v_logWrites_2283_ == 0)
{
lean_object* v___x_2286_; 
v___x_2286_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2280_, v_env_2278_, v___f_2284_, v_asyncMode_2282_, v_decl_2277_, v___x_2285_);
lean_dec(v_asyncMode_2282_);
return v___x_2286_;
}
else
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
lean_inc_ref(v_toEnvExtension_2280_);
v___x_2287_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2280_, v_env_2278_);
lean_dec_ref(v_env_2278_);
v___x_2288_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2280_, v___x_2287_, v___f_2284_, v_asyncMode_2282_, v_decl_2277_, v___x_2285_);
lean_dec(v_asyncMode_2282_);
return v___x_2288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_modifyEnv_2289_, lean_object* v___f_2290_, lean_object* v_____r_2291_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = lean_apply_1(v_modifyEnv_2289_, v___f_2290_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v_attr_2293_, lean_object* v_env_2294_, lean_object* v_decl_2295_, lean_object* v_inst_2296_, lean_object* v_inst_2297_, lean_object* v_toBind_2298_, lean_object* v___f_2299_, lean_object* v_modifyEnv_2300_, lean_object* v___f_2301_, lean_object* v_____r_2302_){
_start:
{
lean_object* v_ext_2303_; lean_object* v_toEnvExtension_2304_; lean_object* v_attr_2305_; lean_object* v_asyncMode_2306_; uint8_t v___x_2307_; 
v_ext_2303_ = lean_ctor_get(v_attr_2293_, 1);
v_toEnvExtension_2304_ = lean_ctor_get(v_ext_2303_, 0);
lean_inc_ref(v_toEnvExtension_2304_);
v_attr_2305_ = lean_ctor_get(v_attr_2293_, 0);
lean_inc_ref(v_attr_2305_);
lean_dec_ref(v_attr_2293_);
v_asyncMode_2306_ = lean_ctor_get(v_toEnvExtension_2304_, 2);
lean_inc(v_asyncMode_2306_);
lean_dec_ref(v_toEnvExtension_2304_);
lean_inc(v_decl_2295_);
lean_inc_ref(v_env_2294_);
v___x_2307_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2294_, v_decl_2295_, v_asyncMode_2306_);
lean_dec(v_asyncMode_2306_);
if (v___x_2307_ == 0)
{
lean_object* v_toAttributeImplCore_2308_; lean_object* v_name_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
lean_dec_ref(v___f_2301_);
lean_dec(v_modifyEnv_2300_);
v_toAttributeImplCore_2308_ = lean_ctor_get(v_attr_2305_, 0);
lean_inc_ref(v_toAttributeImplCore_2308_);
lean_dec_ref(v_attr_2305_);
v_name_2309_ = lean_ctor_get(v_toAttributeImplCore_2308_, 1);
lean_inc(v_name_2309_);
lean_dec_ref(v_toAttributeImplCore_2308_);
v___x_2310_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2294_);
v___x_2311_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2296_, v_inst_2297_, v_name_2309_, v_decl_2295_, v___x_2310_);
v___x_2312_ = lean_apply_4(v_toBind_2298_, lean_box(0), lean_box(0), v___x_2311_, v___f_2299_);
return v___x_2312_;
}
else
{
lean_object* v___x_2313_; 
lean_dec_ref(v_attr_2305_);
lean_dec(v___f_2299_);
lean_dec(v_toBind_2298_);
lean_dec_ref(v_inst_2297_);
lean_dec_ref(v_inst_2296_);
lean_dec(v_decl_2295_);
lean_dec_ref(v_env_2294_);
v___x_2313_ = lean_apply_1(v_modifyEnv_2300_, v___f_2301_);
return v___x_2313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v___f_2314_, lean_object* v_____r_2315_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = lean_apply_1(v___f_2314_, v_____r_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__5(lean_object* v_attr_2317_, lean_object* v_decl_2318_, lean_object* v_inst_2319_, lean_object* v_inst_2320_, lean_object* v_toBind_2321_, lean_object* v___f_2322_, lean_object* v_modifyEnv_2323_, lean_object* v___f_2324_, lean_object* v_env_2325_){
_start:
{
lean_object* v___f_2326_; lean_object* v___x_2327_; 
lean_inc_ref(v___f_2324_);
lean_inc(v_modifyEnv_2323_);
lean_inc(v___f_2322_);
lean_inc(v_toBind_2321_);
lean_inc_ref(v_inst_2320_);
lean_inc_ref(v_inst_2319_);
lean_inc(v_decl_2318_);
lean_inc_ref(v_env_2325_);
lean_inc_ref(v_attr_2317_);
v___f_2326_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 10, 9);
lean_closure_set(v___f_2326_, 0, v_attr_2317_);
lean_closure_set(v___f_2326_, 1, v_env_2325_);
lean_closure_set(v___f_2326_, 2, v_decl_2318_);
lean_closure_set(v___f_2326_, 3, v_inst_2319_);
lean_closure_set(v___f_2326_, 4, v_inst_2320_);
lean_closure_set(v___f_2326_, 5, v_toBind_2321_);
lean_closure_set(v___f_2326_, 6, v___f_2322_);
lean_closure_set(v___f_2326_, 7, v_modifyEnv_2323_);
lean_closure_set(v___f_2326_, 8, v___f_2324_);
v___x_2327_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2325_, v_decl_2318_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_dec_ref(v___f_2326_);
v___x_2328_ = lean_box(0);
v___x_2329_ = l_Lean_TagAttribute_setTag___redArg___lam__3(v_attr_2317_, v_env_2325_, v_decl_2318_, v_inst_2319_, v_inst_2320_, v_toBind_2321_, v___f_2322_, v_modifyEnv_2323_, v___f_2324_, v___x_2328_);
return v___x_2329_;
}
else
{
lean_object* v_attr_2330_; lean_object* v_toAttributeImplCore_2331_; lean_object* v_name_2332_; lean_object* v___f_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
lean_dec_ref_known(v___x_2327_, 1);
lean_dec_ref(v_env_2325_);
lean_dec_ref(v___f_2324_);
lean_dec(v_modifyEnv_2323_);
lean_dec(v___f_2322_);
v_attr_2330_ = lean_ctor_get(v_attr_2317_, 0);
lean_inc_ref(v_attr_2330_);
lean_dec_ref(v_attr_2317_);
v_toAttributeImplCore_2331_ = lean_ctor_get(v_attr_2330_, 0);
lean_inc_ref(v_toAttributeImplCore_2331_);
lean_dec_ref(v_attr_2330_);
v_name_2332_ = lean_ctor_get(v_toAttributeImplCore_2331_, 1);
lean_inc(v_name_2332_);
lean_dec_ref(v_toAttributeImplCore_2331_);
v___f_2333_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2333_, 0, v___f_2326_);
v___x_2334_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2319_, v_inst_2320_, v_name_2332_, v_decl_2318_);
v___x_2335_ = lean_apply_4(v_toBind_2321_, lean_box(0), lean_box(0), v___x_2334_, v___f_2333_);
return v___x_2335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2336_, lean_object* v_inst_2337_, lean_object* v_inst_2338_, lean_object* v_attr_2339_, lean_object* v_decl_2340_){
_start:
{
lean_object* v_toBind_2341_; lean_object* v_getEnv_2342_; lean_object* v_modifyEnv_2343_; lean_object* v___f_2344_; lean_object* v___f_2345_; lean_object* v___f_2346_; lean_object* v___x_2347_; 
v_toBind_2341_ = lean_ctor_get(v_inst_2336_, 1);
lean_inc_n(v_toBind_2341_, 2);
v_getEnv_2342_ = lean_ctor_get(v_inst_2338_, 0);
lean_inc(v_getEnv_2342_);
v_modifyEnv_2343_ = lean_ctor_get(v_inst_2338_, 1);
lean_inc_n(v_modifyEnv_2343_, 2);
lean_dec_ref(v_inst_2338_);
lean_inc(v_decl_2340_);
lean_inc_ref(v_attr_2339_);
v___f_2344_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2344_, 0, v_attr_2339_);
lean_closure_set(v___f_2344_, 1, v_decl_2340_);
lean_inc_ref(v___f_2344_);
v___f_2345_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2345_, 0, v_modifyEnv_2343_);
lean_closure_set(v___f_2345_, 1, v___f_2344_);
v___f_2346_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__5), 9, 8);
lean_closure_set(v___f_2346_, 0, v_attr_2339_);
lean_closure_set(v___f_2346_, 1, v_decl_2340_);
lean_closure_set(v___f_2346_, 2, v_inst_2336_);
lean_closure_set(v___f_2346_, 3, v_inst_2337_);
lean_closure_set(v___f_2346_, 4, v_toBind_2341_);
lean_closure_set(v___f_2346_, 5, v___f_2345_);
lean_closure_set(v___f_2346_, 6, v_modifyEnv_2343_);
lean_closure_set(v___f_2346_, 7, v___f_2344_);
v___x_2347_ = lean_apply_4(v_toBind_2341_, lean_box(0), lean_box(0), v_getEnv_2342_, v___f_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2348_, lean_object* v_inst_2349_, lean_object* v_inst_2350_, lean_object* v_inst_2351_, lean_object* v_attr_2352_, lean_object* v_decl_2353_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2349_, v_inst_2350_, v_inst_2351_, v_attr_2352_, v_decl_2353_);
return v___x_2354_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2355_, lean_object* v_env_2356_, lean_object* v_decl_2357_){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = lean_box(1);
v___x_2359_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2356_, v_decl_2357_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_ext_2360_; lean_object* v_toEnvExtension_2361_; lean_object* v_asyncMode_2362_; uint8_t v___x_2363_; lean_object* v___x_2364_; uint8_t v___x_2365_; 
v_ext_2360_ = lean_ctor_get(v_attr_2355_, 1);
v_toEnvExtension_2361_ = lean_ctor_get(v_ext_2360_, 0);
v_asyncMode_2362_ = lean_ctor_get(v_toEnvExtension_2361_, 2);
v___x_2363_ = 0;
lean_inc(v_decl_2357_);
v___x_2364_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2358_, v_ext_2360_, v_env_2356_, v_asyncMode_2362_, v_decl_2357_, v___x_2363_);
v___x_2365_ = l_Lean_NameSet_contains(v___x_2364_, v_decl_2357_);
lean_dec(v_decl_2357_);
lean_dec(v___x_2364_);
return v___x_2365_;
}
else
{
lean_object* v_val_2366_; lean_object* v_ext_2367_; uint8_t v___x_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; 
v_val_2366_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_val_2366_);
lean_dec_ref_known(v___x_2359_, 1);
v_ext_2367_ = lean_ctor_get(v_attr_2355_, 1);
v___x_2368_ = 0;
v___x_2369_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2358_, v_ext_2367_, v_env_2356_, v_val_2366_, v___x_2368_);
lean_dec(v_val_2366_);
lean_dec_ref(v_env_2356_);
v___x_2370_ = l_Lean_containsSortedName(v___x_2369_, v_decl_2357_);
lean_dec(v_decl_2357_);
lean_dec_ref(v___x_2369_);
return v___x_2370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2371_, lean_object* v_env_2372_, lean_object* v_decl_2373_){
_start:
{
uint8_t v_res_2374_; lean_object* v_r_2375_; 
v_res_2374_ = l_Lean_TagAttribute_hasTag(v_attr_2371_, v_env_2372_, v_decl_2373_);
lean_dec_ref(v_attr_2371_);
v_r_2375_ = lean_box(v_res_2374_);
return v_r_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(lean_object* v_x_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0___boxed(lean_object* v_x_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(v_x_2381_, v___y_2382_);
lean_dec_ref(v___y_2382_);
lean_dec_ref(v_x_2381_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(lean_object* v_s_2385_, lean_object* v_x_2386_){
_start:
{
lean_inc_ref(v_s_2385_);
return v_s_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1___boxed(lean_object* v_s_2387_, lean_object* v_x_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(v_s_2387_, v_x_2388_);
lean_dec_ref(v_x_2388_);
lean_dec_ref(v_s_2387_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(lean_object* v_x_2394_, lean_object* v_x_2395_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___boxed(lean_object* v_x_2397_, lean_object* v_x_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(v_x_2397_, v_x_2398_);
lean_dec_ref(v_x_2398_);
lean_dec_ref(v_x_2397_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(lean_object* v_x_2400_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = lean_box(0);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3___boxed(lean_object* v_x_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(v_x_2402_);
lean_dec_ref(v_x_2402_);
return v_res_2403_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4(void){
_start:
{
lean_object* v___f_2408_; lean_object* v___f_2409_; lean_object* v___f_2410_; lean_object* v___f_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___f_2408_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3));
v___f_2409_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2));
v___f_2410_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1));
v___f_2411_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0));
v___x_2412_ = lean_box(0);
v___x_2413_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_2414_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
lean_ctor_set(v___x_2414_, 1, v___x_2412_);
lean_ctor_set(v___x_2414_, 2, v___f_2411_);
lean_ctor_set(v___x_2414_, 3, v___f_2410_);
lean_ctor_set(v___x_2414_, 4, v___f_2409_);
lean_ctor_set(v___x_2414_, 5, v___f_2408_);
return v___x_2414_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5(void){
_start:
{
uint8_t v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2415_ = 0;
v___x_2416_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4);
v___x_2417_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2418_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
lean_ctor_set(v___x_2418_, 1, v___x_2416_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*2, v___x_2415_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg(){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___boxed(lean_object* v___dummy_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v_res_2422_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__0(void){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg(){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg___boxed(lean_object* v___dummy_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Lean_instInhabitedParametricAttribute___redArg();
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2430_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object* v_x_2432_, lean_object* v_p_2433_){
_start:
{
lean_object* v_fst_2434_; lean_object* v_snd_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2452_; 
v_fst_2434_ = lean_ctor_get(v_x_2432_, 0);
v_snd_2435_ = lean_ctor_get(v_x_2432_, 1);
v_isSharedCheck_2452_ = !lean_is_exclusive(v_x_2432_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2437_ = v_x_2432_;
v_isShared_2438_ = v_isSharedCheck_2452_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_snd_2435_);
lean_inc(v_fst_2434_);
lean_dec(v_x_2432_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2452_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v_fst_2439_; lean_object* v_snd_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2451_; 
v_fst_2439_ = lean_ctor_get(v_p_2433_, 0);
v_snd_2440_ = lean_ctor_get(v_p_2433_, 1);
v_isSharedCheck_2451_ = !lean_is_exclusive(v_p_2433_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2442_ = v_p_2433_;
v_isShared_2443_ = v_isSharedCheck_2451_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_snd_2440_);
lean_inc(v_fst_2439_);
lean_dec(v_p_2433_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2451_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
lean_inc(v_fst_2439_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set_tag(v___x_2437_, 1);
lean_ctor_set(v___x_2437_, 1, v_fst_2434_);
lean_ctor_set(v___x_2437_, 0, v_fst_2439_);
v___x_2445_ = v___x_2437_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_fst_2439_);
lean_ctor_set(v_reuseFailAlloc_2450_, 1, v_fst_2434_);
v___x_2445_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2446_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2439_, v_snd_2440_, v_snd_2435_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 1, v___x_2446_);
lean_ctor_set(v___x_2442_, 0, v___x_2445_);
v___x_2448_ = v___x_2442_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object* v_init_2453_, lean_object* v_x_2454_){
_start:
{
if (lean_obj_tag(v_x_2454_) == 0)
{
lean_object* v_k_2455_; lean_object* v_v_2456_; lean_object* v_l_2457_; lean_object* v_r_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v_k_2455_ = lean_ctor_get(v_x_2454_, 1);
v_v_2456_ = lean_ctor_get(v_x_2454_, 2);
v_l_2457_ = lean_ctor_get(v_x_2454_, 3);
v_r_2458_ = lean_ctor_get(v_x_2454_, 4);
v___x_2459_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2453_, v_l_2457_);
lean_inc(v_v_2456_);
lean_inc(v_k_2455_);
v___x_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2460_, 0, v_k_2455_);
lean_ctor_set(v___x_2460_, 1, v_v_2456_);
v___x_2461_ = lean_array_push(v___x_2459_, v___x_2460_);
v_init_2453_ = v___x_2461_;
v_x_2454_ = v_r_2458_;
goto _start;
}
else
{
return v_init_2453_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object* v_init_2463_, lean_object* v_x_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2463_, v_x_2464_);
lean_dec(v_x_2464_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object* v_snd_2466_, lean_object* v_as_2467_, size_t v_i_2468_, size_t v_stop_2469_, lean_object* v_b_2470_){
_start:
{
lean_object* v___y_2472_; uint8_t v___x_2476_; 
v___x_2476_ = lean_usize_dec_eq(v_i_2468_, v_stop_2469_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = lean_array_uget_borrowed(v_as_2467_, v_i_2468_);
v___x_2478_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2466_, v___x_2477_);
if (lean_obj_tag(v___x_2478_) == 0)
{
v___y_2472_ = v_b_2470_;
goto v___jp_2471_;
}
else
{
lean_object* v_val_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_val_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_val_2479_);
lean_dec_ref_known(v___x_2478_, 1);
lean_inc(v___x_2477_);
v___x_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2477_);
lean_ctor_set(v___x_2480_, 1, v_val_2479_);
v___x_2481_ = lean_array_push(v_b_2470_, v___x_2480_);
v___y_2472_ = v___x_2481_;
goto v___jp_2471_;
}
}
else
{
return v_b_2470_;
}
v___jp_2471_:
{
size_t v___x_2473_; size_t v___x_2474_; 
v___x_2473_ = ((size_t)1ULL);
v___x_2474_ = lean_usize_add(v_i_2468_, v___x_2473_);
v_i_2468_ = v___x_2474_;
v_b_2470_ = v___y_2472_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2482_, lean_object* v_as_2483_, lean_object* v_i_2484_, lean_object* v_stop_2485_, lean_object* v_b_2486_){
_start:
{
size_t v_i_boxed_2487_; size_t v_stop_boxed_2488_; lean_object* v_res_2489_; 
v_i_boxed_2487_ = lean_unbox_usize(v_i_2484_);
lean_dec(v_i_2484_);
v_stop_boxed_2488_ = lean_unbox_usize(v_stop_2485_);
lean_dec(v_stop_2485_);
v_res_2489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2482_, v_as_2483_, v_i_boxed_2487_, v_stop_boxed_2488_, v_b_2486_);
lean_dec_ref(v_as_2483_);
lean_dec(v_snd_2482_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object* v_snd_2490_, lean_object* v_as_2491_, lean_object* v_start_2492_, lean_object* v_stop_2493_){
_start:
{
lean_object* v___x_2494_; uint8_t v___x_2495_; 
v___x_2494_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2495_ = lean_nat_dec_lt(v_start_2492_, v_stop_2493_);
if (v___x_2495_ == 0)
{
return v___x_2494_;
}
else
{
lean_object* v___x_2496_; uint8_t v___x_2497_; 
v___x_2496_ = lean_array_get_size(v_as_2491_);
v___x_2497_ = lean_nat_dec_le(v_stop_2493_, v___x_2496_);
if (v___x_2497_ == 0)
{
uint8_t v___x_2498_; 
v___x_2498_ = lean_nat_dec_lt(v_start_2492_, v___x_2496_);
if (v___x_2498_ == 0)
{
return v___x_2494_;
}
else
{
size_t v___x_2499_; size_t v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = lean_usize_of_nat(v_start_2492_);
v___x_2500_ = lean_usize_of_nat(v___x_2496_);
v___x_2501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2490_, v_as_2491_, v___x_2499_, v___x_2500_, v___x_2494_);
return v___x_2501_;
}
}
else
{
size_t v___x_2502_; size_t v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = lean_usize_of_nat(v_start_2492_);
v___x_2503_ = lean_usize_of_nat(v_stop_2493_);
v___x_2504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2490_, v_as_2491_, v___x_2502_, v___x_2503_, v___x_2494_);
return v___x_2504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object* v_snd_2505_, lean_object* v_as_2506_, lean_object* v_start_2507_, lean_object* v_stop_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2505_, v_as_2506_, v_start_2507_, v_stop_2508_);
lean_dec(v_stop_2508_);
lean_dec(v_start_2507_);
lean_dec_ref(v_as_2506_);
lean_dec(v_snd_2505_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object* v_hi_2510_, lean_object* v_pivot_2511_, lean_object* v_as_2512_, lean_object* v_i_2513_, lean_object* v_k_2514_){
_start:
{
uint8_t v___x_2515_; 
v___x_2515_ = lean_nat_dec_lt(v_k_2514_, v_hi_2510_);
if (v___x_2515_ == 0)
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
lean_dec(v_k_2514_);
v___x_2516_ = lean_array_fswap(v_as_2512_, v_i_2513_, v_hi_2510_);
v___x_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2517_, 0, v_i_2513_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
return v___x_2517_;
}
else
{
lean_object* v___x_2518_; lean_object* v_fst_2519_; lean_object* v_fst_2520_; uint8_t v___x_2521_; 
v___x_2518_ = lean_array_fget_borrowed(v_as_2512_, v_k_2514_);
v_fst_2519_ = lean_ctor_get(v___x_2518_, 0);
v_fst_2520_ = lean_ctor_get(v_pivot_2511_, 0);
v___x_2521_ = l_Lean_Name_quickLt(v_fst_2519_, v_fst_2520_);
if (v___x_2521_ == 0)
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = lean_unsigned_to_nat(1u);
v___x_2523_ = lean_nat_add(v_k_2514_, v___x_2522_);
lean_dec(v_k_2514_);
v_k_2514_ = v___x_2523_;
goto _start;
}
else
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2525_ = lean_array_fswap(v_as_2512_, v_i_2513_, v_k_2514_);
v___x_2526_ = lean_unsigned_to_nat(1u);
v___x_2527_ = lean_nat_add(v_i_2513_, v___x_2526_);
lean_dec(v_i_2513_);
v___x_2528_ = lean_nat_add(v_k_2514_, v___x_2526_);
lean_dec(v_k_2514_);
v_as_2512_ = v___x_2525_;
v_i_2513_ = v___x_2527_;
v_k_2514_ = v___x_2528_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2530_, lean_object* v_pivot_2531_, lean_object* v_as_2532_, lean_object* v_i_2533_, lean_object* v_k_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2530_, v_pivot_2531_, v_as_2532_, v_i_2533_, v_k_2534_);
lean_dec_ref(v_pivot_2531_);
lean_dec(v_hi_2530_);
return v_res_2535_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object* v_a_2536_, lean_object* v_b_2537_){
_start:
{
lean_object* v_fst_2538_; lean_object* v_fst_2539_; uint8_t v___x_2540_; 
v_fst_2538_ = lean_ctor_get(v_a_2536_, 0);
v_fst_2539_ = lean_ctor_get(v_b_2537_, 0);
v___x_2540_ = l_Lean_Name_quickLt(v_fst_2538_, v_fst_2539_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object* v_a_2541_, lean_object* v_b_2542_){
_start:
{
uint8_t v_res_2543_; lean_object* v_r_2544_; 
v_res_2543_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2541_, v_b_2542_);
lean_dec_ref(v_b_2542_);
lean_dec_ref(v_a_2541_);
v_r_2544_ = lean_box(v_res_2543_);
return v_r_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object* v_n_2545_, lean_object* v_as_2546_, lean_object* v_lo_2547_, lean_object* v_hi_2548_){
_start:
{
lean_object* v___y_2550_; uint8_t v___x_2560_; 
v___x_2560_ = lean_nat_dec_lt(v_lo_2547_, v_hi_2548_);
if (v___x_2560_ == 0)
{
lean_dec(v_lo_2547_);
return v_as_2546_;
}
else
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v_mid_2563_; lean_object* v___y_2565_; lean_object* v___y_2571_; lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2561_ = lean_nat_add(v_lo_2547_, v_hi_2548_);
v___x_2562_ = lean_unsigned_to_nat(1u);
v_mid_2563_ = lean_nat_shiftr(v___x_2561_, v___x_2562_);
lean_dec(v___x_2561_);
v___x_2576_ = lean_array_fget_borrowed(v_as_2546_, v_mid_2563_);
v___x_2577_ = lean_array_fget_borrowed(v_as_2546_, v_lo_2547_);
v___x_2578_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2576_, v___x_2577_);
if (v___x_2578_ == 0)
{
v___y_2571_ = v_as_2546_;
goto v___jp_2570_;
}
else
{
lean_object* v___x_2579_; 
v___x_2579_ = lean_array_fswap(v_as_2546_, v_lo_2547_, v_mid_2563_);
v___y_2571_ = v___x_2579_;
goto v___jp_2570_;
}
v___jp_2564_:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; uint8_t v___x_2568_; 
v___x_2566_ = lean_array_fget_borrowed(v___y_2565_, v_mid_2563_);
v___x_2567_ = lean_array_fget_borrowed(v___y_2565_, v_hi_2548_);
v___x_2568_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2566_, v___x_2567_);
if (v___x_2568_ == 0)
{
lean_dec(v_mid_2563_);
v___y_2550_ = v___y_2565_;
goto v___jp_2549_;
}
else
{
lean_object* v___x_2569_; 
v___x_2569_ = lean_array_fswap(v___y_2565_, v_mid_2563_, v_hi_2548_);
lean_dec(v_mid_2563_);
v___y_2550_ = v___x_2569_;
goto v___jp_2549_;
}
}
v___jp_2570_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; 
v___x_2572_ = lean_array_fget_borrowed(v___y_2571_, v_hi_2548_);
v___x_2573_ = lean_array_fget_borrowed(v___y_2571_, v_lo_2547_);
v___x_2574_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2572_, v___x_2573_);
if (v___x_2574_ == 0)
{
v___y_2565_ = v___y_2571_;
goto v___jp_2564_;
}
else
{
lean_object* v___x_2575_; 
v___x_2575_ = lean_array_fswap(v___y_2571_, v_lo_2547_, v_hi_2548_);
v___y_2565_ = v___x_2575_;
goto v___jp_2564_;
}
}
}
v___jp_2549_:
{
lean_object* v_pivot_2551_; lean_object* v___x_2552_; lean_object* v_fst_2553_; lean_object* v_snd_2554_; uint8_t v___x_2555_; 
v_pivot_2551_ = lean_array_fget(v___y_2550_, v_hi_2548_);
lean_inc_n(v_lo_2547_, 2);
v___x_2552_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2548_, v_pivot_2551_, v___y_2550_, v_lo_2547_, v_lo_2547_);
lean_dec(v_pivot_2551_);
v_fst_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_fst_2553_);
v_snd_2554_ = lean_ctor_get(v___x_2552_, 1);
lean_inc(v_snd_2554_);
lean_dec_ref(v___x_2552_);
v___x_2555_ = lean_nat_dec_le(v_hi_2548_, v_fst_2553_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2556_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2545_, v_snd_2554_, v_lo_2547_, v_fst_2553_);
v___x_2557_ = lean_unsigned_to_nat(1u);
v___x_2558_ = lean_nat_add(v_fst_2553_, v___x_2557_);
lean_dec(v_fst_2553_);
v_as_2546_ = v___x_2556_;
v_lo_2547_ = v___x_2558_;
goto _start;
}
else
{
lean_dec(v_fst_2553_);
lean_dec(v_lo_2547_);
return v_snd_2554_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object* v_n_2580_, lean_object* v_as_2581_, lean_object* v_lo_2582_, lean_object* v_hi_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2580_, v_as_2581_, v_lo_2582_, v_hi_2583_);
lean_dec(v_hi_2583_);
lean_dec(v_n_2580_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object* v_filterExport_2585_, lean_object* v_env_2586_, lean_object* v_as_2587_, size_t v_i_2588_, size_t v_stop_2589_, lean_object* v_b_2590_){
_start:
{
lean_object* v___y_2592_; uint8_t v___x_2596_; 
v___x_2596_ = lean_usize_dec_eq(v_i_2588_, v_stop_2589_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; lean_object* v_fst_2598_; lean_object* v_snd_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; 
v___x_2597_ = lean_array_uget_borrowed(v_as_2587_, v_i_2588_);
v_fst_2598_ = lean_ctor_get(v___x_2597_, 0);
v_snd_2599_ = lean_ctor_get(v___x_2597_, 1);
lean_inc_ref(v_filterExport_2585_);
lean_inc(v_snd_2599_);
lean_inc(v_fst_2598_);
lean_inc_ref(v_env_2586_);
v___x_2600_ = lean_apply_3(v_filterExport_2585_, v_env_2586_, v_fst_2598_, v_snd_2599_);
v___x_2601_ = lean_unbox(v___x_2600_);
if (v___x_2601_ == 0)
{
v___y_2592_ = v_b_2590_;
goto v___jp_2591_;
}
else
{
lean_object* v___x_2602_; 
lean_inc(v___x_2597_);
v___x_2602_ = lean_array_push(v_b_2590_, v___x_2597_);
v___y_2592_ = v___x_2602_;
goto v___jp_2591_;
}
}
else
{
lean_dec_ref(v_env_2586_);
lean_dec_ref(v_filterExport_2585_);
return v_b_2590_;
}
v___jp_2591_:
{
size_t v___x_2593_; size_t v___x_2594_; 
v___x_2593_ = ((size_t)1ULL);
v___x_2594_ = lean_usize_add(v_i_2588_, v___x_2593_);
v_i_2588_ = v___x_2594_;
v_b_2590_ = v___y_2592_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object* v_filterExport_2603_, lean_object* v_env_2604_, lean_object* v_as_2605_, lean_object* v_i_2606_, lean_object* v_stop_2607_, lean_object* v_b_2608_){
_start:
{
size_t v_i_boxed_2609_; size_t v_stop_boxed_2610_; lean_object* v_res_2611_; 
v_i_boxed_2609_ = lean_unbox_usize(v_i_2606_);
lean_dec(v_i_2606_);
v_stop_boxed_2610_ = lean_unbox_usize(v_stop_2607_);
lean_dec(v_stop_2607_);
v_res_2611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2603_, v_env_2604_, v_as_2605_, v_i_boxed_2609_, v_stop_boxed_2610_, v_b_2608_);
lean_dec_ref(v_as_2605_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object* v_filterExport_2612_, uint8_t v_preserveOrder_2613_, lean_object* v_env_2614_, lean_object* v_x_2615_){
_start:
{
lean_object* v___y_2617_; 
if (v_preserveOrder_2613_ == 0)
{
lean_object* v_snd_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v_r_2630_; lean_object* v___x_2631_; lean_object* v___y_2633_; lean_object* v___y_2634_; uint8_t v___x_2636_; 
v_snd_2627_ = lean_ctor_get(v_x_2615_, 1);
lean_inc(v_snd_2627_);
lean_dec_ref(v_x_2615_);
v___x_2628_ = lean_unsigned_to_nat(0u);
v___x_2629_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v_r_2630_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_2629_, v_snd_2627_);
lean_dec(v_snd_2627_);
v___x_2631_ = lean_array_get_size(v_r_2630_);
v___x_2636_ = lean_nat_dec_eq(v___x_2631_, v___x_2628_);
if (v___x_2636_ == 0)
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___y_2640_; uint8_t v___x_2642_; 
v___x_2637_ = lean_unsigned_to_nat(1u);
v___x_2638_ = lean_nat_sub(v___x_2631_, v___x_2637_);
v___x_2642_ = lean_nat_dec_le(v___x_2628_, v___x_2638_);
if (v___x_2642_ == 0)
{
lean_inc(v___x_2638_);
v___y_2640_ = v___x_2638_;
goto v___jp_2639_;
}
else
{
v___y_2640_ = v___x_2628_;
goto v___jp_2639_;
}
v___jp_2639_:
{
uint8_t v___x_2641_; 
v___x_2641_ = lean_nat_dec_le(v___y_2640_, v___x_2638_);
if (v___x_2641_ == 0)
{
lean_dec(v___x_2638_);
lean_inc(v___y_2640_);
v___y_2633_ = v___y_2640_;
v___y_2634_ = v___y_2640_;
goto v___jp_2632_;
}
else
{
v___y_2633_ = v___y_2640_;
v___y_2634_ = v___x_2638_;
goto v___jp_2632_;
}
}
}
else
{
v___y_2617_ = v_r_2630_;
goto v___jp_2616_;
}
v___jp_2632_:
{
lean_object* v___x_2635_; 
v___x_2635_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_2631_, v_r_2630_, v___y_2633_, v___y_2634_);
lean_dec(v___y_2634_);
v___y_2617_ = v___x_2635_;
goto v___jp_2616_;
}
}
else
{
lean_object* v_fst_2643_; lean_object* v_snd_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v_fst_2643_ = lean_ctor_get(v_x_2615_, 0);
lean_inc(v_fst_2643_);
v_snd_2644_ = lean_ctor_get(v_x_2615_, 1);
lean_inc(v_snd_2644_);
lean_dec_ref(v_x_2615_);
v___x_2645_ = lean_array_mk(v_fst_2643_);
v___x_2646_ = l_Array_reverse___redArg(v___x_2645_);
v___x_2647_ = lean_unsigned_to_nat(0u);
v___x_2648_ = lean_array_get_size(v___x_2646_);
v___x_2649_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2644_, v___x_2646_, v___x_2647_, v___x_2648_);
lean_dec_ref(v___x_2646_);
lean_dec(v_snd_2644_);
v___y_2617_ = v___x_2649_;
goto v___jp_2616_;
}
v___jp_2616_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v___x_2618_ = lean_unsigned_to_nat(0u);
v___x_2619_ = lean_array_get_size(v___y_2617_);
v___x_2620_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2621_ = lean_nat_dec_lt(v___x_2618_, v___x_2619_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2622_; 
lean_dec_ref(v_env_2614_);
lean_dec_ref(v_filterExport_2612_);
v___x_2622_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2620_);
lean_ctor_set(v___x_2622_, 1, v___x_2620_);
lean_ctor_set(v___x_2622_, 2, v___y_2617_);
return v___x_2622_;
}
else
{
size_t v___x_2623_; size_t v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2623_ = ((size_t)0ULL);
v___x_2624_ = lean_usize_of_nat(v___x_2619_);
v___x_2625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2612_, v_env_2614_, v___y_2617_, v___x_2623_, v___x_2624_, v___x_2620_);
lean_inc_ref(v___x_2625_);
v___x_2626_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
lean_ctor_set(v___x_2626_, 2, v___y_2617_);
return v___x_2626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object* v_filterExport_2650_, lean_object* v_preserveOrder_2651_, lean_object* v_env_2652_, lean_object* v_x_2653_){
_start:
{
uint8_t v_preserveOrder_boxed_2654_; lean_object* v_res_2655_; 
v_preserveOrder_boxed_2654_ = lean_unbox(v_preserveOrder_2651_);
v_res_2655_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2650_, v_preserveOrder_boxed_2654_, v_env_2652_, v_x_2653_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object* v_x_2665_){
_start:
{
lean_object* v_snd_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2680_; 
v_snd_2666_ = lean_ctor_get(v_x_2665_, 1);
v_isSharedCheck_2680_ = !lean_is_exclusive(v_x_2665_);
if (v_isSharedCheck_2680_ == 0)
{
lean_object* v_unused_2681_; 
v_unused_2681_ = lean_ctor_get(v_x_2665_, 0);
lean_dec(v_unused_2681_);
v___x_2668_ = v_x_2665_;
v_isShared_2669_ = v_isSharedCheck_2680_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_snd_2666_);
lean_dec(v_x_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2680_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; lean_object* v___y_2672_; 
v___x_2670_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2666_) == 0)
{
lean_object* v_size_2678_; 
v_size_2678_ = lean_ctor_get(v_snd_2666_, 0);
lean_inc(v_size_2678_);
lean_dec_ref_known(v_snd_2666_, 5);
v___y_2672_ = v_size_2678_;
goto v___jp_2671_;
}
else
{
lean_object* v___x_2679_; 
v___x_2679_ = lean_unsigned_to_nat(0u);
v___y_2672_ = v___x_2679_;
goto v___jp_2671_;
}
v___jp_2671_:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2673_ = l_Nat_reprFast(v___y_2672_);
v___x_2674_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2673_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set_tag(v___x_2668_, 5);
lean_ctor_set(v___x_2668_, 1, v___x_2674_);
lean_ctor_set(v___x_2668_, 0, v___x_2670_);
v___x_2676_ = v___x_2668_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object* v_x_2682_){
_start:
{
lean_object* v___x_2683_; 
v___x_2683_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object* v_x_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_registerParametricAttributeExt___redArg___lam__3(v_x_2684_);
lean_dec_ref(v_x_2684_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object* v___x_2686_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2686_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object* v___x_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2689_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object* v___x_2692_, lean_object* v_x_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v___x_2696_; 
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2692_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object* v___x_2697_, lean_object* v_x_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2697_, v_x_2698_, v___y_2699_);
lean_dec_ref(v___y_2699_);
lean_dec_ref(v_x_2698_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object* v_ref_2712_, uint8_t v_preserveOrder_2713_, lean_object* v_filterExport_2714_, uint8_t v_logWrites_2715_){
_start:
{
lean_object* v___f_2717_; lean_object* v___x_2718_; lean_object* v___f_2719_; lean_object* v___f_2720_; lean_object* v___f_2721_; lean_object* v___f_2722_; lean_object* v___f_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; uint8_t v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___f_2717_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__0));
v___x_2718_ = lean_box(v_preserveOrder_2713_);
v___f_2719_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2719_, 0, v_filterExport_2714_);
lean_closure_set(v___f_2719_, 1, v___x_2718_);
v___f_2720_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__1));
v___f_2721_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__2));
v___f_2722_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__4));
v___f_2723_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__5));
v___x_2724_ = lean_box(2);
v___x_2725_ = lean_box(0);
v___x_2726_ = 0;
v___x_2727_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2727_, 0, v_ref_2712_);
lean_ctor_set(v___x_2727_, 1, v___f_2722_);
lean_ctor_set(v___x_2727_, 2, v___f_2723_);
lean_ctor_set(v___x_2727_, 3, v___f_2717_);
lean_ctor_set(v___x_2727_, 4, v___f_2719_);
lean_ctor_set(v___x_2727_, 5, v___f_2720_);
lean_ctor_set(v___x_2727_, 6, v___x_2724_);
lean_ctor_set(v___x_2727_, 7, v___x_2725_);
lean_ctor_set_uint8(v___x_2727_, sizeof(void*)*8, v___x_2726_);
lean_ctor_set_uint8(v___x_2727_, sizeof(void*)*8 + 1, v_logWrites_2715_);
v___x_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2727_);
lean_ctor_set(v___x_2728_, 1, v___f_2721_);
v___x_2729_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2728_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object* v_ref_2730_, lean_object* v_preserveOrder_2731_, lean_object* v_filterExport_2732_, lean_object* v_logWrites_2733_, lean_object* v_a_2734_){
_start:
{
uint8_t v_preserveOrder_boxed_2735_; uint8_t v_logWrites_boxed_2736_; lean_object* v_res_2737_; 
v_preserveOrder_boxed_2735_ = lean_unbox(v_preserveOrder_2731_);
v_logWrites_boxed_2736_ = lean_unbox(v_logWrites_2733_);
v_res_2737_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2730_, v_preserveOrder_boxed_2735_, v_filterExport_2732_, v_logWrites_boxed_2736_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object* v_00_u03b1_2738_, lean_object* v_ref_2739_, uint8_t v_preserveOrder_2740_, lean_object* v_filterExport_2741_, uint8_t v_logWrites_2742_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2739_, v_preserveOrder_2740_, v_filterExport_2741_, v_logWrites_2742_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object* v_00_u03b1_2745_, lean_object* v_ref_2746_, lean_object* v_preserveOrder_2747_, lean_object* v_filterExport_2748_, lean_object* v_logWrites_2749_, lean_object* v_a_2750_){
_start:
{
uint8_t v_preserveOrder_boxed_2751_; uint8_t v_logWrites_boxed_2752_; lean_object* v_res_2753_; 
v_preserveOrder_boxed_2751_ = lean_unbox(v_preserveOrder_2747_);
v_logWrites_boxed_2752_ = lean_unbox(v_logWrites_2749_);
v_res_2753_ = l_Lean_registerParametricAttributeExt(v_00_u03b1_2745_, v_ref_2746_, v_preserveOrder_boxed_2751_, v_filterExport_2748_, v_logWrites_boxed_2752_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object* v_00_u03b1_2754_, lean_object* v_filterExport_2755_, lean_object* v_env_2756_, lean_object* v_as_2757_, size_t v_i_2758_, size_t v_stop_2759_, lean_object* v_b_2760_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2755_, v_env_2756_, v_as_2757_, v_i_2758_, v_stop_2759_, v_b_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object* v_00_u03b1_2762_, lean_object* v_filterExport_2763_, lean_object* v_env_2764_, lean_object* v_as_2765_, lean_object* v_i_2766_, lean_object* v_stop_2767_, lean_object* v_b_2768_){
_start:
{
size_t v_i_boxed_2769_; size_t v_stop_boxed_2770_; lean_object* v_res_2771_; 
v_i_boxed_2769_ = lean_unbox_usize(v_i_2766_);
lean_dec(v_i_2766_);
v_stop_boxed_2770_ = lean_unbox_usize(v_stop_2767_);
lean_dec(v_stop_2767_);
v_res_2771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(v_00_u03b1_2762_, v_filterExport_2763_, v_env_2764_, v_as_2765_, v_i_boxed_2769_, v_stop_boxed_2770_, v_b_2768_);
lean_dec_ref(v_as_2765_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object* v_init_2772_, lean_object* v_t_2773_){
_start:
{
lean_object* v___x_2774_; 
v___x_2774_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2772_, v_t_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object* v_init_2775_, lean_object* v_t_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(v_init_2775_, v_t_2776_);
lean_dec(v_t_2776_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object* v_00_u03b1_2778_, lean_object* v_init_2779_, lean_object* v_t_2780_){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2779_, v_t_2780_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object* v_00_u03b1_2782_, lean_object* v_init_2783_, lean_object* v_t_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(v_00_u03b1_2782_, v_init_2783_, v_t_2784_);
lean_dec(v_t_2784_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object* v_00_u03b1_2786_, lean_object* v_n_2787_, lean_object* v_as_2788_, lean_object* v_lo_2789_, lean_object* v_hi_2790_, lean_object* v_w_2791_, lean_object* v_hlo_2792_, lean_object* v_hhi_2793_){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2787_, v_as_2788_, v_lo_2789_, v_hi_2790_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object* v_00_u03b1_2795_, lean_object* v_n_2796_, lean_object* v_as_2797_, lean_object* v_lo_2798_, lean_object* v_hi_2799_, lean_object* v_w_2800_, lean_object* v_hlo_2801_, lean_object* v_hhi_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(v_00_u03b1_2795_, v_n_2796_, v_as_2797_, v_lo_2798_, v_hi_2799_, v_w_2800_, v_hlo_2801_, v_hhi_2802_);
lean_dec(v_hi_2799_);
lean_dec(v_n_2796_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object* v_00_u03b1_2804_, lean_object* v_snd_2805_, lean_object* v_as_2806_, lean_object* v_start_2807_, lean_object* v_stop_2808_){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2805_, v_as_2806_, v_start_2807_, v_stop_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object* v_00_u03b1_2810_, lean_object* v_snd_2811_, lean_object* v_as_2812_, lean_object* v_start_2813_, lean_object* v_stop_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(v_00_u03b1_2810_, v_snd_2811_, v_as_2812_, v_start_2813_, v_stop_2814_);
lean_dec(v_stop_2814_);
lean_dec(v_start_2813_);
lean_dec_ref(v_as_2812_);
lean_dec(v_snd_2811_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object* v_00_u03b1_2816_, lean_object* v_init_2817_, lean_object* v_x_2818_){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2817_, v_x_2818_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2820_, lean_object* v_init_2821_, lean_object* v_x_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(v_00_u03b1_2820_, v_init_2821_, v_x_2822_);
lean_dec(v_x_2822_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object* v_00_u03b1_2824_, lean_object* v_n_2825_, lean_object* v_lo_2826_, lean_object* v_hi_2827_, lean_object* v_hhi_2828_, lean_object* v_pivot_2829_, lean_object* v_as_2830_, lean_object* v_i_2831_, lean_object* v_k_2832_, lean_object* v_ilo_2833_, lean_object* v_ik_2834_, lean_object* v_w_2835_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2827_, v_pivot_2829_, v_as_2830_, v_i_2831_, v_k_2832_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2837_, lean_object* v_n_2838_, lean_object* v_lo_2839_, lean_object* v_hi_2840_, lean_object* v_hhi_2841_, lean_object* v_pivot_2842_, lean_object* v_as_2843_, lean_object* v_i_2844_, lean_object* v_k_2845_, lean_object* v_ilo_2846_, lean_object* v_ik_2847_, lean_object* v_w_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(v_00_u03b1_2837_, v_n_2838_, v_lo_2839_, v_hi_2840_, v_hhi_2841_, v_pivot_2842_, v_as_2843_, v_i_2844_, v_k_2845_, v_ilo_2846_, v_ik_2847_, v_w_2848_);
lean_dec_ref(v_pivot_2842_);
lean_dec(v_hi_2840_);
lean_dec(v_lo_2839_);
lean_dec(v_n_2838_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object* v_00_u03b1_2850_, lean_object* v_snd_2851_, lean_object* v_as_2852_, size_t v_i_2853_, size_t v_stop_2854_, lean_object* v_b_2855_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2851_, v_as_2852_, v_i_2853_, v_stop_2854_, v_b_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2857_, lean_object* v_snd_2858_, lean_object* v_as_2859_, lean_object* v_i_2860_, lean_object* v_stop_2861_, lean_object* v_b_2862_){
_start:
{
size_t v_i_boxed_2863_; size_t v_stop_boxed_2864_; lean_object* v_res_2865_; 
v_i_boxed_2863_ = lean_unbox_usize(v_i_2860_);
lean_dec(v_i_2860_);
v_stop_boxed_2864_ = lean_unbox_usize(v_stop_2861_);
lean_dec(v_stop_2861_);
v_res_2865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(v_00_u03b1_2857_, v_snd_2858_, v_as_2859_, v_i_boxed_2863_, v_stop_boxed_2864_, v_b_2862_);
lean_dec_ref(v_as_2859_);
lean_dec(v_snd_2858_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object* v_env_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v___x_2869_; lean_object* v_nextMacroScope_2870_; lean_object* v_ngen_2871_; lean_object* v_auxDeclNGen_2872_; lean_object* v_traceState_2873_; lean_object* v_recordedDeps_2874_; lean_object* v_messages_2875_; lean_object* v_infoState_2876_; lean_object* v_snapshotTasks_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2888_; 
v___x_2869_ = lean_st_ref_take(v___y_2867_);
v_nextMacroScope_2870_ = lean_ctor_get(v___x_2869_, 1);
v_ngen_2871_ = lean_ctor_get(v___x_2869_, 2);
v_auxDeclNGen_2872_ = lean_ctor_get(v___x_2869_, 3);
v_traceState_2873_ = lean_ctor_get(v___x_2869_, 4);
v_recordedDeps_2874_ = lean_ctor_get(v___x_2869_, 6);
v_messages_2875_ = lean_ctor_get(v___x_2869_, 7);
v_infoState_2876_ = lean_ctor_get(v___x_2869_, 8);
v_snapshotTasks_2877_ = lean_ctor_get(v___x_2869_, 9);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2888_ == 0)
{
lean_object* v_unused_2889_; lean_object* v_unused_2890_; 
v_unused_2889_ = lean_ctor_get(v___x_2869_, 5);
lean_dec(v_unused_2889_);
v_unused_2890_ = lean_ctor_get(v___x_2869_, 0);
lean_dec(v_unused_2890_);
v___x_2879_ = v___x_2869_;
v_isShared_2880_ = v_isSharedCheck_2888_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_snapshotTasks_2877_);
lean_inc(v_infoState_2876_);
lean_inc(v_messages_2875_);
lean_inc(v_recordedDeps_2874_);
lean_inc(v_traceState_2873_);
lean_inc(v_auxDeclNGen_2872_);
lean_inc(v_ngen_2871_);
lean_inc(v_nextMacroScope_2870_);
lean_dec(v___x_2869_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2888_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2884_; 
v___x_2881_ = lean_box(0);
v___x_2882_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 5, v___x_2882_);
lean_ctor_set(v___x_2879_, 0, v_env_2866_);
v___x_2884_ = v___x_2879_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_env_2866_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_nextMacroScope_2870_);
lean_ctor_set(v_reuseFailAlloc_2887_, 2, v_ngen_2871_);
lean_ctor_set(v_reuseFailAlloc_2887_, 3, v_auxDeclNGen_2872_);
lean_ctor_set(v_reuseFailAlloc_2887_, 4, v_traceState_2873_);
lean_ctor_set(v_reuseFailAlloc_2887_, 5, v___x_2882_);
lean_ctor_set(v_reuseFailAlloc_2887_, 6, v_recordedDeps_2874_);
lean_ctor_set(v_reuseFailAlloc_2887_, 7, v_messages_2875_);
lean_ctor_set(v_reuseFailAlloc_2887_, 8, v_infoState_2876_);
lean_ctor_set(v_reuseFailAlloc_2887_, 9, v_snapshotTasks_2877_);
v___x_2884_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = lean_st_ref_put(v___y_2867_, v___x_2884_);
v___x_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2881_);
return v___x_2886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object* v_env_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2891_, v___y_2892_);
lean_dec(v___y_2892_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object* v_env_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2895_, v___y_2897_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object* v_env_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(v_env_2900_, v___y_2901_, v___y_2902_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object* v_addEntryFn_2905_, lean_object* v___x_2906_, lean_object* v_s_2907_){
_start:
{
lean_object* v_importedEntries_2908_; lean_object* v_state_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2917_; 
v_importedEntries_2908_ = lean_ctor_get(v_s_2907_, 0);
v_state_2909_ = lean_ctor_get(v_s_2907_, 1);
v_isSharedCheck_2917_ = !lean_is_exclusive(v_s_2907_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2911_ = v_s_2907_;
v_isShared_2912_ = v_isSharedCheck_2917_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_state_2909_);
lean_inc(v_importedEntries_2908_);
lean_dec(v_s_2907_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2917_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v_state_2913_; lean_object* v___x_2915_; 
v_state_2913_ = lean_apply_2(v_addEntryFn_2905_, v_state_2909_, v___x_2906_);
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 1, v_state_2913_);
v___x_2915_ = v___x_2911_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_importedEntries_2908_);
lean_ctor_set(v_reuseFailAlloc_2916_, 1, v_state_2913_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object* v_afterSet_2918_, lean_object* v_getParam_2919_, lean_object* v_ext_2920_, lean_object* v_toAttributeImplCore_2921_, lean_object* v_decl_2922_, lean_object* v_stx_2923_, uint8_t v_kind_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v_nextMacroScope_2932_; lean_object* v_ngen_2933_; lean_object* v_auxDeclNGen_2934_; lean_object* v_traceState_2935_; lean_object* v_recordedDeps_2936_; lean_object* v_messages_2937_; lean_object* v_infoState_2938_; lean_object* v_snapshotTasks_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; uint8_t v___x_2990_; uint8_t v___x_2991_; 
v___x_2990_ = 0;
v___x_2991_ = l_Lean_instBEqAttributeKind_beq(v_kind_2924_, v___x_2990_);
if (v___x_2991_ == 0)
{
lean_object* v_name_2992_; lean_object* v___x_2993_; 
lean_dec(v_stx_2923_);
lean_dec(v_decl_2922_);
lean_dec_ref(v_ext_2920_);
lean_dec_ref(v_getParam_2919_);
lean_dec_ref(v_afterSet_2918_);
v_name_2992_ = lean_ctor_get(v_toAttributeImplCore_2921_, 1);
lean_inc(v_name_2992_);
lean_dec_ref(v_toAttributeImplCore_2921_);
v___x_2993_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2992_, v_kind_2924_, v___y_2925_, v___y_2926_);
return v___x_2993_;
}
else
{
goto v___jp_2984_;
}
v___jp_2928_:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2942_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_2943_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2943_, 0, v___y_2941_);
lean_ctor_set(v___x_2943_, 1, v_nextMacroScope_2932_);
lean_ctor_set(v___x_2943_, 2, v_ngen_2933_);
lean_ctor_set(v___x_2943_, 3, v_auxDeclNGen_2934_);
lean_ctor_set(v___x_2943_, 4, v_traceState_2935_);
lean_ctor_set(v___x_2943_, 5, v___x_2942_);
lean_ctor_set(v___x_2943_, 6, v_recordedDeps_2936_);
lean_ctor_set(v___x_2943_, 7, v_messages_2937_);
lean_ctor_set(v___x_2943_, 8, v_infoState_2938_);
lean_ctor_set(v___x_2943_, 9, v_snapshotTasks_2939_);
v___x_2944_ = lean_st_ref_put(v___y_2931_, v___x_2943_);
lean_inc(v___y_2931_);
lean_inc_ref(v___y_2929_);
v___x_2945_ = lean_apply_5(v_afterSet_2918_, v_decl_2922_, v___y_2940_, v___y_2929_, v___y_2931_, lean_box(0));
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_dec_ref(v___y_2930_);
return v___x_2945_;
}
else
{
lean_object* v_a_2946_; uint8_t v___x_2947_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
v___x_2947_ = l_Lean_Exception_isInterrupt(v_a_2946_);
if (v___x_2947_ == 0)
{
uint8_t v___x_2948_; 
v___x_2948_ = l_Lean_Exception_isRuntime(v_a_2946_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; 
lean_dec_ref_known(v___x_2945_, 1);
v___x_2949_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v___y_2930_, v___y_2931_);
return v___x_2949_;
}
else
{
lean_dec_ref(v___y_2930_);
return v___x_2945_;
}
}
else
{
lean_dec(v_a_2946_);
lean_dec_ref(v___y_2930_);
return v___x_2945_;
}
}
}
v___jp_2950_:
{
lean_object* v___x_2954_; 
lean_inc(v___y_2953_);
lean_inc_ref(v___y_2952_);
lean_inc(v_decl_2922_);
v___x_2954_ = lean_apply_5(v_getParam_2919_, v_decl_2922_, v_stx_2923_, v___y_2952_, v___y_2953_, lean_box(0));
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v___x_2956_; lean_object* v_toEnvExtension_2957_; lean_object* v_env_2958_; lean_object* v_nextMacroScope_2959_; lean_object* v_ngen_2960_; lean_object* v_auxDeclNGen_2961_; lean_object* v_traceState_2962_; lean_object* v_recordedDeps_2963_; lean_object* v_messages_2964_; lean_object* v_infoState_2965_; lean_object* v_snapshotTasks_2966_; lean_object* v_addEntryFn_2967_; lean_object* v_asyncMode_2968_; uint8_t v_logWrites_2969_; lean_object* v___x_2970_; lean_object* v___f_2971_; uint8_t v___x_2972_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc_n(v_a_2955_, 2);
lean_dec_ref_known(v___x_2954_, 1);
v___x_2956_ = lean_st_ref_take(v___y_2953_);
v_toEnvExtension_2957_ = lean_ctor_get(v_ext_2920_, 0);
lean_inc_ref(v_toEnvExtension_2957_);
v_env_2958_ = lean_ctor_get(v___x_2956_, 0);
lean_inc_ref(v_env_2958_);
v_nextMacroScope_2959_ = lean_ctor_get(v___x_2956_, 1);
lean_inc(v_nextMacroScope_2959_);
v_ngen_2960_ = lean_ctor_get(v___x_2956_, 2);
lean_inc_ref(v_ngen_2960_);
v_auxDeclNGen_2961_ = lean_ctor_get(v___x_2956_, 3);
lean_inc_ref(v_auxDeclNGen_2961_);
v_traceState_2962_ = lean_ctor_get(v___x_2956_, 4);
lean_inc_ref(v_traceState_2962_);
v_recordedDeps_2963_ = lean_ctor_get(v___x_2956_, 6);
lean_inc_ref(v_recordedDeps_2963_);
v_messages_2964_ = lean_ctor_get(v___x_2956_, 7);
lean_inc_ref(v_messages_2964_);
v_infoState_2965_ = lean_ctor_get(v___x_2956_, 8);
lean_inc_ref(v_infoState_2965_);
v_snapshotTasks_2966_ = lean_ctor_get(v___x_2956_, 9);
lean_inc_ref(v_snapshotTasks_2966_);
lean_dec(v___x_2956_);
v_addEntryFn_2967_ = lean_ctor_get(v_ext_2920_, 3);
lean_inc(v_addEntryFn_2967_);
lean_dec_ref(v_ext_2920_);
v_asyncMode_2968_ = lean_ctor_get(v_toEnvExtension_2957_, 2);
lean_inc(v_asyncMode_2968_);
v_logWrites_2969_ = lean_ctor_get_uint8(v_toEnvExtension_2957_, sizeof(void*)*6);
lean_inc(v_decl_2922_);
v___x_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2970_, 0, v_decl_2922_);
lean_ctor_set(v___x_2970_, 1, v_a_2955_);
v___f_2971_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2971_, 0, v_addEntryFn_2967_);
lean_closure_set(v___f_2971_, 1, v___x_2970_);
v___x_2972_ = 1;
if (v_logWrites_2969_ == 0)
{
lean_object* v___x_2973_; 
lean_inc(v_decl_2922_);
v___x_2973_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2957_, v_env_2958_, v___f_2971_, v_asyncMode_2968_, v_decl_2922_, v___x_2972_);
lean_dec(v_asyncMode_2968_);
v___y_2929_ = v___y_2952_;
v___y_2930_ = v___y_2951_;
v___y_2931_ = v___y_2953_;
v_nextMacroScope_2932_ = v_nextMacroScope_2959_;
v_ngen_2933_ = v_ngen_2960_;
v_auxDeclNGen_2934_ = v_auxDeclNGen_2961_;
v_traceState_2935_ = v_traceState_2962_;
v_recordedDeps_2936_ = v_recordedDeps_2963_;
v_messages_2937_ = v_messages_2964_;
v_infoState_2938_ = v_infoState_2965_;
v_snapshotTasks_2939_ = v_snapshotTasks_2966_;
v___y_2940_ = v_a_2955_;
v___y_2941_ = v___x_2973_;
goto v___jp_2928_;
}
else
{
lean_object* v___x_2974_; lean_object* v___x_2975_; 
lean_inc_n(v_decl_2922_, 2);
v___x_2974_ = l_Lean_Environment_logDeclChange(v_env_2958_, v_decl_2922_);
v___x_2975_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2957_, v___x_2974_, v___f_2971_, v_asyncMode_2968_, v_decl_2922_, v___x_2972_);
lean_dec(v_asyncMode_2968_);
v___y_2929_ = v___y_2952_;
v___y_2930_ = v___y_2951_;
v___y_2931_ = v___y_2953_;
v_nextMacroScope_2932_ = v_nextMacroScope_2959_;
v_ngen_2933_ = v_ngen_2960_;
v_auxDeclNGen_2934_ = v_auxDeclNGen_2961_;
v_traceState_2935_ = v_traceState_2962_;
v_recordedDeps_2936_ = v_recordedDeps_2963_;
v_messages_2937_ = v_messages_2964_;
v_infoState_2938_ = v_infoState_2965_;
v_snapshotTasks_2939_ = v_snapshotTasks_2966_;
v___y_2940_ = v_a_2955_;
v___y_2941_ = v___x_2975_;
goto v___jp_2928_;
}
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_dec_ref(v___y_2951_);
lean_dec(v_decl_2922_);
lean_dec_ref(v_ext_2920_);
lean_dec_ref(v_afterSet_2918_);
v_a_2976_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2954_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2954_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
v___jp_2984_:
{
lean_object* v___x_2985_; lean_object* v_env_2986_; lean_object* v___x_2987_; 
v___x_2985_ = lean_st_ref_get(v___y_2926_);
v_env_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc_ref(v_env_2986_);
lean_dec(v___x_2985_);
v___x_2987_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2986_, v_decl_2922_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_dec_ref(v_toAttributeImplCore_2921_);
v___y_2951_ = v_env_2986_;
v___y_2952_ = v___y_2925_;
v___y_2953_ = v___y_2926_;
goto v___jp_2950_;
}
else
{
lean_object* v_name_2988_; lean_object* v___x_2989_; 
lean_dec_ref_known(v___x_2987_, 1);
lean_dec_ref(v_env_2986_);
lean_dec(v_stx_2923_);
lean_dec_ref(v_ext_2920_);
lean_dec_ref(v_getParam_2919_);
lean_dec_ref(v_afterSet_2918_);
v_name_2988_ = lean_ctor_get(v_toAttributeImplCore_2921_, 1);
lean_inc(v_name_2988_);
lean_dec_ref(v_toAttributeImplCore_2921_);
v___x_2989_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2988_, v_decl_2922_, v___y_2925_, v___y_2926_);
return v___x_2989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object* v_afterSet_2994_, lean_object* v_getParam_2995_, lean_object* v_ext_2996_, lean_object* v_toAttributeImplCore_2997_, lean_object* v_decl_2998_, lean_object* v_stx_2999_, lean_object* v_kind_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
uint8_t v_kind_boxed_3004_; lean_object* v_res_3005_; 
v_kind_boxed_3004_ = lean_unbox(v_kind_3000_);
v_res_3005_ = l_Lean_registerParametricAttributeForExt___redArg___lam__1(v_afterSet_2994_, v_getParam_2995_, v_ext_2996_, v_toAttributeImplCore_2997_, v_decl_2998_, v_stx_2999_, v_kind_boxed_3004_, v___y_3001_, v___y_3002_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__2(lean_object* v_toAttributeImplCore_3006_, lean_object* v_decl_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_name_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v_name_3011_ = lean_ctor_get(v_toAttributeImplCore_3006_, 1);
lean_inc(v_name_3011_);
lean_dec_ref(v_toAttributeImplCore_3006_);
v___x_3012_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3013_ = l_Lean_MessageData_ofName(v_name_3011_);
v___x_3014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3012_);
lean_ctor_set(v___x_3014_, 1, v___x_3013_);
v___x_3015_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3014_);
lean_ctor_set(v___x_3016_, 1, v___x_3015_);
v___x_3017_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3016_, v___y_3008_, v___y_3009_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__2___boxed(lean_object* v_toAttributeImplCore_3018_, lean_object* v_decl_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Lean_registerParametricAttributeForExt___redArg___lam__2(v_toAttributeImplCore_3018_, v_decl_3019_, v___y_3020_, v___y_3021_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec(v_decl_3019_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object* v_impl_3024_, lean_object* v_ext_3025_){
_start:
{
lean_object* v_toAttributeImplCore_3027_; lean_object* v_getParam_3028_; lean_object* v_afterSet_3029_; uint8_t v_preserveOrder_3030_; lean_object* v___f_3031_; lean_object* v___f_3032_; lean_object* v_attrImpl_3033_; lean_object* v___x_3034_; 
v_toAttributeImplCore_3027_ = lean_ctor_get(v_impl_3024_, 0);
lean_inc_ref_n(v_toAttributeImplCore_3027_, 3);
v_getParam_3028_ = lean_ctor_get(v_impl_3024_, 1);
lean_inc_ref(v_getParam_3028_);
v_afterSet_3029_ = lean_ctor_get(v_impl_3024_, 2);
lean_inc_ref(v_afterSet_3029_);
v_preserveOrder_3030_ = lean_ctor_get_uint8(v_impl_3024_, sizeof(void*)*4);
lean_dec_ref(v_impl_3024_);
lean_inc_ref(v_ext_3025_);
v___f_3031_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3031_, 0, v_afterSet_3029_);
lean_closure_set(v___f_3031_, 1, v_getParam_3028_);
lean_closure_set(v___f_3031_, 2, v_ext_3025_);
lean_closure_set(v___f_3031_, 3, v_toAttributeImplCore_3027_);
v___f_3032_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__2___boxed), 5, 1);
lean_closure_set(v___f_3032_, 0, v_toAttributeImplCore_3027_);
v_attrImpl_3033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_attrImpl_3033_, 0, v_toAttributeImplCore_3027_);
lean_ctor_set(v_attrImpl_3033_, 1, v___f_3031_);
lean_ctor_set(v_attrImpl_3033_, 2, v___f_3032_);
lean_inc_ref(v_attrImpl_3033_);
v___x_3034_ = l_Lean_registerBuiltinAttribute(v_attrImpl_3033_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3042_; 
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3042_ == 0)
{
lean_object* v_unused_3043_; 
v_unused_3043_ = lean_ctor_get(v___x_3034_, 0);
lean_dec(v_unused_3043_);
v___x_3036_ = v___x_3034_;
v_isShared_3037_ = v_isSharedCheck_3042_;
goto v_resetjp_3035_;
}
else
{
lean_dec(v___x_3034_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3042_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3038_; lean_object* v___x_3040_; 
v___x_3038_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3038_, 0, v_attrImpl_3033_);
lean_ctor_set(v___x_3038_, 1, v_ext_3025_);
lean_ctor_set_uint8(v___x_3038_, sizeof(void*)*2, v_preserveOrder_3030_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v___x_3038_);
v___x_3040_ = v___x_3036_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec_ref_known(v_attrImpl_3033_, 3);
lean_dec_ref(v_ext_3025_);
v_a_3044_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3034_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3034_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object* v_impl_3052_, lean_object* v_ext_3053_, lean_object* v_a_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3052_, v_ext_3053_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object* v_00_u03b1_3056_, lean_object* v_impl_3057_, lean_object* v_ext_3058_){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3057_, v_ext_3058_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object* v_00_u03b1_3061_, lean_object* v_impl_3062_, lean_object* v_ext_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_registerParametricAttributeForExt(v_00_u03b1_3061_, v_impl_3062_, v_ext_3063_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_3066_){
_start:
{
lean_object* v_toAttributeImplCore_3068_; uint8_t v_preserveOrder_3069_; lean_object* v_filterExport_3070_; lean_object* v_ref_3071_; uint8_t v___x_3072_; lean_object* v___x_3073_; 
v_toAttributeImplCore_3068_ = lean_ctor_get(v_impl_3066_, 0);
v_preserveOrder_3069_ = lean_ctor_get_uint8(v_impl_3066_, sizeof(void*)*4);
v_filterExport_3070_ = lean_ctor_get(v_impl_3066_, 3);
v_ref_3071_ = lean_ctor_get(v_toAttributeImplCore_3068_, 0);
v___x_3072_ = 0;
lean_inc_ref(v_filterExport_3070_);
lean_inc(v_ref_3071_);
v___x_3073_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_3071_, v_preserveOrder_3069_, v_filterExport_3070_, v___x_3072_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3075_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_a_3074_);
lean_dec_ref_known(v___x_3073_, 1);
v___x_3075_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3066_, v_a_3074_);
return v___x_3075_;
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec_ref(v_impl_3066_);
v_a_3076_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3073_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3073_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lean_registerParametricAttribute___redArg(v_impl_3084_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_3087_, lean_object* v_impl_3088_){
_start:
{
lean_object* v___x_3090_; 
v___x_3090_ = l_Lean_registerParametricAttribute___redArg(v_impl_3088_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_3091_, lean_object* v_impl_3092_, lean_object* v_a_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_Lean_registerParametricAttribute(v_00_u03b1_3091_, v_impl_3092_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object* v_inst_3100_, lean_object* v_ext_3101_, uint8_t v_preserveOrder_3102_, lean_object* v_env_3103_, lean_object* v_decl_3104_){
_start:
{
lean_object* v___y_3106_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3118_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3103_, v_decl_3104_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_toEnvExtension_3119_; lean_object* v_asyncMode_3120_; lean_object* v___x_3121_; uint8_t v___x_3122_; lean_object* v___x_3123_; lean_object* v_snd_3124_; lean_object* v___x_3125_; 
lean_dec(v_inst_3100_);
v_toEnvExtension_3119_ = lean_ctor_get(v_ext_3101_, 0);
v_asyncMode_3120_ = lean_ctor_get(v_toEnvExtension_3119_, 2);
v___x_3121_ = lean_box(0);
v___x_3122_ = 0;
v___x_3123_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3117_, v_ext_3101_, v_env_3103_, v_asyncMode_3120_, v___x_3121_, v___x_3122_);
v_snd_3124_ = lean_ctor_get(v___x_3123_, 1);
lean_inc(v_snd_3124_);
lean_dec(v___x_3123_);
v___x_3125_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3124_, v_decl_3104_);
lean_dec(v_decl_3104_);
lean_dec(v_snd_3124_);
return v___x_3125_;
}
else
{
if (v_preserveOrder_3102_ == 0)
{
lean_object* v_val_3126_; uint8_t v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; 
v_val_3126_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_val_3126_);
lean_dec_ref_known(v___x_3118_, 1);
v___x_3127_ = 0;
v___x_3128_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3117_, v_ext_3101_, v_env_3103_, v_val_3126_, v___x_3127_);
lean_dec(v_val_3126_);
lean_dec_ref(v_env_3103_);
v___x_3129_ = lean_unsigned_to_nat(0u);
v___x_3130_ = lean_array_get_size(v___x_3128_);
v___x_3131_ = lean_nat_dec_lt(v___x_3129_, v___x_3130_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; 
lean_dec_ref(v___x_3128_);
lean_dec(v_decl_3104_);
lean_dec(v_inst_3100_);
v___x_3132_ = lean_box(0);
return v___x_3132_;
}
else
{
lean_object* v___x_3133_; lean_object* v___x_3134_; uint8_t v___x_3135_; 
v___x_3133_ = lean_unsigned_to_nat(1u);
v___x_3134_ = lean_nat_sub(v___x_3130_, v___x_3133_);
v___x_3135_ = lean_nat_dec_le(v___x_3129_, v___x_3134_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; 
lean_dec(v___x_3134_);
lean_dec_ref(v___x_3128_);
lean_dec(v_decl_3104_);
lean_dec(v_inst_3100_);
v___x_3136_ = lean_box(0);
return v___x_3136_;
}
else
{
lean_object* v___f_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___f_3137_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
v___x_3138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3138_, 0, v_decl_3104_);
lean_ctor_set(v___x_3138_, 1, v_inst_3100_);
v___x_3139_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3140_ = l_Array_binSearchAux___redArg(v___f_3137_, v___x_3139_, v___x_3128_, v___x_3138_, v___x_3129_, v___x_3134_);
lean_dec_ref(v___x_3128_);
v___y_3106_ = v___x_3140_;
goto v___jp_3105_;
}
}
}
else
{
lean_object* v_val_3141_; uint8_t v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
lean_dec(v_inst_3100_);
v_val_3141_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_val_3141_);
lean_dec_ref_known(v___x_3118_, 1);
v___x_3142_ = 0;
v___x_3143_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3117_, v_ext_3101_, v_env_3103_, v_val_3141_, v___x_3142_);
lean_dec(v_val_3141_);
lean_dec_ref(v_env_3103_);
v___x_3144_ = l_Lean_findByName_x3f___redArg(v___x_3143_, v_decl_3104_);
lean_dec(v_decl_3104_);
lean_dec_ref(v___x_3143_);
v___y_3106_ = v___x_3144_;
goto v___jp_3105_;
}
}
v___jp_3105_:
{
if (lean_obj_tag(v___y_3106_) == 0)
{
lean_object* v___x_3107_; 
v___x_3107_ = lean_box(0);
return v___x_3107_;
}
else
{
lean_object* v_val_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3116_; 
v_val_3108_ = lean_ctor_get(v___y_3106_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___y_3106_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3110_ = v___y_3106_;
v_isShared_3111_ = v_isSharedCheck_3116_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_val_3108_);
lean_dec(v___y_3106_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3116_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v_snd_3112_; lean_object* v___x_3114_; 
v_snd_3112_ = lean_ctor_get(v_val_3108_, 1);
lean_inc(v_snd_3112_);
lean_dec(v_val_3108_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v_snd_3112_);
v___x_3114_ = v___x_3110_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_snd_3112_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object* v_inst_3145_, lean_object* v_ext_3146_, lean_object* v_preserveOrder_3147_, lean_object* v_env_3148_, lean_object* v_decl_3149_){
_start:
{
uint8_t v_preserveOrder_boxed_3150_; lean_object* v_res_3151_; 
v_preserveOrder_boxed_3150_ = lean_unbox(v_preserveOrder_3147_);
v_res_3151_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3145_, v_ext_3146_, v_preserveOrder_boxed_3150_, v_env_3148_, v_decl_3149_);
lean_dec_ref(v_ext_3146_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object* v_00_u03b1_3152_, lean_object* v_inst_3153_, lean_object* v_ext_3154_, uint8_t v_preserveOrder_3155_, lean_object* v_env_3156_, lean_object* v_decl_3157_){
_start:
{
lean_object* v___x_3158_; 
v___x_3158_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3153_, v_ext_3154_, v_preserveOrder_3155_, v_env_3156_, v_decl_3157_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object* v_00_u03b1_3159_, lean_object* v_inst_3160_, lean_object* v_ext_3161_, lean_object* v_preserveOrder_3162_, lean_object* v_env_3163_, lean_object* v_decl_3164_){
_start:
{
uint8_t v_preserveOrder_boxed_3165_; lean_object* v_res_3166_; 
v_preserveOrder_boxed_3165_ = lean_unbox(v_preserveOrder_3162_);
v_res_3166_ = l_Lean_ParametricAttribute_getParamFromExt_x3f(v_00_u03b1_3159_, v_inst_3160_, v_ext_3161_, v_preserveOrder_boxed_3165_, v_env_3163_, v_decl_3164_);
lean_dec_ref(v_ext_3161_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3167_, lean_object* v_attr_3168_, lean_object* v_env_3169_, lean_object* v_decl_3170_){
_start:
{
lean_object* v_ext_3171_; uint8_t v_preserveOrder_3172_; lean_object* v___x_3173_; 
v_ext_3171_ = lean_ctor_get(v_attr_3168_, 1);
v_preserveOrder_3172_ = lean_ctor_get_uint8(v_attr_3168_, sizeof(void*)*2);
v___x_3173_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3167_, v_ext_3171_, v_preserveOrder_3172_, v_env_3169_, v_decl_3170_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3174_, lean_object* v_attr_3175_, lean_object* v_env_3176_, lean_object* v_decl_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3174_, v_attr_3175_, v_env_3176_, v_decl_3177_);
lean_dec_ref(v_attr_3175_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3179_, lean_object* v_inst_3180_, lean_object* v_attr_3181_, lean_object* v_env_3182_, lean_object* v_decl_3183_){
_start:
{
lean_object* v___x_3184_; 
v___x_3184_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3180_, v_attr_3181_, v_env_3182_, v_decl_3183_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3185_, lean_object* v_inst_3186_, lean_object* v_attr_3187_, lean_object* v_env_3188_, lean_object* v_decl_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3185_, v_inst_3186_, v_attr_3187_, v_env_3188_, v_decl_3189_);
lean_dec_ref(v_attr_3187_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object* v_ext_3195_, lean_object* v_attr_3196_, lean_object* v_env_3197_, lean_object* v_decl_3198_, lean_object* v_param_3199_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3197_, v_decl_3198_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_toEnvExtension_3201_; lean_object* v_addEntryFn_3202_; lean_object* v_asyncMode_3203_; uint8_t v_logWrites_3204_; uint8_t v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v_snd_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3244_; 
v_toEnvExtension_3201_ = lean_ctor_get(v_ext_3195_, 0);
lean_inc_ref(v_toEnvExtension_3201_);
v_addEntryFn_3202_ = lean_ctor_get(v_ext_3195_, 3);
lean_inc(v_addEntryFn_3202_);
v_asyncMode_3203_ = lean_ctor_get(v_toEnvExtension_3201_, 2);
lean_inc(v_asyncMode_3203_);
v_logWrites_3204_ = lean_ctor_get_uint8(v_toEnvExtension_3201_, sizeof(void*)*6);
v___x_3205_ = 0;
v___x_3206_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3207_ = lean_box(0);
lean_inc_ref(v_env_3197_);
v___x_3208_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3206_, v_ext_3195_, v_env_3197_, v_asyncMode_3203_, v___x_3207_, v___x_3205_);
lean_dec_ref(v_ext_3195_);
v_snd_3209_ = lean_ctor_get(v___x_3208_, 1);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3244_ == 0)
{
lean_object* v_unused_3245_; 
v_unused_3245_ = lean_ctor_get(v___x_3208_, 0);
lean_dec(v_unused_3245_);
v___x_3211_ = v___x_3208_;
v_isShared_3212_ = v_isSharedCheck_3244_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_snd_3209_);
lean_dec(v___x_3208_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3244_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3213_; 
v___x_3213_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3209_, v_decl_3198_);
lean_dec(v_snd_3209_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v___x_3215_; 
lean_dec_ref(v_attr_3196_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 1, v_param_3199_);
lean_ctor_set(v___x_3211_, 0, v_decl_3198_);
v___x_3215_ = v___x_3211_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_decl_3198_);
lean_ctor_set(v_reuseFailAlloc_3223_, 1, v_param_3199_);
v___x_3215_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
lean_object* v___f_3216_; uint8_t v___x_3217_; 
v___f_3216_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3216_, 0, v_addEntryFn_3202_);
lean_closure_set(v___f_3216_, 1, v___x_3215_);
v___x_3217_ = 1;
if (v_logWrites_3204_ == 0)
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3201_, v_env_3197_, v___f_3216_, v_asyncMode_3203_, v___x_3207_, v___x_3217_);
lean_dec(v_asyncMode_3203_);
v___x_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
return v___x_3219_;
}
else
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
lean_inc_ref(v_toEnvExtension_3201_);
v___x_3220_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3201_, v_env_3197_);
lean_dec_ref(v_env_3197_);
v___x_3221_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3201_, v___x_3220_, v___f_3216_, v_asyncMode_3203_, v___x_3207_, v___x_3217_);
lean_dec(v_asyncMode_3203_);
v___x_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
return v___x_3222_;
}
}
}
else
{
lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3242_; 
lean_del_object(v___x_3211_);
lean_dec(v_asyncMode_3203_);
lean_dec(v_addEntryFn_3202_);
lean_dec_ref(v_toEnvExtension_3201_);
lean_dec(v_param_3199_);
lean_dec_ref(v_env_3197_);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3242_ == 0)
{
lean_object* v_unused_3243_; 
v_unused_3243_ = lean_ctor_get(v___x_3213_, 0);
lean_dec(v_unused_3243_);
v___x_3225_ = v___x_3213_;
v_isShared_3226_ = v_isSharedCheck_3242_;
goto v_resetjp_3224_;
}
else
{
lean_dec(v___x_3213_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3242_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v_toAttributeImplCore_3227_; lean_object* v_name_3228_; uint8_t v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3240_; 
v_toAttributeImplCore_3227_ = lean_ctor_get(v_attr_3196_, 0);
lean_inc_ref(v_toAttributeImplCore_3227_);
lean_dec_ref(v_attr_3196_);
v_name_3228_ = lean_ctor_get(v_toAttributeImplCore_3227_, 1);
lean_inc(v_name_3228_);
lean_dec_ref(v_toAttributeImplCore_3227_);
v___x_3229_ = 1;
v___x_3230_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3231_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3228_, v___x_3229_);
v___x_3232_ = lean_string_append(v___x_3230_, v___x_3231_);
lean_dec_ref(v___x_3231_);
v___x_3233_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3234_ = lean_string_append(v___x_3232_, v___x_3233_);
v___x_3235_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3198_, v___x_3229_);
v___x_3236_ = lean_string_append(v___x_3234_, v___x_3235_);
lean_dec_ref(v___x_3235_);
v___x_3237_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2));
v___x_3238_ = lean_string_append(v___x_3236_, v___x_3237_);
if (v_isShared_3226_ == 0)
{
lean_ctor_set_tag(v___x_3225_, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3238_);
v___x_3240_ = v___x_3225_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
}
else
{
lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3264_; 
lean_dec(v_param_3199_);
lean_dec_ref(v_env_3197_);
lean_dec_ref(v_ext_3195_);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3264_ == 0)
{
lean_object* v_unused_3265_; 
v_unused_3265_ = lean_ctor_get(v___x_3200_, 0);
lean_dec(v_unused_3265_);
v___x_3247_ = v___x_3200_;
v_isShared_3248_ = v_isSharedCheck_3264_;
goto v_resetjp_3246_;
}
else
{
lean_dec(v___x_3200_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3264_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v_toAttributeImplCore_3249_; lean_object* v_name_3250_; uint8_t v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3262_; 
v_toAttributeImplCore_3249_ = lean_ctor_get(v_attr_3196_, 0);
lean_inc_ref(v_toAttributeImplCore_3249_);
lean_dec_ref(v_attr_3196_);
v_name_3250_ = lean_ctor_get(v_toAttributeImplCore_3249_, 1);
lean_inc(v_name_3250_);
lean_dec_ref(v_toAttributeImplCore_3249_);
v___x_3251_ = 1;
v___x_3252_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3253_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3250_, v___x_3251_);
v___x_3254_ = lean_string_append(v___x_3252_, v___x_3253_);
lean_dec_ref(v___x_3253_);
v___x_3255_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3256_ = lean_string_append(v___x_3254_, v___x_3255_);
v___x_3257_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3198_, v___x_3251_);
v___x_3258_ = lean_string_append(v___x_3256_, v___x_3257_);
lean_dec_ref(v___x_3257_);
v___x_3259_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3));
v___x_3260_ = lean_string_append(v___x_3258_, v___x_3259_);
if (v_isShared_3248_ == 0)
{
lean_ctor_set_tag(v___x_3247_, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3260_);
v___x_3262_ = v___x_3247_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object* v_00_u03b1_3266_, lean_object* v_ext_3267_, lean_object* v_attr_3268_, lean_object* v_env_3269_, lean_object* v_decl_3270_, lean_object* v_param_3271_){
_start:
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3267_, v_attr_3268_, v_env_3269_, v_decl_3270_, v_param_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3273_, lean_object* v_env_3274_, lean_object* v_decl_3275_, lean_object* v_param_3276_){
_start:
{
lean_object* v_attr_3277_; lean_object* v_ext_3278_; lean_object* v___x_3279_; 
v_attr_3277_ = lean_ctor_get(v_attr_3273_, 0);
lean_inc_ref(v_attr_3277_);
v_ext_3278_ = lean_ctor_get(v_attr_3273_, 1);
lean_inc_ref(v_ext_3278_);
lean_dec_ref(v_attr_3273_);
v___x_3279_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3278_, v_attr_3277_, v_env_3274_, v_decl_3275_, v_param_3276_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3280_, lean_object* v_attr_3281_, lean_object* v_env_3282_, lean_object* v_decl_3283_, lean_object* v_param_3284_){
_start:
{
lean_object* v___x_3285_; 
v___x_3285_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3281_, v_env_3282_, v_decl_3283_, v_param_3284_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(lean_object* v_x_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0___boxed(lean_object* v_x_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(v_x_3291_, v___y_3292_);
lean_dec_ref(v___y_3292_);
lean_dec_ref(v_x_3291_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(lean_object* v_s_3295_, lean_object* v_x_3296_){
_start:
{
lean_inc(v_s_3295_);
return v_s_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1___boxed(lean_object* v_s_3297_, lean_object* v_x_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(v_s_3297_, v_x_3298_);
lean_dec_ref(v_x_3298_);
lean_dec(v_s_3297_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(lean_object* v_x_3300_, lean_object* v_x_3301_){
_start:
{
lean_object* v___x_3302_; 
v___x_3302_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2___boxed(lean_object* v_x_3303_, lean_object* v_x_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(v_x_3303_, v_x_3304_);
lean_dec(v_x_3304_);
lean_dec_ref(v_x_3303_);
return v_res_3305_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3(void){
_start:
{
lean_object* v___f_3309_; lean_object* v___f_3310_; lean_object* v___f_3311_; lean_object* v___f_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___f_3309_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3310_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2));
v___f_3311_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1));
v___f_3312_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0));
v___x_3313_ = lean_box(0);
v___x_3314_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_3315_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3314_);
lean_ctor_set(v___x_3315_, 1, v___x_3313_);
lean_ctor_set(v___x_3315_, 2, v___f_3312_);
lean_ctor_set(v___x_3315_, 3, v___f_3311_);
lean_ctor_set(v___x_3315_, 4, v___f_3310_);
lean_ctor_set(v___x_3315_, 5, v___f_3309_);
return v___x_3315_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3316_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3);
v___x_3317_ = lean_box(0);
v___x_3318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3317_);
lean_ctor_set(v___x_3318_, 1, v___x_3316_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg(){
_start:
{
lean_object* v___x_3320_; 
v___x_3320_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___boxed(lean_object* v___dummy_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v_res_3322_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__0(void){
_start:
{
lean_object* v___x_3323_; 
v___x_3323_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3324_){
_start:
{
lean_object* v___x_3325_; 
v___x_3325_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg(){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg___boxed(lean_object* v___dummy_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_Lean_instInhabitedEnumAttributes___redArg();
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3330_){
_start:
{
lean_object* v___x_3331_; 
v___x_3331_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3331_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3332_; 
v___x_3332_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3333_){
_start:
{
lean_object* v___x_3334_; 
v___x_3334_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3335_);
lean_dec(v_x_3335_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3337_, lean_object* v_x_3338_, lean_object* v_x_3339_){
_start:
{
if (lean_obj_tag(v_x_3339_) == 0)
{
return v_x_3338_;
}
else
{
lean_object* v_head_3340_; lean_object* v_tail_3341_; lean_object* v___x_3342_; 
v_head_3340_ = lean_ctor_get(v_x_3339_, 0);
lean_inc(v_head_3340_);
v_tail_3341_ = lean_ctor_get(v_x_3339_, 1);
lean_inc(v_tail_3341_);
lean_dec_ref_known(v_x_3339_, 2);
v___x_3342_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3337_, v_head_3340_);
if (lean_obj_tag(v___x_3342_) == 1)
{
lean_object* v_val_3343_; lean_object* v___x_3344_; 
v_val_3343_ = lean_ctor_get(v___x_3342_, 0);
lean_inc(v_val_3343_);
lean_dec_ref_known(v___x_3342_, 1);
v___x_3344_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3340_, v_val_3343_, v_x_3338_);
v_x_3338_ = v___x_3344_;
v_x_3339_ = v_tail_3341_;
goto _start;
}
else
{
lean_dec(v___x_3342_);
lean_dec(v_head_3340_);
v_x_3339_ = v_tail_3341_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3347_, lean_object* v_x_3348_, lean_object* v_x_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3347_, v_x_3348_, v_x_3349_);
lean_dec(v_newState_3347_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3351_, lean_object* v_newState_3352_, lean_object* v_consts_3353_, lean_object* v_st_3354_){
_start:
{
lean_object* v___x_3355_; 
v___x_3355_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3352_, v_st_3354_, v_consts_3353_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3356_, lean_object* v_newState_3357_, lean_object* v_consts_3358_, lean_object* v_st_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3356_, v_newState_3357_, v_consts_3358_, v_st_3359_);
lean_dec(v_newState_3357_);
lean_dec(v_x_3356_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3370_){
_start:
{
lean_object* v___x_3371_; lean_object* v___y_3373_; 
v___x_3371_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3370_) == 0)
{
lean_object* v_size_3377_; 
v_size_3377_ = lean_ctor_get(v_s_3370_, 0);
lean_inc(v_size_3377_);
lean_dec_ref_known(v_s_3370_, 5);
v___y_3373_ = v_size_3377_;
goto v___jp_3372_;
}
else
{
lean_object* v___x_3378_; 
v___x_3378_ = lean_unsigned_to_nat(0u);
v___y_3373_ = v___x_3378_;
goto v___jp_3372_;
}
v___jp_3372_:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3374_ = l_Nat_reprFast(v___y_3373_);
v___x_3375_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
v___x_3376_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3371_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
return v___x_3376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3379_, lean_object* v_as_3380_, size_t v_i_3381_, size_t v_stop_3382_, lean_object* v_b_3383_){
_start:
{
lean_object* v___y_3385_; uint8_t v___x_3389_; 
v___x_3389_ = lean_usize_dec_eq(v_i_3381_, v_stop_3382_);
if (v___x_3389_ == 0)
{
lean_object* v___x_3390_; lean_object* v_fst_3391_; uint8_t v___x_3392_; lean_object* v___x_3393_; uint8_t v___x_3394_; 
v___x_3390_ = lean_array_uget_borrowed(v_as_3380_, v_i_3381_);
v_fst_3391_ = lean_ctor_get(v___x_3390_, 0);
v___x_3392_ = 1;
lean_inc_ref(v_env_3379_);
v___x_3393_ = l_Lean_Environment_setExporting(v_env_3379_, v___x_3392_);
lean_inc(v_fst_3391_);
v___x_3394_ = l_Lean_Environment_contains(v___x_3393_, v_fst_3391_, v___x_3392_);
if (v___x_3394_ == 0)
{
v___y_3385_ = v_b_3383_;
goto v___jp_3384_;
}
else
{
lean_object* v___x_3395_; 
lean_inc(v___x_3390_);
v___x_3395_ = lean_array_push(v_b_3383_, v___x_3390_);
v___y_3385_ = v___x_3395_;
goto v___jp_3384_;
}
}
else
{
lean_dec_ref(v_env_3379_);
return v_b_3383_;
}
v___jp_3384_:
{
size_t v___x_3386_; size_t v___x_3387_; 
v___x_3386_ = ((size_t)1ULL);
v___x_3387_ = lean_usize_add(v_i_3381_, v___x_3386_);
v_i_3381_ = v___x_3387_;
v_b_3383_ = v___y_3385_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3396_, lean_object* v_as_3397_, lean_object* v_i_3398_, lean_object* v_stop_3399_, lean_object* v_b_3400_){
_start:
{
size_t v_i_boxed_3401_; size_t v_stop_boxed_3402_; lean_object* v_res_3403_; 
v_i_boxed_3401_ = lean_unbox_usize(v_i_3398_);
lean_dec(v_i_3398_);
v_stop_boxed_3402_ = lean_unbox_usize(v_stop_3399_);
lean_dec(v_stop_3399_);
v_res_3403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3396_, v_as_3397_, v_i_boxed_3401_, v_stop_boxed_3402_, v_b_3400_);
lean_dec_ref(v_as_3397_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3404_, lean_object* v_m_3405_){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___y_3409_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___y_3420_; lean_object* v___y_3421_; uint8_t v___x_3423_; 
v___x_3406_ = lean_unsigned_to_nat(0u);
v___x_3407_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_3417_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_3407_, v_m_3405_);
v___x_3418_ = lean_array_get_size(v___x_3417_);
v___x_3423_ = lean_nat_dec_eq(v___x_3418_, v___x_3406_);
if (v___x_3423_ == 0)
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___y_3427_; uint8_t v___x_3429_; 
v___x_3424_ = lean_unsigned_to_nat(1u);
v___x_3425_ = lean_nat_sub(v___x_3418_, v___x_3424_);
v___x_3429_ = lean_nat_dec_le(v___x_3406_, v___x_3425_);
if (v___x_3429_ == 0)
{
lean_inc(v___x_3425_);
v___y_3427_ = v___x_3425_;
goto v___jp_3426_;
}
else
{
v___y_3427_ = v___x_3406_;
goto v___jp_3426_;
}
v___jp_3426_:
{
uint8_t v___x_3428_; 
v___x_3428_ = lean_nat_dec_le(v___y_3427_, v___x_3425_);
if (v___x_3428_ == 0)
{
lean_dec(v___x_3425_);
lean_inc(v___y_3427_);
v___y_3420_ = v___y_3427_;
v___y_3421_ = v___y_3427_;
goto v___jp_3419_;
}
else
{
v___y_3420_ = v___y_3427_;
v___y_3421_ = v___x_3425_;
goto v___jp_3419_;
}
}
}
else
{
v___y_3409_ = v___x_3417_;
goto v___jp_3408_;
}
v___jp_3408_:
{
lean_object* v___x_3410_; uint8_t v___x_3411_; 
v___x_3410_ = lean_array_get_size(v___y_3409_);
v___x_3411_ = lean_nat_dec_lt(v___x_3406_, v___x_3410_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3412_; 
lean_dec_ref(v_env_3404_);
v___x_3412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3407_);
lean_ctor_set(v___x_3412_, 1, v___x_3407_);
lean_ctor_set(v___x_3412_, 2, v___y_3409_);
return v___x_3412_;
}
else
{
size_t v___x_3413_; size_t v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3413_ = ((size_t)0ULL);
v___x_3414_ = lean_usize_of_nat(v___x_3410_);
v___x_3415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3404_, v___y_3409_, v___x_3413_, v___x_3414_, v___x_3407_);
lean_inc_ref(v___x_3415_);
v___x_3416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
lean_ctor_set(v___x_3416_, 2, v___y_3409_);
return v___x_3416_;
}
}
v___jp_3419_:
{
lean_object* v___x_3422_; 
v___x_3422_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_3418_, v___x_3417_, v___y_3420_, v___y_3421_);
lean_dec(v___y_3421_);
v___y_3409_ = v___x_3422_;
goto v___jp_3408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3430_, lean_object* v_m_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3430_, v_m_3431_);
lean_dec(v_m_3431_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3433_, lean_object* v_p_3434_){
_start:
{
lean_object* v_fst_3435_; lean_object* v_snd_3436_; lean_object* v___x_3437_; 
v_fst_3435_ = lean_ctor_get(v_p_3434_, 0);
lean_inc(v_fst_3435_);
v_snd_3436_ = lean_ctor_get(v_p_3434_, 1);
lean_inc(v_snd_3436_);
lean_dec_ref(v_p_3434_);
v___x_3437_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3435_, v_snd_3436_, v_s_3433_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3438_, lean_object* v_x_3439_, lean_object* v_x_3440_){
_start:
{
lean_object* v___x_3442_; 
v___x_3442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3438_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3443_, lean_object* v_x_3444_, lean_object* v_x_3445_, lean_object* v___y_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3443_, v_x_3444_, v_x_3445_);
lean_dec_ref(v_x_3445_);
lean_dec_ref(v_x_3444_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3448_){
_start:
{
if (lean_obj_tag(v_as_3448_) == 0)
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3450_ = lean_box(0);
v___x_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
return v___x_3451_;
}
else
{
lean_object* v_head_3452_; lean_object* v_tail_3453_; lean_object* v___x_3454_; 
v_head_3452_ = lean_ctor_get(v_as_3448_, 0);
lean_inc(v_head_3452_);
v_tail_3453_ = lean_ctor_get(v_as_3448_, 1);
lean_inc(v_tail_3453_);
lean_dec_ref_known(v_as_3448_, 2);
v___x_3454_ = l_Lean_registerBuiltinAttribute(v_head_3452_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_dec_ref_known(v___x_3454_, 1);
v_as_3448_ = v_tail_3453_;
goto _start;
}
else
{
lean_dec(v_tail_3453_);
return v___x_3454_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3456_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_addEntryFn_3459_, lean_object* v___x_3460_, lean_object* v_s_3461_){
_start:
{
lean_object* v_importedEntries_3462_; lean_object* v_state_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3471_; 
v_importedEntries_3462_ = lean_ctor_get(v_s_3461_, 0);
v_state_3463_ = lean_ctor_get(v_s_3461_, 1);
v_isSharedCheck_3471_ = !lean_is_exclusive(v_s_3461_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3465_ = v_s_3461_;
v_isShared_3466_ = v_isSharedCheck_3471_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_state_3463_);
lean_inc(v_importedEntries_3462_);
lean_dec(v_s_3461_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3471_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v_state_3467_; lean_object* v___x_3469_; 
v_state_3467_ = lean_apply_2(v_addEntryFn_3459_, v_state_3463_, v___x_3460_);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 1, v_state_3467_);
v___x_3469_ = v___x_3465_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_importedEntries_3462_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_state_3467_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2(lean_object* v_validate_3472_, lean_object* v_snd_3473_, lean_object* v_a_3474_, lean_object* v_fst_3475_, lean_object* v_decl_3476_, lean_object* v_stx_3477_, uint8_t v_kind_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v_nextMacroScope_3485_; lean_object* v_ngen_3486_; lean_object* v_auxDeclNGen_3487_; lean_object* v_traceState_3488_; lean_object* v_recordedDeps_3489_; lean_object* v_messages_3490_; lean_object* v_infoState_3491_; lean_object* v_snapshotTasks_3492_; lean_object* v___y_3493_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___x_3528_; 
v___x_3528_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3477_, v___y_3479_, v___y_3480_);
if (lean_obj_tag(v___x_3528_) == 0)
{
uint8_t v___x_3529_; uint8_t v___x_3530_; 
lean_dec_ref_known(v___x_3528_, 1);
v___x_3529_ = 0;
v___x_3530_ = l_Lean_instBEqAttributeKind_beq(v_kind_3478_, v___x_3529_);
if (v___x_3530_ == 0)
{
lean_object* v___x_3531_; 
lean_dec(v_decl_3476_);
lean_dec_ref(v_a_3474_);
lean_dec(v_snd_3473_);
lean_dec_ref(v_validate_3472_);
v___x_3531_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3475_, v_kind_3478_, v___y_3479_, v___y_3480_);
return v___x_3531_;
}
else
{
goto v___jp_3523_;
}
}
else
{
lean_dec(v_decl_3476_);
lean_dec(v_fst_3475_);
lean_dec_ref(v_a_3474_);
lean_dec(v_snd_3473_);
lean_dec_ref(v_validate_3472_);
return v___x_3528_;
}
v___jp_3482_:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3494_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_3495_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3495_, 0, v___y_3493_);
lean_ctor_set(v___x_3495_, 1, v_nextMacroScope_3485_);
lean_ctor_set(v___x_3495_, 2, v_ngen_3486_);
lean_ctor_set(v___x_3495_, 3, v_auxDeclNGen_3487_);
lean_ctor_set(v___x_3495_, 4, v_traceState_3488_);
lean_ctor_set(v___x_3495_, 5, v___x_3494_);
lean_ctor_set(v___x_3495_, 6, v_recordedDeps_3489_);
lean_ctor_set(v___x_3495_, 7, v_messages_3490_);
lean_ctor_set(v___x_3495_, 8, v_infoState_3491_);
lean_ctor_set(v___x_3495_, 9, v_snapshotTasks_3492_);
v___x_3496_ = lean_st_ref_put(v___y_3483_, v___x_3495_);
v___x_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3497_, 0, v___y_3484_);
return v___x_3497_;
}
v___jp_3498_:
{
lean_object* v___x_3501_; 
lean_inc(v___y_3500_);
lean_inc_ref(v___y_3499_);
lean_inc(v_snd_3473_);
lean_inc(v_decl_3476_);
v___x_3501_ = lean_apply_5(v_validate_3472_, v_decl_3476_, v_snd_3473_, v___y_3499_, v___y_3500_, lean_box(0));
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v___x_3502_; lean_object* v_toEnvExtension_3503_; lean_object* v_env_3504_; lean_object* v_nextMacroScope_3505_; lean_object* v_ngen_3506_; lean_object* v_auxDeclNGen_3507_; lean_object* v_traceState_3508_; lean_object* v_recordedDeps_3509_; lean_object* v_messages_3510_; lean_object* v_infoState_3511_; lean_object* v_snapshotTasks_3512_; lean_object* v_addEntryFn_3513_; lean_object* v_asyncMode_3514_; uint8_t v_logWrites_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___f_3518_; uint8_t v___x_3519_; 
lean_dec_ref_known(v___x_3501_, 1);
v___x_3502_ = lean_st_ref_take(v___y_3500_);
v_toEnvExtension_3503_ = lean_ctor_get(v_a_3474_, 0);
lean_inc_ref(v_toEnvExtension_3503_);
v_env_3504_ = lean_ctor_get(v___x_3502_, 0);
lean_inc_ref(v_env_3504_);
v_nextMacroScope_3505_ = lean_ctor_get(v___x_3502_, 1);
lean_inc(v_nextMacroScope_3505_);
v_ngen_3506_ = lean_ctor_get(v___x_3502_, 2);
lean_inc_ref(v_ngen_3506_);
v_auxDeclNGen_3507_ = lean_ctor_get(v___x_3502_, 3);
lean_inc_ref(v_auxDeclNGen_3507_);
v_traceState_3508_ = lean_ctor_get(v___x_3502_, 4);
lean_inc_ref(v_traceState_3508_);
v_recordedDeps_3509_ = lean_ctor_get(v___x_3502_, 6);
lean_inc_ref(v_recordedDeps_3509_);
v_messages_3510_ = lean_ctor_get(v___x_3502_, 7);
lean_inc_ref(v_messages_3510_);
v_infoState_3511_ = lean_ctor_get(v___x_3502_, 8);
lean_inc_ref(v_infoState_3511_);
v_snapshotTasks_3512_ = lean_ctor_get(v___x_3502_, 9);
lean_inc_ref(v_snapshotTasks_3512_);
lean_dec(v___x_3502_);
v_addEntryFn_3513_ = lean_ctor_get(v_a_3474_, 3);
lean_inc(v_addEntryFn_3513_);
lean_dec_ref(v_a_3474_);
v_asyncMode_3514_ = lean_ctor_get(v_toEnvExtension_3503_, 2);
lean_inc(v_asyncMode_3514_);
v_logWrites_3515_ = lean_ctor_get_uint8(v_toEnvExtension_3503_, sizeof(void*)*6);
v___x_3516_ = lean_box(0);
lean_inc(v_decl_3476_);
v___x_3517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3517_, 0, v_decl_3476_);
lean_ctor_set(v___x_3517_, 1, v_snd_3473_);
v___f_3518_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3518_, 0, v_addEntryFn_3513_);
lean_closure_set(v___f_3518_, 1, v___x_3517_);
v___x_3519_ = 1;
if (v_logWrites_3515_ == 0)
{
lean_object* v___x_3520_; 
v___x_3520_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3503_, v_env_3504_, v___f_3518_, v_asyncMode_3514_, v_decl_3476_, v___x_3519_);
lean_dec(v_asyncMode_3514_);
v___y_3483_ = v___y_3500_;
v___y_3484_ = v___x_3516_;
v_nextMacroScope_3485_ = v_nextMacroScope_3505_;
v_ngen_3486_ = v_ngen_3506_;
v_auxDeclNGen_3487_ = v_auxDeclNGen_3507_;
v_traceState_3488_ = v_traceState_3508_;
v_recordedDeps_3489_ = v_recordedDeps_3509_;
v_messages_3490_ = v_messages_3510_;
v_infoState_3491_ = v_infoState_3511_;
v_snapshotTasks_3492_ = v_snapshotTasks_3512_;
v___y_3493_ = v___x_3520_;
goto v___jp_3482_;
}
else
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
lean_inc_ref(v_toEnvExtension_3503_);
v___x_3521_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3503_, v_env_3504_);
lean_dec_ref(v_env_3504_);
v___x_3522_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3503_, v___x_3521_, v___f_3518_, v_asyncMode_3514_, v_decl_3476_, v___x_3519_);
lean_dec(v_asyncMode_3514_);
v___y_3483_ = v___y_3500_;
v___y_3484_ = v___x_3516_;
v_nextMacroScope_3485_ = v_nextMacroScope_3505_;
v_ngen_3486_ = v_ngen_3506_;
v_auxDeclNGen_3487_ = v_auxDeclNGen_3507_;
v_traceState_3488_ = v_traceState_3508_;
v_recordedDeps_3489_ = v_recordedDeps_3509_;
v_messages_3490_ = v_messages_3510_;
v_infoState_3491_ = v_infoState_3511_;
v_snapshotTasks_3492_ = v_snapshotTasks_3512_;
v___y_3493_ = v___x_3522_;
goto v___jp_3482_;
}
}
else
{
lean_dec(v_decl_3476_);
lean_dec_ref(v_a_3474_);
lean_dec(v_snd_3473_);
return v___x_3501_;
}
}
v___jp_3523_:
{
lean_object* v___x_3524_; lean_object* v_env_3525_; lean_object* v___x_3526_; 
v___x_3524_ = lean_st_ref_get(v___y_3480_);
v_env_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc_ref(v_env_3525_);
lean_dec(v___x_3524_);
v___x_3526_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3525_, v_decl_3476_);
lean_dec_ref(v_env_3525_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_dec(v_fst_3475_);
v___y_3499_ = v___y_3479_;
v___y_3500_ = v___y_3480_;
goto v___jp_3498_;
}
else
{
lean_object* v___x_3527_; 
lean_dec_ref_known(v___x_3526_, 1);
lean_dec_ref(v_a_3474_);
lean_dec(v_snd_3473_);
lean_dec_ref(v_validate_3472_);
v___x_3527_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3475_, v_decl_3476_, v___y_3479_, v___y_3480_);
return v___x_3527_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2___boxed(lean_object* v_validate_3532_, lean_object* v_snd_3533_, lean_object* v_a_3534_, lean_object* v_fst_3535_, lean_object* v_decl_3536_, lean_object* v_stx_3537_, lean_object* v_kind_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
uint8_t v_kind_boxed_3542_; lean_object* v_res_3543_; 
v_kind_boxed_3542_ = lean_unbox(v_kind_3538_);
v_res_3543_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2(v_validate_3532_, v_snd_3533_, v_a_3534_, v_fst_3535_, v_decl_3536_, v_stx_3537_, v_kind_boxed_3542_, v___y_3539_, v___y_3540_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3544_, lean_object* v_decl_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3549_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3550_ = l_Lean_MessageData_ofName(v_fst_3544_);
v___x_3551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3549_);
lean_ctor_set(v___x_3551_, 1, v___x_3550_);
v___x_3552_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3551_);
lean_ctor_set(v___x_3553_, 1, v___x_3552_);
v___x_3554_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3553_, v___y_3546_, v___y_3547_);
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3555_, lean_object* v_decl_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3555_, v_decl_3556_, v___y_3557_, v___y_3558_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v_decl_3556_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3561_, lean_object* v_a_3562_, lean_object* v_ref_3563_, uint8_t v_applicationTime_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_){
_start:
{
if (lean_obj_tag(v_a_3565_) == 0)
{
lean_object* v___x_3567_; 
lean_dec(v_ref_3563_);
lean_dec_ref(v_a_3562_);
lean_dec_ref(v_validate_3561_);
v___x_3567_ = l_List_reverse___redArg(v_a_3566_);
return v___x_3567_;
}
else
{
lean_object* v_head_3568_; lean_object* v_snd_3569_; lean_object* v_tail_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3585_; 
v_head_3568_ = lean_ctor_get(v_a_3565_, 0);
lean_inc(v_head_3568_);
v_snd_3569_ = lean_ctor_get(v_head_3568_, 1);
lean_inc(v_snd_3569_);
v_tail_3570_ = lean_ctor_get(v_a_3565_, 1);
v_isSharedCheck_3585_ = !lean_is_exclusive(v_a_3565_);
if (v_isSharedCheck_3585_ == 0)
{
lean_object* v_unused_3586_; 
v_unused_3586_ = lean_ctor_get(v_a_3565_, 0);
lean_dec(v_unused_3586_);
v___x_3572_ = v_a_3565_;
v_isShared_3573_ = v_isSharedCheck_3585_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_tail_3570_);
lean_dec(v_a_3565_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3585_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v_fst_3574_; lean_object* v_fst_3575_; lean_object* v_snd_3576_; lean_object* v___f_3577_; lean_object* v___f_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3582_; 
v_fst_3574_ = lean_ctor_get(v_head_3568_, 0);
lean_inc_n(v_fst_3574_, 3);
lean_dec(v_head_3568_);
v_fst_3575_ = lean_ctor_get(v_snd_3569_, 0);
lean_inc(v_fst_3575_);
v_snd_3576_ = lean_ctor_get(v_snd_3569_, 1);
lean_inc(v_snd_3576_);
lean_dec(v_snd_3569_);
v___f_3577_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3577_, 0, v_fst_3574_);
lean_inc_ref(v_a_3562_);
lean_inc_ref(v_validate_3561_);
v___f_3578_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2___boxed), 10, 4);
lean_closure_set(v___f_3578_, 0, v_validate_3561_);
lean_closure_set(v___f_3578_, 1, v_snd_3576_);
lean_closure_set(v___f_3578_, 2, v_a_3562_);
lean_closure_set(v___f_3578_, 3, v_fst_3574_);
lean_inc(v_ref_3563_);
v___x_3579_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3579_, 0, v_ref_3563_);
lean_ctor_set(v___x_3579_, 1, v_fst_3574_);
lean_ctor_set(v___x_3579_, 2, v_fst_3575_);
lean_ctor_set_uint8(v___x_3579_, sizeof(void*)*3, v_applicationTime_3564_);
v___x_3580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3579_);
lean_ctor_set(v___x_3580_, 1, v___f_3578_);
lean_ctor_set(v___x_3580_, 2, v___f_3577_);
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 1, v_a_3566_);
lean_ctor_set(v___x_3572_, 0, v___x_3580_);
v___x_3582_ = v___x_3572_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3580_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v_a_3566_);
v___x_3582_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
v_a_3565_ = v_tail_3570_;
v_a_3566_ = v___x_3582_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3587_, lean_object* v_a_3588_, lean_object* v_ref_3589_, lean_object* v_applicationTime_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_){
_start:
{
uint8_t v_applicationTime_boxed_3593_; lean_object* v_res_3594_; 
v_applicationTime_boxed_3593_ = lean_unbox(v_applicationTime_3590_);
v_res_3594_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3587_, v_a_3588_, v_ref_3589_, v_applicationTime_boxed_3593_, v_a_3591_, v_a_3592_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3608_, lean_object* v_validate_3609_, uint8_t v_applicationTime_3610_, lean_object* v_ref_3611_){
_start:
{
lean_object* v___f_3613_; lean_object* v___f_3614_; lean_object* v___f_3615_; lean_object* v___f_3616_; lean_object* v___f_3617_; lean_object* v___f_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; uint8_t v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v___f_3613_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3614_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3615_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3616_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3617_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3618_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3619_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3620_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
v___x_3621_ = 0;
lean_inc(v_ref_3611_);
v___x_3622_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_3622_, 0, v_ref_3611_);
lean_ctor_set(v___x_3622_, 1, v___f_3617_);
lean_ctor_set(v___x_3622_, 2, v___f_3618_);
lean_ctor_set(v___x_3622_, 3, v___f_3616_);
lean_ctor_set(v___x_3622_, 4, v___f_3615_);
lean_ctor_set(v___x_3622_, 5, v___f_3614_);
lean_ctor_set(v___x_3622_, 6, v___x_3619_);
lean_ctor_set(v___x_3622_, 7, v___x_3620_);
lean_ctor_set_uint8(v___x_3622_, sizeof(void*)*8, v___x_3621_);
lean_ctor_set_uint8(v___x_3622_, sizeof(void*)*8 + 1, v___x_3621_);
v___x_3623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3622_);
lean_ctor_set(v___x_3623_, 1, v___f_3613_);
v___x_3624_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3623_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc_n(v_a_3625_, 2);
lean_dec_ref_known(v___x_3624_, 1);
v___x_3626_ = lean_box(0);
v___x_3627_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3609_, v_a_3625_, v_ref_3611_, v_applicationTime_3610_, v_attrDescrs_3608_, v___x_3626_);
lean_inc(v___x_3627_);
v___x_3628_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3627_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3636_; 
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3636_ == 0)
{
lean_object* v_unused_3637_; 
v_unused_3637_ = lean_ctor_get(v___x_3628_, 0);
lean_dec(v_unused_3637_);
v___x_3630_ = v___x_3628_;
v_isShared_3631_ = v_isSharedCheck_3636_;
goto v_resetjp_3629_;
}
else
{
lean_dec(v___x_3628_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3636_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3632_; lean_object* v___x_3634_; 
v___x_3632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3627_);
lean_ctor_set(v___x_3632_, 1, v_a_3625_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 0, v___x_3632_);
v___x_3634_ = v___x_3630_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3632_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
else
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
lean_dec(v___x_3627_);
lean_dec(v_a_3625_);
v_a_3638_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v___x_3628_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3628_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3638_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
else
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
lean_dec(v_ref_3611_);
lean_dec_ref(v_validate_3609_);
lean_dec(v_attrDescrs_3608_);
v_a_3646_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3624_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3624_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3646_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3654_, lean_object* v_validate_3655_, lean_object* v_applicationTime_3656_, lean_object* v_ref_3657_, lean_object* v_a_3658_){
_start:
{
uint8_t v_applicationTime_boxed_3659_; lean_object* v_res_3660_; 
v_applicationTime_boxed_3659_ = lean_unbox(v_applicationTime_3656_);
v_res_3660_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3654_, v_validate_3655_, v_applicationTime_boxed_3659_, v_ref_3657_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3661_, lean_object* v_attrDescrs_3662_, lean_object* v_validate_3663_, uint8_t v_applicationTime_3664_, lean_object* v_ref_3665_){
_start:
{
lean_object* v___x_3667_; 
v___x_3667_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3662_, v_validate_3663_, v_applicationTime_3664_, v_ref_3665_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3668_, lean_object* v_attrDescrs_3669_, lean_object* v_validate_3670_, lean_object* v_applicationTime_3671_, lean_object* v_ref_3672_, lean_object* v_a_3673_){
_start:
{
uint8_t v_applicationTime_boxed_3674_; lean_object* v_res_3675_; 
v_applicationTime_boxed_3674_ = lean_unbox(v_applicationTime_3671_);
v_res_3675_ = l_Lean_registerEnumAttributes(v_00_u03b1_3668_, v_attrDescrs_3669_, v_validate_3670_, v_applicationTime_boxed_3674_, v_ref_3672_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3676_, lean_object* v_env_3677_, lean_object* v_as_3678_, size_t v_i_3679_, size_t v_stop_3680_, lean_object* v_b_3681_){
_start:
{
lean_object* v___x_3682_; 
v___x_3682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3677_, v_as_3678_, v_i_3679_, v_stop_3680_, v_b_3681_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3683_, lean_object* v_env_3684_, lean_object* v_as_3685_, lean_object* v_i_3686_, lean_object* v_stop_3687_, lean_object* v_b_3688_){
_start:
{
size_t v_i_boxed_3689_; size_t v_stop_boxed_3690_; lean_object* v_res_3691_; 
v_i_boxed_3689_ = lean_unbox_usize(v_i_3686_);
lean_dec(v_i_3686_);
v_stop_boxed_3690_ = lean_unbox_usize(v_stop_3687_);
lean_dec(v_stop_3687_);
v_res_3691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3683_, v_env_3684_, v_as_3685_, v_i_boxed_3689_, v_stop_boxed_3690_, v_b_3688_);
lean_dec_ref(v_as_3685_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3692_, lean_object* v_newState_3693_, lean_object* v_x_3694_, lean_object* v_x_3695_){
_start:
{
lean_object* v___x_3696_; 
v___x_3696_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3693_, v_x_3694_, v_x_3695_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3697_, lean_object* v_newState_3698_, lean_object* v_x_3699_, lean_object* v_x_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3697_, v_newState_3698_, v_x_3699_, v_x_3700_);
lean_dec(v_newState_3698_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3702_, lean_object* v_validate_3703_, lean_object* v_a_3704_, lean_object* v_ref_3705_, uint8_t v_applicationTime_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_){
_start:
{
lean_object* v___x_3709_; 
v___x_3709_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3703_, v_a_3704_, v_ref_3705_, v_applicationTime_3706_, v_a_3707_, v_a_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3710_, lean_object* v_validate_3711_, lean_object* v_a_3712_, lean_object* v_ref_3713_, lean_object* v_applicationTime_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_){
_start:
{
uint8_t v_applicationTime_boxed_3717_; lean_object* v_res_3718_; 
v_applicationTime_boxed_3717_ = lean_unbox(v_applicationTime_3714_);
v_res_3718_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3710_, v_validate_3711_, v_a_3712_, v_ref_3713_, v_applicationTime_boxed_3717_, v_a_3715_, v_a_3716_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3719_, lean_object* v_attr_3720_, lean_object* v_env_3721_, lean_object* v_decl_3722_){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3723_ = lean_box(1);
v___x_3724_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3721_, v_decl_3722_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_ext_3725_; lean_object* v_toEnvExtension_3726_; lean_object* v_asyncMode_3727_; uint8_t v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
lean_dec(v_inst_3719_);
v_ext_3725_ = lean_ctor_get(v_attr_3720_, 1);
lean_inc_ref(v_ext_3725_);
lean_dec_ref(v_attr_3720_);
v_toEnvExtension_3726_ = lean_ctor_get(v_ext_3725_, 0);
v_asyncMode_3727_ = lean_ctor_get(v_toEnvExtension_3726_, 2);
lean_inc(v_asyncMode_3727_);
v___x_3728_ = 0;
lean_inc(v_decl_3722_);
v___x_3729_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3723_, v_ext_3725_, v_env_3721_, v_asyncMode_3727_, v_decl_3722_, v___x_3728_);
lean_dec(v_asyncMode_3727_);
lean_dec_ref(v_ext_3725_);
v___x_3730_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3729_, v_decl_3722_);
lean_dec(v_decl_3722_);
lean_dec(v___x_3729_);
return v___x_3730_;
}
else
{
lean_object* v_val_3731_; lean_object* v_ext_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3762_; 
v_val_3731_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_val_3731_);
lean_dec_ref_known(v___x_3724_, 1);
v_ext_3732_ = lean_ctor_get(v_attr_3720_, 1);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_attr_3720_);
if (v_isSharedCheck_3762_ == 0)
{
lean_object* v_unused_3763_; 
v_unused_3763_ = lean_ctor_get(v_attr_3720_, 0);
lean_dec(v_unused_3763_);
v___x_3734_ = v_attr_3720_;
v_isShared_3735_ = v_isSharedCheck_3762_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_ext_3732_);
lean_dec(v_attr_3720_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3762_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
uint8_t v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; uint8_t v___x_3740_; 
v___x_3736_ = 0;
v___x_3737_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3723_, v_ext_3732_, v_env_3721_, v_val_3731_, v___x_3736_);
lean_dec(v_val_3731_);
lean_dec_ref(v_env_3721_);
lean_dec_ref(v_ext_3732_);
v___x_3738_ = lean_unsigned_to_nat(0u);
v___x_3739_ = lean_array_get_size(v___x_3737_);
v___x_3740_ = lean_nat_dec_lt(v___x_3738_, v___x_3739_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3741_; 
lean_dec_ref(v___x_3737_);
lean_del_object(v___x_3734_);
lean_dec(v_decl_3722_);
lean_dec(v_inst_3719_);
v___x_3741_ = lean_box(0);
return v___x_3741_;
}
else
{
lean_object* v___x_3742_; lean_object* v___x_3743_; uint8_t v___x_3744_; 
v___x_3742_ = lean_unsigned_to_nat(1u);
v___x_3743_ = lean_nat_sub(v___x_3739_, v___x_3742_);
v___x_3744_ = lean_nat_dec_le(v___x_3738_, v___x_3743_);
if (v___x_3744_ == 0)
{
lean_object* v___x_3745_; 
lean_dec(v___x_3743_);
lean_dec_ref(v___x_3737_);
lean_del_object(v___x_3734_);
lean_dec(v_decl_3722_);
lean_dec(v_inst_3719_);
v___x_3745_ = lean_box(0);
return v___x_3745_;
}
else
{
lean_object* v___f_3746_; lean_object* v___x_3748_; 
v___f_3746_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 1, v_inst_3719_);
lean_ctor_set(v___x_3734_, 0, v_decl_3722_);
v___x_3748_ = v___x_3734_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_decl_3722_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_inst_3719_);
v___x_3748_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3749_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3750_ = l_Array_binSearchAux___redArg(v___f_3746_, v___x_3749_, v___x_3737_, v___x_3748_, v___x_3738_, v___x_3743_);
lean_dec_ref(v___x_3737_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v___x_3751_; 
v___x_3751_ = lean_box(0);
return v___x_3751_;
}
else
{
lean_object* v_val_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3760_; 
v_val_3752_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3754_ = v___x_3750_;
v_isShared_3755_ = v_isSharedCheck_3760_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_val_3752_);
lean_dec(v___x_3750_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3760_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v_snd_3756_; lean_object* v___x_3758_; 
v_snd_3756_ = lean_ctor_get(v_val_3752_, 1);
lean_inc(v_snd_3756_);
lean_dec(v_val_3752_);
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 0, v_snd_3756_);
v___x_3758_ = v___x_3754_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_snd_3756_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3764_, lean_object* v_inst_3765_, lean_object* v_attr_3766_, lean_object* v_env_3767_, lean_object* v_decl_3768_){
_start:
{
lean_object* v___x_3769_; 
v___x_3769_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3765_, v_attr_3766_, v_env_3767_, v_decl_3768_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3778_, lean_object* v_env_3779_, lean_object* v_decl_3780_, lean_object* v_val_3781_){
_start:
{
lean_object* v_ext_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3852_; 
v_ext_3782_ = lean_ctor_get(v_attrs_3778_, 1);
v_isSharedCheck_3852_ = !lean_is_exclusive(v_attrs_3778_);
if (v_isSharedCheck_3852_ == 0)
{
lean_object* v_unused_3853_; 
v_unused_3853_ = lean_ctor_get(v_attrs_3778_, 0);
lean_dec(v_unused_3853_);
v___x_3784_ = v_attrs_3778_;
v_isShared_3785_ = v_isSharedCheck_3852_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_ext_3782_);
lean_dec(v_attrs_3778_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3852_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v_toEnvExtension_3786_; lean_object* v_name_3787_; lean_object* v_addEntryFn_3788_; lean_object* v___x_3789_; uint8_t v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v_pfx_3798_; lean_object* v___x_3799_; 
v_toEnvExtension_3786_ = lean_ctor_get(v_ext_3782_, 0);
lean_inc_ref(v_toEnvExtension_3786_);
v_name_3787_ = lean_ctor_get(v_ext_3782_, 1);
v_addEntryFn_3788_ = lean_ctor_get(v_ext_3782_, 3);
lean_inc(v_addEntryFn_3788_);
v___x_3789_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3790_ = 1;
lean_inc(v_name_3787_);
v___x_3791_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3787_, v___x_3790_);
v___x_3792_ = lean_string_append(v___x_3789_, v___x_3791_);
lean_dec_ref(v___x_3791_);
v___x_3793_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3794_ = lean_string_append(v___x_3792_, v___x_3793_);
lean_inc(v_decl_3780_);
v___x_3795_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3780_, v___x_3790_);
v___x_3796_ = lean_string_append(v___x_3794_, v___x_3795_);
lean_dec_ref(v___x_3795_);
v___x_3797_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3798_ = lean_string_append(v___x_3796_, v___x_3797_);
v___x_3799_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3779_, v_decl_3780_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v_asyncMode_3800_; uint8_t v_logWrites_3801_; uint8_t v___x_3802_; 
v_asyncMode_3800_ = lean_ctor_get(v_toEnvExtension_3786_, 2);
lean_inc(v_asyncMode_3800_);
v_logWrites_3801_ = lean_ctor_get_uint8(v_toEnvExtension_3786_, sizeof(void*)*6);
lean_inc(v_decl_3780_);
lean_inc_ref(v_env_3779_);
v___x_3802_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3779_, v_decl_3780_, v_asyncMode_3800_);
if (v___x_3802_ == 0)
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___y_3806_; lean_object* v___x_3810_; 
lean_dec(v_asyncMode_3800_);
lean_dec(v_addEntryFn_3788_);
lean_dec_ref(v_toEnvExtension_3786_);
lean_del_object(v___x_3784_);
lean_dec_ref(v_ext_3782_);
lean_dec(v_val_3781_);
lean_dec(v_decl_3780_);
v___x_3803_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3804_ = lean_string_append(v_pfx_3798_, v___x_3803_);
v___x_3810_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3779_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_object* v___x_3811_; 
v___x_3811_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3806_ = v___x_3811_;
goto v___jp_3805_;
}
else
{
lean_object* v_val_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
v_val_3812_ = lean_ctor_get(v___x_3810_, 0);
lean_inc(v_val_3812_);
lean_dec_ref_known(v___x_3810_, 1);
v___x_3813_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3814_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3812_, v___x_3790_);
v___x_3815_ = l_addParenHeuristic(v___x_3814_);
v___x_3816_ = lean_string_append(v___x_3813_, v___x_3815_);
lean_dec_ref(v___x_3815_);
v___x_3817_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3818_ = lean_string_append(v___x_3816_, v___x_3817_);
v___y_3806_ = v___x_3818_;
goto v___jp_3805_;
}
v___jp_3805_:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3807_ = lean_string_append(v___x_3804_, v___y_3806_);
lean_dec_ref(v___y_3806_);
v___x_3808_ = lean_string_append(v___x_3807_, v___x_3797_);
v___x_3809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3808_);
return v___x_3809_;
}
}
else
{
lean_object* v___x_3819_; uint8_t v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3819_ = lean_box(1);
v___x_3820_ = 0;
lean_inc(v_decl_3780_);
lean_inc_ref(v_env_3779_);
v___x_3821_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3819_, v_ext_3782_, v_env_3779_, v_asyncMode_3800_, v_decl_3780_, v___x_3820_);
lean_dec_ref(v_ext_3782_);
v___x_3822_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3821_, v_decl_3780_);
lean_dec(v___x_3821_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v___x_3824_; 
lean_dec_ref(v_pfx_3798_);
lean_inc(v_decl_3780_);
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 1, v_val_3781_);
lean_ctor_set(v___x_3784_, 0, v_decl_3780_);
v___x_3824_ = v___x_3784_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_decl_3780_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v_val_3781_);
v___x_3824_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
lean_object* v___f_3825_; 
v___f_3825_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3825_, 0, v_addEntryFn_3788_);
lean_closure_set(v___f_3825_, 1, v___x_3824_);
if (v_logWrites_3801_ == 0)
{
lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3826_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3786_, v_env_3779_, v___f_3825_, v_asyncMode_3800_, v_decl_3780_, v___x_3802_);
lean_dec(v_asyncMode_3800_);
v___x_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3826_);
return v___x_3827_;
}
else
{
lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
lean_inc_ref(v_toEnvExtension_3786_);
v___x_3828_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3786_, v_env_3779_);
lean_dec_ref(v_env_3779_);
v___x_3829_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3786_, v___x_3828_, v___f_3825_, v_asyncMode_3800_, v_decl_3780_, v___x_3802_);
lean_dec(v_asyncMode_3800_);
v___x_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3829_);
return v___x_3830_;
}
}
}
else
{
lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3840_; 
lean_dec(v_asyncMode_3800_);
lean_dec(v_addEntryFn_3788_);
lean_dec_ref(v_toEnvExtension_3786_);
lean_del_object(v___x_3784_);
lean_dec(v_val_3781_);
lean_dec(v_decl_3780_);
lean_dec_ref(v_env_3779_);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3840_ == 0)
{
lean_object* v_unused_3841_; 
v_unused_3841_ = lean_ctor_get(v___x_3822_, 0);
lean_dec(v_unused_3841_);
v___x_3833_ = v___x_3822_;
v_isShared_3834_ = v_isSharedCheck_3840_;
goto v_resetjp_3832_;
}
else
{
lean_dec(v___x_3822_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3840_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3838_; 
v___x_3835_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3836_ = lean_string_append(v_pfx_3798_, v___x_3835_);
if (v_isShared_3834_ == 0)
{
lean_ctor_set_tag(v___x_3833_, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3836_);
v___x_3838_ = v___x_3833_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3836_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
}
else
{
lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3850_; 
lean_dec(v_addEntryFn_3788_);
lean_dec_ref(v_toEnvExtension_3786_);
lean_del_object(v___x_3784_);
lean_dec_ref(v_ext_3782_);
lean_dec(v_val_3781_);
lean_dec(v_decl_3780_);
lean_dec_ref(v_env_3779_);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3850_ == 0)
{
lean_object* v_unused_3851_; 
v_unused_3851_ = lean_ctor_get(v___x_3799_, 0);
lean_dec(v_unused_3851_);
v___x_3843_ = v___x_3799_;
v_isShared_3844_ = v_isSharedCheck_3850_;
goto v_resetjp_3842_;
}
else
{
lean_dec(v___x_3799_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3850_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3848_; 
v___x_3845_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3846_ = lean_string_append(v_pfx_3798_, v___x_3845_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set_tag(v___x_3843_, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3846_);
v___x_3848_ = v___x_3843_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3846_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3854_, lean_object* v_attrs_3855_, lean_object* v_env_3856_, lean_object* v_decl_3857_, lean_object* v_val_3858_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3855_, v_env_3856_, v_decl_3857_, v_val_3858_);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3861_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3862_ = lean_st_mk_ref(v___x_3861_);
v___x_3863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3862_);
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3868_, lean_object* v_builder_3869_){
_start:
{
lean_object* v___x_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; 
v___x_3871_ = l_Lean_attributeImplBuilderTableRef;
v___x_3872_ = lean_st_ref_get(v___x_3871_);
v___x_3873_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3872_, v_builderId_3868_);
lean_dec(v___x_3872_);
if (v___x_3873_ == 0)
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3874_ = lean_st_ref_take(v___x_3871_);
v___x_3875_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3874_, v_builderId_3868_, v_builder_3869_);
v___x_3876_ = lean_st_ref_put(v___x_3871_, v___x_3875_);
v___x_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3877_, 0, v___x_3876_);
return v___x_3877_;
}
else
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
lean_dec_ref(v_builder_3869_);
v___x_3878_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3879_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3868_, v___x_3873_);
v___x_3880_ = lean_string_append(v___x_3878_, v___x_3879_);
lean_dec_ref(v___x_3879_);
v___x_3881_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3882_ = lean_string_append(v___x_3880_, v___x_3881_);
v___x_3883_ = lean_mk_io_user_error(v___x_3882_);
v___x_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3883_);
return v___x_3884_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3885_, lean_object* v_builder_3886_, lean_object* v_a_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_Lean_registerAttributeImplBuilder(v_builderId_3885_, v_builder_3886_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3889_){
_start:
{
if (lean_obj_tag(v_e_3889_) == 0)
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3899_; 
v_a_3891_ = lean_ctor_get(v_e_3889_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v_e_3889_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3893_ = v_e_3889_;
v_isShared_3894_ = v_isSharedCheck_3899_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v_e_3889_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3899_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3895_; lean_object* v___x_3897_; 
v___x_3895_ = lean_mk_io_user_error(v_a_3891_);
if (v_isShared_3894_ == 0)
{
lean_ctor_set_tag(v___x_3893_, 1);
lean_ctor_set(v___x_3893_, 0, v___x_3895_);
v___x_3897_ = v___x_3893_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3895_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
else
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3907_; 
v_a_3900_ = lean_ctor_get(v_e_3889_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v_e_3889_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v_e_3889_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v_e_3889_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
if (v_isShared_3903_ == 0)
{
lean_ctor_set_tag(v___x_3902_, 0);
v___x_3905_ = v___x_3902_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3900_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3908_, lean_object* v_a_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3908_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3911_, lean_object* v_e_3912_){
_start:
{
lean_object* v___x_3914_; 
v___x_3914_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3912_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3915_, lean_object* v_e_3916_, lean_object* v_a_3917_){
_start:
{
lean_object* v_res_3918_; 
v_res_3918_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3915_, v_e_3916_);
return v_res_3918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3919_, lean_object* v_x_3920_){
_start:
{
if (lean_obj_tag(v_x_3920_) == 0)
{
lean_object* v___x_3921_; 
v___x_3921_ = lean_box(0);
return v___x_3921_;
}
else
{
lean_object* v_key_3922_; lean_object* v_value_3923_; lean_object* v_tail_3924_; uint8_t v___x_3925_; 
v_key_3922_ = lean_ctor_get(v_x_3920_, 0);
v_value_3923_ = lean_ctor_get(v_x_3920_, 1);
v_tail_3924_ = lean_ctor_get(v_x_3920_, 2);
v___x_3925_ = lean_name_eq(v_key_3922_, v_a_3919_);
if (v___x_3925_ == 0)
{
v_x_3920_ = v_tail_3924_;
goto _start;
}
else
{
lean_object* v___x_3927_; 
lean_inc(v_value_3923_);
v___x_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3927_, 0, v_value_3923_);
return v___x_3927_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3928_, lean_object* v_x_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3928_, v_x_3929_);
lean_dec(v_x_3929_);
lean_dec(v_a_3928_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3931_, lean_object* v_a_3932_){
_start:
{
lean_object* v_buckets_3933_; lean_object* v___x_3934_; uint64_t v___y_3936_; 
v_buckets_3933_ = lean_ctor_get(v_m_3931_, 1);
v___x_3934_ = lean_array_get_size(v_buckets_3933_);
if (lean_obj_tag(v_a_3932_) == 0)
{
uint64_t v___x_3950_; 
v___x_3950_ = 1723ULL;
v___y_3936_ = v___x_3950_;
goto v___jp_3935_;
}
else
{
uint64_t v_hash_3951_; 
v_hash_3951_ = lean_ctor_get_uint64(v_a_3932_, sizeof(void*)*2);
v___y_3936_ = v_hash_3951_;
goto v___jp_3935_;
}
v___jp_3935_:
{
uint64_t v___x_3937_; uint64_t v___x_3938_; uint64_t v_fold_3939_; uint64_t v___x_3940_; uint64_t v___x_3941_; uint64_t v___x_3942_; size_t v___x_3943_; size_t v___x_3944_; size_t v___x_3945_; size_t v___x_3946_; size_t v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
v___x_3937_ = 32ULL;
v___x_3938_ = lean_uint64_shift_right(v___y_3936_, v___x_3937_);
v_fold_3939_ = lean_uint64_xor(v___y_3936_, v___x_3938_);
v___x_3940_ = 16ULL;
v___x_3941_ = lean_uint64_shift_right(v_fold_3939_, v___x_3940_);
v___x_3942_ = lean_uint64_xor(v_fold_3939_, v___x_3941_);
v___x_3943_ = lean_uint64_to_usize(v___x_3942_);
v___x_3944_ = lean_usize_of_nat(v___x_3934_);
v___x_3945_ = ((size_t)1ULL);
v___x_3946_ = lean_usize_sub(v___x_3944_, v___x_3945_);
v___x_3947_ = lean_usize_land(v___x_3943_, v___x_3946_);
v___x_3948_ = lean_array_uget_borrowed(v_buckets_3933_, v___x_3947_);
v___x_3949_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3932_, v___x_3948_);
return v___x_3949_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3952_, lean_object* v_a_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3952_, v_a_3953_);
lean_dec(v_a_3953_);
lean_dec_ref(v_m_3952_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3956_){
_start:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v_builderId_3960_; lean_object* v_ref_3961_; lean_object* v_args_3962_; lean_object* v___x_3963_; 
v___x_3958_ = l_Lean_attributeImplBuilderTableRef;
v___x_3959_ = lean_st_ref_get(v___x_3958_);
v_builderId_3960_ = lean_ctor_get(v_e_3956_, 0);
lean_inc(v_builderId_3960_);
v_ref_3961_ = lean_ctor_get(v_e_3956_, 1);
lean_inc(v_ref_3961_);
v_args_3962_ = lean_ctor_get(v_e_3956_, 2);
lean_inc(v_args_3962_);
lean_dec_ref(v_e_3956_);
v___x_3963_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3959_, v_builderId_3960_);
lean_dec(v___x_3959_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v___x_3964_; uint8_t v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
lean_dec(v_args_3962_);
lean_dec(v_ref_3961_);
v___x_3964_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3965_ = 1;
v___x_3966_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3960_, v___x_3965_);
v___x_3967_ = lean_string_append(v___x_3964_, v___x_3966_);
lean_dec_ref(v___x_3966_);
v___x_3968_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3969_ = lean_string_append(v___x_3967_, v___x_3968_);
v___x_3970_ = lean_mk_io_user_error(v___x_3969_);
v___x_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
return v___x_3971_;
}
else
{
lean_object* v_val_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
lean_dec(v_builderId_3960_);
v_val_3972_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_val_3972_);
lean_dec_ref_known(v___x_3963_, 1);
v___x_3973_ = lean_apply_2(v_val_3972_, v_ref_3961_, v_args_3962_);
v___x_3974_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3973_);
return v___x_3974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3975_, lean_object* v_a_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l_Lean_mkAttributeImplOfEntry(v_e_3975_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3978_, lean_object* v_m_3979_, lean_object* v_a_3980_){
_start:
{
lean_object* v___x_3981_; 
v___x_3981_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3979_, v_a_3980_);
return v___x_3981_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3982_, lean_object* v_m_3983_, lean_object* v_a_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3982_, v_m_3983_, v_a_3984_);
lean_dec(v_a_3984_);
lean_dec_ref(v_m_3983_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3986_, lean_object* v_a_3987_, lean_object* v_x_3988_){
_start:
{
lean_object* v___x_3989_; 
v___x_3989_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3987_, v_x_3988_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3990_, lean_object* v_a_3991_, lean_object* v_x_3992_){
_start:
{
lean_object* v_res_3993_; 
v_res_3993_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3990_, v_a_3991_, v_x_3992_);
lean_dec(v_x_3992_);
lean_dec(v_a_3991_);
return v_res_3993_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3994_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3995_ = lean_box(0);
v___x_3996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3995_);
lean_ctor_set(v___x_3996_, 1, v___x_3994_);
return v___x_3996_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3997_; 
v___x_3997_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3997_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3998_; 
v___x_3998_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4000_ = l_Lean_attributeMapRef;
v___x_4001_ = lean_st_ref_get(v___x_4000_);
v___x_4002_ = lean_box(0);
v___x_4003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4002_);
lean_ctor_set(v___x_4003_, 1, v___x_4001_);
v___x_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4003_);
return v___x_4004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_4012_, lean_object* v_opts_4013_, lean_object* v_declName_4014_){
_start:
{
uint8_t v___x_4017_; lean_object* v___x_4018_; 
v___x_4017_ = 0;
lean_inc(v_declName_4014_);
lean_inc_ref(v_env_4012_);
v___x_4018_ = l_Lean_Environment_find_x3f(v_env_4012_, v_declName_4014_, v___x_4017_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v___x_4019_; uint8_t v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
lean_dec_ref(v_env_4012_);
v___x_4019_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_4020_ = 1;
v___x_4021_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_4014_, v___x_4020_);
v___x_4022_ = lean_string_append(v___x_4019_, v___x_4021_);
lean_dec_ref(v___x_4021_);
v___x_4023_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4024_ = lean_string_append(v___x_4022_, v___x_4023_);
v___x_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4024_);
return v___x_4025_;
}
else
{
lean_object* v_val_4026_; lean_object* v___x_4027_; 
v_val_4026_ = lean_ctor_get(v___x_4018_, 0);
lean_inc(v_val_4026_);
lean_dec_ref_known(v___x_4018_, 1);
v___x_4027_ = l_Lean_ConstantInfo_type(v_val_4026_);
lean_dec(v_val_4026_);
if (lean_obj_tag(v___x_4027_) == 4)
{
lean_object* v_declName_4028_; 
v_declName_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_declName_4028_);
lean_dec_ref_known(v___x_4027_, 2);
if (lean_obj_tag(v_declName_4028_) == 1)
{
lean_object* v_pre_4029_; 
v_pre_4029_ = lean_ctor_get(v_declName_4028_, 0);
lean_inc(v_pre_4029_);
if (lean_obj_tag(v_pre_4029_) == 1)
{
lean_object* v_pre_4030_; 
v_pre_4030_ = lean_ctor_get(v_pre_4029_, 0);
if (lean_obj_tag(v_pre_4030_) == 0)
{
lean_object* v_str_4031_; lean_object* v_str_4032_; lean_object* v___x_4033_; uint8_t v___x_4034_; 
v_str_4031_ = lean_ctor_get(v_declName_4028_, 1);
lean_inc_ref(v_str_4031_);
lean_dec_ref_known(v_declName_4028_, 2);
v_str_4032_ = lean_ctor_get(v_pre_4029_, 1);
lean_inc_ref(v_str_4032_);
lean_dec_ref_known(v_pre_4029_, 2);
v___x_4033_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_4034_ = lean_string_dec_eq(v_str_4032_, v___x_4033_);
lean_dec_ref(v_str_4032_);
if (v___x_4034_ == 0)
{
lean_dec_ref(v_str_4031_);
lean_dec(v_declName_4014_);
lean_dec_ref(v_env_4012_);
goto v___jp_4015_;
}
else
{
lean_object* v___x_4035_; uint8_t v___x_4036_; 
v___x_4035_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_4036_ = lean_string_dec_eq(v_str_4031_, v___x_4035_);
lean_dec_ref(v_str_4031_);
if (v___x_4036_ == 0)
{
lean_dec(v_declName_4014_);
lean_dec_ref(v_env_4012_);
goto v___jp_4015_;
}
else
{
lean_object* v___x_4037_; 
v___x_4037_ = l_Lean_Environment_evalConst___redArg(v_env_4012_, v_opts_4013_, v_declName_4014_, v___x_4036_);
lean_dec(v_declName_4014_);
lean_dec_ref(v_env_4012_);
return v___x_4037_;
}
}
}
else
{
lean_dec_ref_known(v_pre_4029_, 2);
lean_dec_ref_known(v_declName_4028_, 2);
lean_dec(v_declName_4014_);
lean_dec_ref(v_env_4012_);
goto v___jp_4015_;
}
}
else
{
lean_dec_ref_known(v_declName_4028_, 2);
lean_dec(v_pre_4029_);
lean_dec(v_declName_4014_);
lean_dec_ref(v_env_4012_);
goto v___jp_4015_;
}
}
else
{
lean_dec(v_declName_4028_);
lean_dec(v_declName_4014_);
lean_dec_ref(v_env_4012_);
goto v___jp_4015_;
}
}
else
{
lean_dec_ref(v___x_4027_);
lean_dec(v_declName_4014_);
lean_dec_ref(v_env_4012_);
goto v___jp_4015_;
}
}
v___jp_4015_:
{
lean_object* v___x_4016_; 
v___x_4016_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_4016_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_4038_, lean_object* v_opts_4039_, lean_object* v_declName_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_4038_, v_opts_4039_, v_declName_4040_);
lean_dec_ref(v_opts_4039_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_4042_, size_t v_i_4043_, size_t v_stop_4044_, lean_object* v_b_4045_){
_start:
{
uint8_t v___x_4047_; 
v___x_4047_ = lean_usize_dec_eq(v_i_4043_, v_stop_4044_);
if (v___x_4047_ == 0)
{
lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4048_ = lean_array_uget_borrowed(v_as_4042_, v_i_4043_);
lean_inc(v___x_4048_);
v___x_4049_ = l_Lean_mkAttributeImplOfEntry(v___x_4048_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v_toAttributeImplCore_4051_; lean_object* v_name_4052_; lean_object* v___x_4053_; size_t v___x_4054_; size_t v___x_4055_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_a_4050_);
lean_dec_ref_known(v___x_4049_, 1);
v_toAttributeImplCore_4051_ = lean_ctor_get(v_a_4050_, 0);
v_name_4052_ = lean_ctor_get(v_toAttributeImplCore_4051_, 1);
lean_inc(v_name_4052_);
v___x_4053_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_4045_, v_name_4052_, v_a_4050_);
v___x_4054_ = ((size_t)1ULL);
v___x_4055_ = lean_usize_add(v_i_4043_, v___x_4054_);
v_i_4043_ = v___x_4055_;
v_b_4045_ = v___x_4053_;
goto _start;
}
else
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4064_; 
lean_dec_ref(v_b_4045_);
v_a_4057_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4059_ = v___x_4049_;
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_4049_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
}
else
{
lean_object* v___x_4065_; 
v___x_4065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4065_, 0, v_b_4045_);
return v___x_4065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_4066_, lean_object* v_i_4067_, lean_object* v_stop_4068_, lean_object* v_b_4069_, lean_object* v___y_4070_){
_start:
{
size_t v_i_boxed_4071_; size_t v_stop_boxed_4072_; lean_object* v_res_4073_; 
v_i_boxed_4071_ = lean_unbox_usize(v_i_4067_);
lean_dec(v_i_4067_);
v_stop_boxed_4072_ = lean_unbox_usize(v_stop_4068_);
lean_dec(v_stop_4068_);
v_res_4073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4066_, v_i_boxed_4071_, v_stop_boxed_4072_, v_b_4069_);
lean_dec_ref(v_as_4066_);
return v_res_4073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_4074_, size_t v_i_4075_, size_t v_stop_4076_, lean_object* v_b_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v_a_4081_; uint8_t v___x_4085_; 
v___x_4085_ = lean_usize_dec_eq(v_i_4075_, v_stop_4076_);
if (v___x_4085_ == 0)
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; uint8_t v___x_4089_; 
v___x_4086_ = lean_array_uget_borrowed(v_as_4074_, v_i_4075_);
v___x_4087_ = lean_unsigned_to_nat(0u);
v___x_4088_ = lean_array_get_size(v___x_4086_);
v___x_4089_ = lean_nat_dec_lt(v___x_4087_, v___x_4088_);
if (v___x_4089_ == 0)
{
v_a_4081_ = v_b_4077_;
goto v___jp_4080_;
}
else
{
size_t v___x_4090_; size_t v___x_4091_; lean_object* v___x_4092_; 
v___x_4090_ = ((size_t)0ULL);
v___x_4091_ = lean_usize_of_nat(v___x_4088_);
v___x_4092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4086_, v___x_4090_, v___x_4091_, v_b_4077_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc(v_a_4093_);
lean_dec_ref_known(v___x_4092_, 1);
v_a_4081_ = v_a_4093_;
goto v___jp_4080_;
}
else
{
return v___x_4092_;
}
}
}
else
{
lean_object* v___x_4094_; 
v___x_4094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4094_, 0, v_b_4077_);
return v___x_4094_;
}
v___jp_4080_:
{
size_t v___x_4082_; size_t v___x_4083_; 
v___x_4082_ = ((size_t)1ULL);
v___x_4083_ = lean_usize_add(v_i_4075_, v___x_4082_);
v_i_4075_ = v___x_4083_;
v_b_4077_ = v_a_4081_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4095_, lean_object* v_i_4096_, lean_object* v_stop_4097_, lean_object* v_b_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
size_t v_i_boxed_4101_; size_t v_stop_boxed_4102_; lean_object* v_res_4103_; 
v_i_boxed_4101_ = lean_unbox_usize(v_i_4096_);
lean_dec(v_i_4096_);
v_stop_boxed_4102_ = lean_unbox_usize(v_stop_4097_);
lean_dec(v_stop_4097_);
v_res_4103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4095_, v_i_boxed_4101_, v_stop_boxed_4102_, v_b_4098_, v___y_4099_);
lean_dec_ref(v___y_4099_);
lean_dec_ref(v_as_4095_);
return v_res_4103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4104_, lean_object* v_a_4105_){
_start:
{
lean_object* v_a_4108_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; uint8_t v___x_4116_; 
v___x_4112_ = l_Lean_attributeMapRef;
v___x_4113_ = lean_st_ref_get(v___x_4112_);
v___x_4114_ = lean_unsigned_to_nat(0u);
v___x_4115_ = lean_array_get_size(v_es_4104_);
v___x_4116_ = lean_nat_dec_lt(v___x_4114_, v___x_4115_);
if (v___x_4116_ == 0)
{
v_a_4108_ = v___x_4113_;
goto v___jp_4107_;
}
else
{
size_t v___x_4117_; size_t v___x_4118_; lean_object* v___x_4119_; 
v___x_4117_ = ((size_t)0ULL);
v___x_4118_ = lean_usize_of_nat(v___x_4115_);
v___x_4119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4104_, v___x_4117_, v___x_4118_, v___x_4113_, v_a_4105_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref_known(v___x_4119_, 1);
v_a_4108_ = v_a_4120_;
goto v___jp_4107_;
}
else
{
lean_object* v_a_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4128_; 
v_a_4121_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4128_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4128_ == 0)
{
v___x_4123_ = v___x_4119_;
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_a_4121_);
lean_dec(v___x_4119_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4126_; 
if (v_isShared_4124_ == 0)
{
v___x_4126_ = v___x_4123_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_a_4121_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
return v___x_4126_;
}
}
}
}
v___jp_4107_:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4109_ = lean_box(0);
v___x_4110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4109_);
lean_ctor_set(v___x_4110_, 1, v_a_4108_);
v___x_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4111_, 0, v___x_4110_);
return v___x_4111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4129_, v_a_4130_);
lean_dec_ref(v_a_4130_);
lean_dec_ref(v_es_4129_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4133_, size_t v_i_4134_, size_t v_stop_4135_, lean_object* v_b_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v___x_4139_; 
v___x_4139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4133_, v_i_4134_, v_stop_4135_, v_b_4136_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4140_, lean_object* v_i_4141_, lean_object* v_stop_4142_, lean_object* v_b_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
size_t v_i_boxed_4146_; size_t v_stop_boxed_4147_; lean_object* v_res_4148_; 
v_i_boxed_4146_ = lean_unbox_usize(v_i_4141_);
lean_dec(v_i_4141_);
v_stop_boxed_4147_ = lean_unbox_usize(v_stop_4142_);
lean_dec(v_stop_4142_);
v_res_4148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4140_, v_i_boxed_4146_, v_stop_boxed_4147_, v_b_4143_, v___y_4144_);
lean_dec_ref(v___y_4144_);
lean_dec_ref(v_as_4140_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4149_, lean_object* v_e_4150_){
_start:
{
lean_object* v_snd_4151_; lean_object* v_toAttributeImplCore_4152_; lean_object* v_fst_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4171_; 
v_snd_4151_ = lean_ctor_get(v_e_4150_, 1);
lean_inc(v_snd_4151_);
v_toAttributeImplCore_4152_ = lean_ctor_get(v_snd_4151_, 0);
v_fst_4153_ = lean_ctor_get(v_e_4150_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v_e_4150_);
if (v_isSharedCheck_4171_ == 0)
{
lean_object* v_unused_4172_; 
v_unused_4172_ = lean_ctor_get(v_e_4150_, 1);
lean_dec(v_unused_4172_);
v___x_4155_ = v_e_4150_;
v_isShared_4156_ = v_isSharedCheck_4171_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_fst_4153_);
lean_dec(v_e_4150_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4171_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v_newEntries_4157_; lean_object* v_map_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4170_; 
v_newEntries_4157_ = lean_ctor_get(v_s_4149_, 0);
v_map_4158_ = lean_ctor_get(v_s_4149_, 1);
v_isSharedCheck_4170_ = !lean_is_exclusive(v_s_4149_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4160_ = v_s_4149_;
v_isShared_4161_ = v_isSharedCheck_4170_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_map_4158_);
lean_inc(v_newEntries_4157_);
lean_dec(v_s_4149_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4170_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v_name_4162_; lean_object* v___x_4164_; 
v_name_4162_ = lean_ctor_get(v_toAttributeImplCore_4152_, 1);
lean_inc(v_name_4162_);
if (v_isShared_4156_ == 0)
{
lean_ctor_set_tag(v___x_4155_, 1);
lean_ctor_set(v___x_4155_, 1, v_newEntries_4157_);
v___x_4164_ = v___x_4155_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v_fst_4153_);
lean_ctor_set(v_reuseFailAlloc_4169_, 1, v_newEntries_4157_);
v___x_4164_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
lean_object* v___x_4165_; lean_object* v___x_4167_; 
v___x_4165_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4158_, v_name_4162_, v_snd_4151_);
if (v_isShared_4161_ == 0)
{
lean_ctor_set(v___x_4160_, 1, v___x_4165_);
lean_ctor_set(v___x_4160_, 0, v___x_4164_);
v___x_4167_ = v___x_4160_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4164_);
lean_ctor_set(v_reuseFailAlloc_4168_, 1, v___x_4165_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4173_, lean_object* v_s_4174_){
_start:
{
lean_object* v_newEntries_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
v_newEntries_4175_ = lean_ctor_get(v_s_4174_, 0);
lean_inc(v_newEntries_4175_);
lean_dec_ref(v_s_4174_);
v___x_4176_ = l_List_reverse___redArg(v_newEntries_4175_);
v___x_4177_ = lean_array_mk(v___x_4176_);
lean_inc_ref_n(v___x_4177_, 2);
v___x_4178_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4178_, 0, v___x_4177_);
lean_ctor_set(v___x_4178_, 1, v___x_4177_);
lean_ctor_set(v___x_4178_, 2, v___x_4177_);
return v___x_4178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4179_, lean_object* v_s_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4179_, v_s_4180_);
lean_dec_ref(v_x_4179_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4182_){
_start:
{
lean_object* v_newEntries_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4194_; 
v_newEntries_4183_ = lean_ctor_get(v_s_4182_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v_s_4182_);
if (v_isSharedCheck_4194_ == 0)
{
lean_object* v_unused_4195_; 
v_unused_4195_ = lean_ctor_get(v_s_4182_, 1);
lean_dec(v_unused_4195_);
v___x_4185_ = v_s_4182_;
v_isShared_4186_ = v_isSharedCheck_4194_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_newEntries_4183_);
lean_dec(v_s_4182_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4194_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4192_; 
v___x_4187_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4188_ = l_List_lengthTR___redArg(v_newEntries_4183_);
lean_dec(v_newEntries_4183_);
v___x_4189_ = l_Nat_reprFast(v___x_4188_);
v___x_4190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
if (v_isShared_4186_ == 0)
{
lean_ctor_set_tag(v___x_4185_, 5);
lean_ctor_set(v___x_4185_, 1, v___x_4190_);
lean_ctor_set(v___x_4185_, 0, v___x_4187_);
v___x_4192_ = v___x_4185_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v___x_4187_);
lean_ctor_set(v_reuseFailAlloc_4193_, 1, v___x_4190_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4196_){
_start:
{
lean_object* v_newEntries_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v_newEntries_4197_ = lean_ctor_get(v_s_4196_, 0);
lean_inc(v_newEntries_4197_);
lean_dec_ref(v_s_4196_);
v___x_4198_ = l_List_reverse___redArg(v_newEntries_4197_);
v___x_4199_ = lean_array_mk(v___x_4198_);
return v___x_4199_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___f_4212_; lean_object* v___f_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4209_ = 0;
v___x_4210_ = lean_box(0);
v___x_4211_ = lean_box(2);
v___f_4212_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4213_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4214_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4215_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4216_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4217_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4218_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_4218_, 0, v___x_4217_);
lean_ctor_set(v___x_4218_, 1, v___x_4216_);
lean_ctor_set(v___x_4218_, 2, v___x_4215_);
lean_ctor_set(v___x_4218_, 3, v___x_4214_);
lean_ctor_set(v___x_4218_, 4, v___f_4213_);
lean_ctor_set(v___x_4218_, 5, v___f_4212_);
lean_ctor_set(v___x_4218_, 6, v___x_4211_);
lean_ctor_set(v___x_4218_, 7, v___x_4210_);
lean_ctor_set_uint8(v___x_4218_, sizeof(void*)*8, v___x_4209_);
lean_ctor_set_uint8(v___x_4218_, sizeof(void*)*8 + 1, v___x_4209_);
return v___x_4218_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___f_4219_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4220_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4220_);
lean_ctor_set(v___x_4221_, 1, v___f_4219_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4223_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4224_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4223_);
return v___x_4224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4225_){
_start:
{
lean_object* v_res_4226_; 
v_res_4226_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4227_){
_start:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; uint8_t v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
v___x_4229_ = l_Lean_attributeMapRef;
v___x_4230_ = lean_st_ref_get(v___x_4229_);
v___x_4231_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4230_, v_n_4227_);
lean_dec(v___x_4230_);
v___x_4232_ = lean_box(v___x_4231_);
v___x_4233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4233_, 0, v___x_4232_);
return v___x_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4234_, lean_object* v_a_4235_){
_start:
{
lean_object* v_res_4236_; 
v_res_4236_ = l_Lean_isBuiltinAttribute(v_n_4234_);
lean_dec(v_n_4234_);
return v_res_4236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4237_, lean_object* v_x_4238_){
_start:
{
if (lean_obj_tag(v_x_4238_) == 0)
{
return v_x_4237_;
}
else
{
lean_object* v_key_4239_; lean_object* v_tail_4240_; lean_object* v___x_4241_; 
v_key_4239_ = lean_ctor_get(v_x_4238_, 0);
v_tail_4240_ = lean_ctor_get(v_x_4238_, 2);
lean_inc(v_key_4239_);
v___x_4241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4241_, 0, v_key_4239_);
lean_ctor_set(v___x_4241_, 1, v_x_4237_);
v_x_4237_ = v___x_4241_;
v_x_4238_ = v_tail_4240_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4243_, lean_object* v_x_4244_){
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4243_, v_x_4244_);
lean_dec(v_x_4244_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4246_, size_t v_i_4247_, size_t v_stop_4248_, lean_object* v_b_4249_){
_start:
{
uint8_t v___x_4250_; 
v___x_4250_ = lean_usize_dec_eq(v_i_4247_, v_stop_4248_);
if (v___x_4250_ == 0)
{
lean_object* v___x_4251_; lean_object* v___x_4252_; size_t v___x_4253_; size_t v___x_4254_; 
v___x_4251_ = lean_array_uget_borrowed(v_as_4246_, v_i_4247_);
v___x_4252_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4249_, v___x_4251_);
v___x_4253_ = ((size_t)1ULL);
v___x_4254_ = lean_usize_add(v_i_4247_, v___x_4253_);
v_i_4247_ = v___x_4254_;
v_b_4249_ = v___x_4252_;
goto _start;
}
else
{
return v_b_4249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4256_, lean_object* v_i_4257_, lean_object* v_stop_4258_, lean_object* v_b_4259_){
_start:
{
size_t v_i_boxed_4260_; size_t v_stop_boxed_4261_; lean_object* v_res_4262_; 
v_i_boxed_4260_ = lean_unbox_usize(v_i_4257_);
lean_dec(v_i_4257_);
v_stop_boxed_4261_ = lean_unbox_usize(v_stop_4258_);
lean_dec(v_stop_4258_);
v_res_4262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4256_, v_i_boxed_4260_, v_stop_boxed_4261_, v_b_4259_);
lean_dec_ref(v_as_4256_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v_buckets_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; uint8_t v___x_4270_; 
v___x_4264_ = l_Lean_attributeMapRef;
v___x_4265_ = lean_st_ref_get(v___x_4264_);
v_buckets_4266_ = lean_ctor_get(v___x_4265_, 1);
lean_inc_ref(v_buckets_4266_);
lean_dec(v___x_4265_);
v___x_4267_ = lean_box(0);
v___x_4268_ = lean_unsigned_to_nat(0u);
v___x_4269_ = lean_array_get_size(v_buckets_4266_);
v___x_4270_ = lean_nat_dec_lt(v___x_4268_, v___x_4269_);
if (v___x_4270_ == 0)
{
lean_object* v___x_4271_; 
lean_dec_ref(v_buckets_4266_);
v___x_4271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4267_);
return v___x_4271_;
}
else
{
size_t v___x_4272_; size_t v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4272_ = ((size_t)0ULL);
v___x_4273_ = lean_usize_of_nat(v___x_4269_);
v___x_4274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4266_, v___x_4272_, v___x_4273_, v___x_4267_);
lean_dec_ref(v_buckets_4266_);
v___x_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4274_);
return v___x_4275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l_Lean_getBuiltinAttributeNames();
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4279_){
_start:
{
lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; 
v___x_4281_ = l_Lean_attributeMapRef;
v___x_4282_ = lean_st_ref_get(v___x_4281_);
v___x_4283_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4282_, v_attrName_4279_);
lean_dec(v___x_4282_);
if (lean_obj_tag(v___x_4283_) == 0)
{
lean_object* v___x_4284_; uint8_t v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
v___x_4284_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4285_ = 1;
v___x_4286_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4279_, v___x_4285_);
v___x_4287_ = lean_string_append(v___x_4284_, v___x_4286_);
lean_dec_ref(v___x_4286_);
v___x_4288_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4289_ = lean_string_append(v___x_4287_, v___x_4288_);
v___x_4290_ = lean_mk_io_user_error(v___x_4289_);
v___x_4291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4291_, 0, v___x_4290_);
return v___x_4291_;
}
else
{
lean_object* v_val_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4299_; 
lean_dec(v_attrName_4279_);
v_val_4292_ = lean_ctor_get(v___x_4283_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4283_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4294_ = v___x_4283_;
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_val_4292_);
lean_dec(v___x_4283_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
lean_ctor_set_tag(v___x_4294_, 0);
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_val_4292_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4300_, lean_object* v_a_4301_){
_start:
{
lean_object* v_res_4302_; 
v_res_4302_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4300_);
return v_res_4302_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4303_, lean_object* v_attrName_4304_){
_start:
{
lean_object* v___x_4305_; lean_object* v_toEnvExtension_4306_; lean_object* v_asyncMode_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; uint8_t v___x_4310_; lean_object* v___x_4311_; lean_object* v_map_4312_; uint8_t v___x_4313_; 
v___x_4305_ = l_Lean_attributeExtension;
v_toEnvExtension_4306_ = lean_ctor_get(v___x_4305_, 0);
v_asyncMode_4307_ = lean_ctor_get(v_toEnvExtension_4306_, 2);
v___x_4308_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4309_ = lean_box(0);
v___x_4310_ = 0;
v___x_4311_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4308_, v___x_4305_, v_env_4303_, v_asyncMode_4307_, v___x_4309_, v___x_4310_);
v_map_4312_ = lean_ctor_get(v___x_4311_, 1);
lean_inc_ref(v_map_4312_);
lean_dec(v___x_4311_);
v___x_4313_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4312_, v_attrName_4304_);
lean_dec_ref(v_map_4312_);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4314_, lean_object* v_attrName_4315_){
_start:
{
uint8_t v_res_4316_; lean_object* v_r_4317_; 
v_res_4316_ = l_Lean_isAttribute(v_env_4314_, v_attrName_4315_);
lean_dec(v_attrName_4315_);
v_r_4317_ = lean_box(v_res_4316_);
return v_r_4317_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4318_){
_start:
{
lean_object* v___x_4319_; lean_object* v_toEnvExtension_4320_; lean_object* v_asyncMode_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; uint8_t v___x_4324_; lean_object* v___x_4325_; lean_object* v_map_4326_; lean_object* v_buckets_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; uint8_t v___x_4331_; 
v___x_4319_ = l_Lean_attributeExtension;
v_toEnvExtension_4320_ = lean_ctor_get(v___x_4319_, 0);
v_asyncMode_4321_ = lean_ctor_get(v_toEnvExtension_4320_, 2);
v___x_4322_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4323_ = lean_box(0);
v___x_4324_ = 0;
v___x_4325_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4322_, v___x_4319_, v_env_4318_, v_asyncMode_4321_, v___x_4323_, v___x_4324_);
v_map_4326_ = lean_ctor_get(v___x_4325_, 1);
lean_inc_ref(v_map_4326_);
lean_dec(v___x_4325_);
v_buckets_4327_ = lean_ctor_get(v_map_4326_, 1);
lean_inc_ref(v_buckets_4327_);
lean_dec_ref(v_map_4326_);
v___x_4328_ = lean_box(0);
v___x_4329_ = lean_unsigned_to_nat(0u);
v___x_4330_ = lean_array_get_size(v_buckets_4327_);
v___x_4331_ = lean_nat_dec_lt(v___x_4329_, v___x_4330_);
if (v___x_4331_ == 0)
{
lean_dec_ref(v_buckets_4327_);
return v___x_4328_;
}
else
{
size_t v___x_4332_; size_t v___x_4333_; lean_object* v___x_4334_; 
v___x_4332_ = ((size_t)0ULL);
v___x_4333_ = lean_usize_of_nat(v___x_4330_);
v___x_4334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4327_, v___x_4332_, v___x_4333_, v___x_4328_);
lean_dec_ref(v_buckets_4327_);
return v___x_4334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4335_, lean_object* v_attrName_4336_){
_start:
{
lean_object* v___x_4337_; lean_object* v_toEnvExtension_4338_; lean_object* v_asyncMode_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; uint8_t v___x_4342_; lean_object* v___x_4343_; lean_object* v_map_4344_; lean_object* v___x_4345_; 
v___x_4337_ = l_Lean_attributeExtension;
v_toEnvExtension_4338_ = lean_ctor_get(v___x_4337_, 0);
v_asyncMode_4339_ = lean_ctor_get(v_toEnvExtension_4338_, 2);
v___x_4340_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4341_ = lean_box(0);
v___x_4342_ = 0;
v___x_4343_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4340_, v___x_4337_, v_env_4335_, v_asyncMode_4339_, v___x_4341_, v___x_4342_);
v_map_4344_ = lean_ctor_get(v___x_4343_, 1);
lean_inc_ref(v_map_4344_);
lean_dec(v___x_4343_);
v___x_4345_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4344_, v_attrName_4336_);
lean_dec_ref(v_map_4344_);
if (lean_obj_tag(v___x_4345_) == 0)
{
lean_object* v___x_4346_; uint8_t v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4346_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4347_ = 1;
v___x_4348_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4336_, v___x_4347_);
v___x_4349_ = lean_string_append(v___x_4346_, v___x_4348_);
lean_dec_ref(v___x_4348_);
v___x_4350_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4351_ = lean_string_append(v___x_4349_, v___x_4350_);
v___x_4352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4352_, 0, v___x_4351_);
return v___x_4352_;
}
else
{
lean_object* v_val_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4360_; 
lean_dec(v_attrName_4336_);
v_val_4353_ = lean_ctor_get(v___x_4345_, 0);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4345_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4355_ = v___x_4345_;
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_val_4353_);
lean_dec(v___x_4345_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4358_; 
if (v_isShared_4356_ == 0)
{
v___x_4358_ = v___x_4355_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v_val_4353_);
v___x_4358_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
return v___x_4358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___lam__0(lean_object* v_addEntryFn_4361_, lean_object* v___x_4362_, lean_object* v_s_4363_){
_start:
{
lean_object* v_importedEntries_4364_; lean_object* v_state_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4373_; 
v_importedEntries_4364_ = lean_ctor_get(v_s_4363_, 0);
v_state_4365_ = lean_ctor_get(v_s_4363_, 1);
v_isSharedCheck_4373_ = !lean_is_exclusive(v_s_4363_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4367_ = v_s_4363_;
v_isShared_4368_ = v_isSharedCheck_4373_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_state_4365_);
lean_inc(v_importedEntries_4364_);
lean_dec(v_s_4363_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4373_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v_state_4369_; lean_object* v___x_4371_; 
v_state_4369_ = lean_apply_2(v_addEntryFn_4361_, v_state_4365_, v___x_4362_);
if (v_isShared_4368_ == 0)
{
lean_ctor_set(v___x_4367_, 1, v_state_4369_);
v___x_4371_ = v___x_4367_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_importedEntries_4364_);
lean_ctor_set(v_reuseFailAlloc_4372_, 1, v_state_4369_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4374_, lean_object* v_builderId_4375_, lean_object* v_ref_4376_, lean_object* v_args_4377_){
_start:
{
lean_object* v_entry_4379_; lean_object* v___x_4380_; 
v_entry_4379_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4379_, 0, v_builderId_4375_);
lean_ctor_set(v_entry_4379_, 1, v_ref_4376_);
lean_ctor_set(v_entry_4379_, 2, v_args_4377_);
lean_inc_ref(v_entry_4379_);
v___x_4380_ = l_Lean_mkAttributeImplOfEntry(v_entry_4379_);
if (lean_obj_tag(v___x_4380_) == 0)
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4415_; 
v_a_4381_ = lean_ctor_get(v___x_4380_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4383_ = v___x_4380_;
v_isShared_4384_ = v_isSharedCheck_4415_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4380_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4415_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v_toAttributeImplCore_4385_; lean_object* v_name_4386_; uint8_t v___x_4387_; 
v_toAttributeImplCore_4385_ = lean_ctor_get(v_a_4381_, 0);
v_name_4386_ = lean_ctor_get(v_toAttributeImplCore_4385_, 1);
lean_inc_ref(v_env_4374_);
v___x_4387_ = l_Lean_isAttribute(v_env_4374_, v_name_4386_);
if (v___x_4387_ == 0)
{
lean_object* v___x_4388_; lean_object* v_toEnvExtension_4389_; lean_object* v_addEntryFn_4390_; lean_object* v_asyncMode_4391_; uint8_t v_logWrites_4392_; lean_object* v___x_4393_; lean_object* v___f_4394_; lean_object* v___x_4395_; uint8_t v___x_4396_; 
v___x_4388_ = l_Lean_attributeExtension;
v_toEnvExtension_4389_ = lean_ctor_get(v___x_4388_, 0);
v_addEntryFn_4390_ = lean_ctor_get(v___x_4388_, 3);
v_asyncMode_4391_ = lean_ctor_get(v_toEnvExtension_4389_, 2);
v_logWrites_4392_ = lean_ctor_get_uint8(v_toEnvExtension_4389_, sizeof(void*)*6);
v___x_4393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4393_, 0, v_entry_4379_);
lean_ctor_set(v___x_4393_, 1, v_a_4381_);
lean_inc(v_addEntryFn_4390_);
v___f_4394_ = lean_alloc_closure((void*)(l_Lean_registerAttributeOfBuilder___lam__0), 3, 2);
lean_closure_set(v___f_4394_, 0, v_addEntryFn_4390_);
lean_closure_set(v___f_4394_, 1, v___x_4393_);
v___x_4395_ = lean_box(0);
v___x_4396_ = 1;
if (v_logWrites_4392_ == 0)
{
lean_object* v___x_4397_; lean_object* v___x_4399_; 
lean_inc_ref(v_toEnvExtension_4389_);
v___x_4397_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4389_, v_env_4374_, v___f_4394_, v_asyncMode_4391_, v___x_4395_, v___x_4396_);
if (v_isShared_4384_ == 0)
{
lean_ctor_set(v___x_4383_, 0, v___x_4397_);
v___x_4399_ = v___x_4383_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v___x_4397_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
return v___x_4399_;
}
}
else
{
lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4404_; 
lean_inc_ref_n(v_toEnvExtension_4389_, 2);
v___x_4401_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4389_, v_env_4374_);
lean_dec_ref(v_env_4374_);
v___x_4402_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4389_, v___x_4401_, v___f_4394_, v_asyncMode_4391_, v___x_4395_, v___x_4396_);
if (v_isShared_4384_ == 0)
{
lean_ctor_set(v___x_4383_, 0, v___x_4402_);
v___x_4404_ = v___x_4383_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v___x_4402_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
}
}
}
else
{
lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4413_; 
lean_inc(v_name_4386_);
lean_dec(v_a_4381_);
lean_dec_ref_known(v_entry_4379_, 3);
lean_dec_ref(v_env_4374_);
v___x_4406_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4407_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4386_, v___x_4387_);
v___x_4408_ = lean_string_append(v___x_4406_, v___x_4407_);
lean_dec_ref(v___x_4407_);
v___x_4409_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4410_ = lean_string_append(v___x_4408_, v___x_4409_);
v___x_4411_ = lean_mk_io_user_error(v___x_4410_);
if (v_isShared_4384_ == 0)
{
lean_ctor_set_tag(v___x_4383_, 1);
lean_ctor_set(v___x_4383_, 0, v___x_4411_);
v___x_4413_ = v___x_4383_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v___x_4411_);
v___x_4413_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
return v___x_4413_;
}
}
}
}
else
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4423_; 
lean_dec_ref_known(v_entry_4379_, 3);
lean_dec_ref(v_env_4374_);
v_a_4416_ = lean_ctor_get(v___x_4380_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4418_ = v___x_4380_;
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4380_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4421_; 
if (v_isShared_4419_ == 0)
{
v___x_4421_ = v___x_4418_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_a_4416_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4424_, lean_object* v_builderId_4425_, lean_object* v_ref_4426_, lean_object* v_args_4427_, lean_object* v_a_4428_){
_start:
{
lean_object* v_res_4429_; 
v_res_4429_ = l_Lean_registerAttributeOfBuilder(v_env_4424_, v_builderId_4425_, v_ref_4426_, v_args_4427_);
return v_res_4429_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
if (lean_obj_tag(v_x_4430_) == 0)
{
lean_object* v_a_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v_a_4434_ = lean_ctor_get(v_x_4430_, 0);
lean_inc(v_a_4434_);
lean_dec_ref_known(v_x_4430_, 1);
v___x_4435_ = l_Lean_stringToMessageData(v_a_4434_);
v___x_4436_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4435_, v___y_4431_, v___y_4432_);
return v___x_4436_;
}
else
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
v_a_4437_ = lean_ctor_get(v_x_4430_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v_x_4430_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v_x_4430_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v_x_4430_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4442_; 
if (v_isShared_4440_ == 0)
{
lean_ctor_set_tag(v___x_4439_, 0);
v___x_4442_ = v___x_4439_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4437_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_){
_start:
{
lean_object* v_res_4449_; 
v_res_4449_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4445_, v___y_4446_, v___y_4447_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4450_, lean_object* v_attrName_4451_, lean_object* v_stx_4452_, uint8_t v_kind_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_){
_start:
{
lean_object* v___x_4457_; lean_object* v_env_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4457_ = lean_st_ref_get(v_a_4455_);
v_env_4458_ = lean_ctor_get(v___x_4457_, 0);
lean_inc_ref(v_env_4458_);
lean_dec(v___x_4457_);
v___x_4459_ = l_Lean_getAttributeImpl(v_env_4458_, v_attrName_4451_);
v___x_4460_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4459_, v_a_4454_, v_a_4455_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_a_4461_; lean_object* v_add_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; 
v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
lean_inc(v_a_4461_);
lean_dec_ref_known(v___x_4460_, 1);
v_add_4462_ = lean_ctor_get(v_a_4461_, 1);
lean_inc_ref(v_add_4462_);
lean_dec(v_a_4461_);
v___x_4463_ = lean_box(v_kind_4453_);
lean_inc(v_a_4455_);
lean_inc_ref(v_a_4454_);
v___x_4464_ = lean_apply_6(v_add_4462_, v_declName_4450_, v_stx_4452_, v___x_4463_, v_a_4454_, v_a_4455_, lean_box(0));
return v___x_4464_;
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
lean_dec(v_stx_4452_);
lean_dec(v_declName_4450_);
v_a_4465_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4460_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4460_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4473_, lean_object* v_attrName_4474_, lean_object* v_stx_4475_, lean_object* v_kind_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_){
_start:
{
uint8_t v_kind_boxed_4480_; lean_object* v_res_4481_; 
v_kind_boxed_4480_ = lean_unbox(v_kind_4476_);
v_res_4481_ = l_Lean_Attribute_add(v_declName_4473_, v_attrName_4474_, v_stx_4475_, v_kind_boxed_4480_, v_a_4477_, v_a_4478_);
lean_dec(v_a_4478_);
lean_dec_ref(v_a_4477_);
return v_res_4481_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4482_, lean_object* v_x_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_){
_start:
{
lean_object* v___x_4487_; 
v___x_4487_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4483_, v___y_4484_, v___y_4485_);
return v___x_4487_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4488_, lean_object* v_x_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
lean_object* v_res_4493_; 
v_res_4493_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4488_, v_x_4489_, v___y_4490_, v___y_4491_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
return v_res_4493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4494_, lean_object* v_attrName_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_){
_start:
{
lean_object* v___x_4499_; lean_object* v_env_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; 
v___x_4499_ = lean_st_ref_get(v_a_4497_);
v_env_4500_ = lean_ctor_get(v___x_4499_, 0);
lean_inc_ref(v_env_4500_);
lean_dec(v___x_4499_);
v___x_4501_ = l_Lean_getAttributeImpl(v_env_4500_, v_attrName_4495_);
v___x_4502_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4501_, v_a_4496_, v_a_4497_);
if (lean_obj_tag(v___x_4502_) == 0)
{
lean_object* v_a_4503_; lean_object* v_erase_4504_; lean_object* v___x_4505_; 
v_a_4503_ = lean_ctor_get(v___x_4502_, 0);
lean_inc(v_a_4503_);
lean_dec_ref_known(v___x_4502_, 1);
v_erase_4504_ = lean_ctor_get(v_a_4503_, 2);
lean_inc_ref(v_erase_4504_);
lean_dec(v_a_4503_);
lean_inc(v_a_4497_);
lean_inc_ref(v_a_4496_);
v___x_4505_ = lean_apply_4(v_erase_4504_, v_declName_4494_, v_a_4496_, v_a_4497_, lean_box(0));
return v___x_4505_;
}
else
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_dec(v_declName_4494_);
v_a_4506_ = lean_ctor_get(v___x_4502_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4502_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4502_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4502_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4514_, lean_object* v_attrName_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_){
_start:
{
lean_object* v_res_4519_; 
v_res_4519_ = l_Lean_Attribute_erase(v_declName_4514_, v_attrName_4515_, v_a_4516_, v_a_4517_);
lean_dec(v_a_4517_);
lean_dec_ref(v_a_4516_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___lam__0(lean_object* v___y_4520_, lean_object* v_ps_4521_){
_start:
{
lean_object* v_importedEntries_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4529_; 
v_importedEntries_4522_ = lean_ctor_get(v_ps_4521_, 0);
v_isSharedCheck_4529_ = !lean_is_exclusive(v_ps_4521_);
if (v_isSharedCheck_4529_ == 0)
{
lean_object* v_unused_4530_; 
v_unused_4530_ = lean_ctor_get(v_ps_4521_, 1);
lean_dec(v_unused_4530_);
v___x_4524_ = v_ps_4521_;
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_importedEntries_4522_);
lean_dec(v_ps_4521_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v___x_4527_; 
if (v_isShared_4525_ == 0)
{
lean_ctor_set(v___x_4524_, 1, v___y_4520_);
v___x_4527_ = v___x_4524_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_importedEntries_4522_);
lean_ctor_set(v_reuseFailAlloc_4528_, 1, v___y_4520_);
v___x_4527_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
return v___x_4527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4531_, lean_object* v_x_4532_){
_start:
{
if (lean_obj_tag(v_x_4532_) == 0)
{
return v_x_4531_;
}
else
{
lean_object* v_key_4533_; lean_object* v_value_4534_; lean_object* v_tail_4535_; lean_object* v_newEntries_4536_; lean_object* v_map_4537_; uint8_t v___x_4538_; 
v_key_4533_ = lean_ctor_get(v_x_4532_, 0);
lean_inc(v_key_4533_);
v_value_4534_ = lean_ctor_get(v_x_4532_, 1);
lean_inc(v_value_4534_);
v_tail_4535_ = lean_ctor_get(v_x_4532_, 2);
lean_inc(v_tail_4535_);
lean_dec_ref_known(v_x_4532_, 3);
v_newEntries_4536_ = lean_ctor_get(v_x_4531_, 0);
v_map_4537_ = lean_ctor_get(v_x_4531_, 1);
v___x_4538_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4537_, v_key_4533_);
if (v___x_4538_ == 0)
{
lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4547_; 
lean_inc_ref(v_map_4537_);
lean_inc(v_newEntries_4536_);
v_isSharedCheck_4547_ = !lean_is_exclusive(v_x_4531_);
if (v_isSharedCheck_4547_ == 0)
{
lean_object* v_unused_4548_; lean_object* v_unused_4549_; 
v_unused_4548_ = lean_ctor_get(v_x_4531_, 1);
lean_dec(v_unused_4548_);
v_unused_4549_ = lean_ctor_get(v_x_4531_, 0);
lean_dec(v_unused_4549_);
v___x_4540_ = v_x_4531_;
v_isShared_4541_ = v_isSharedCheck_4547_;
goto v_resetjp_4539_;
}
else
{
lean_dec(v_x_4531_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4547_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
lean_object* v___x_4542_; lean_object* v___x_4544_; 
v___x_4542_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4537_, v_key_4533_, v_value_4534_);
if (v_isShared_4541_ == 0)
{
lean_ctor_set(v___x_4540_, 1, v___x_4542_);
v___x_4544_ = v___x_4540_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_newEntries_4536_);
lean_ctor_set(v_reuseFailAlloc_4546_, 1, v___x_4542_);
v___x_4544_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
v_x_4531_ = v___x_4544_;
v_x_4532_ = v_tail_4535_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4534_);
lean_dec(v_key_4533_);
v_x_4532_ = v_tail_4535_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4551_, size_t v_i_4552_, size_t v_stop_4553_, lean_object* v_b_4554_){
_start:
{
uint8_t v___x_4555_; 
v___x_4555_ = lean_usize_dec_eq(v_i_4552_, v_stop_4553_);
if (v___x_4555_ == 0)
{
lean_object* v___x_4556_; lean_object* v___x_4557_; size_t v___x_4558_; size_t v___x_4559_; 
v___x_4556_ = lean_array_uget_borrowed(v_as_4551_, v_i_4552_);
lean_inc(v___x_4556_);
v___x_4557_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4554_, v___x_4556_);
v___x_4558_ = ((size_t)1ULL);
v___x_4559_ = lean_usize_add(v_i_4552_, v___x_4558_);
v_i_4552_ = v___x_4559_;
v_b_4554_ = v___x_4557_;
goto _start;
}
else
{
return v_b_4554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4561_, lean_object* v_i_4562_, lean_object* v_stop_4563_, lean_object* v_b_4564_){
_start:
{
size_t v_i_boxed_4565_; size_t v_stop_boxed_4566_; lean_object* v_res_4567_; 
v_i_boxed_4565_ = lean_unbox_usize(v_i_4562_);
lean_dec(v_i_4562_);
v_stop_boxed_4566_ = lean_unbox_usize(v_stop_4563_);
lean_dec(v_stop_4563_);
v_res_4567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4561_, v_i_boxed_4565_, v_stop_boxed_4566_, v_b_4564_);
lean_dec_ref(v_as_4561_);
return v_res_4567_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4568_){
_start:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v_toEnvExtension_4574_; lean_object* v_asyncMode_4575_; uint8_t v_logWrites_4576_; lean_object* v___y_4578_; lean_object* v_buckets_4587_; lean_object* v___x_4588_; uint8_t v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; uint8_t v___x_4593_; 
v___x_4570_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4571_ = l_Lean_attributeMapRef;
v___x_4572_ = lean_st_ref_get(v___x_4571_);
v___x_4573_ = l_Lean_attributeExtension;
v_toEnvExtension_4574_ = lean_ctor_get(v___x_4573_, 0);
v_asyncMode_4575_ = lean_ctor_get(v_toEnvExtension_4574_, 2);
v_logWrites_4576_ = lean_ctor_get_uint8(v_toEnvExtension_4574_, sizeof(void*)*6);
v_buckets_4587_ = lean_ctor_get(v___x_4572_, 1);
lean_inc_ref(v_buckets_4587_);
lean_dec(v___x_4572_);
v___x_4588_ = lean_box(0);
v___x_4589_ = 0;
lean_inc_ref(v_env_4568_);
v___x_4590_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4570_, v___x_4573_, v_env_4568_, v_asyncMode_4575_, v___x_4588_, v___x_4589_);
v___x_4591_ = lean_unsigned_to_nat(0u);
v___x_4592_ = lean_array_get_size(v_buckets_4587_);
v___x_4593_ = lean_nat_dec_lt(v___x_4591_, v___x_4592_);
if (v___x_4593_ == 0)
{
lean_dec_ref(v_buckets_4587_);
v___y_4578_ = v___x_4590_;
goto v___jp_4577_;
}
else
{
size_t v___x_4594_; size_t v___x_4595_; lean_object* v___x_4596_; 
v___x_4594_ = ((size_t)0ULL);
v___x_4595_ = lean_usize_of_nat(v___x_4592_);
v___x_4596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4587_, v___x_4594_, v___x_4595_, v___x_4590_);
lean_dec_ref(v_buckets_4587_);
v___y_4578_ = v___x_4596_;
goto v___jp_4577_;
}
v___jp_4577_:
{
lean_object* v___f_4579_; lean_object* v___x_4580_; uint8_t v___x_4581_; 
v___f_4579_ = lean_alloc_closure((void*)(l_Lean_updateEnvAttributesImpl___lam__0), 2, 1);
lean_closure_set(v___f_4579_, 0, v___y_4578_);
v___x_4580_ = lean_box(0);
v___x_4581_ = 1;
if (v_logWrites_4576_ == 0)
{
lean_object* v___x_4582_; lean_object* v___x_4583_; 
lean_inc_ref(v_toEnvExtension_4574_);
v___x_4582_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4574_, v_env_4568_, v___f_4579_, v_asyncMode_4575_, v___x_4580_, v___x_4581_);
v___x_4583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4582_);
return v___x_4583_;
}
else
{
lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; 
lean_inc_ref_n(v_toEnvExtension_4574_, 2);
v___x_4584_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4574_, v_env_4568_);
lean_dec_ref(v_env_4568_);
v___x_4585_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4574_, v___x_4584_, v___f_4579_, v_asyncMode_4575_, v___x_4580_, v___x_4581_);
v___x_4586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4586_, 0, v___x_4585_);
return v___x_4586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4597_, lean_object* v_a_4598_){
_start:
{
lean_object* v_res_4599_; 
v_res_4599_ = lean_update_env_attributes(v_env_4597_);
return v_res_4599_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v_size_4603_; lean_object* v___x_4604_; 
v___x_4601_ = l_Lean_attributeMapRef;
v___x_4602_ = lean_st_ref_get(v___x_4601_);
v_size_4603_ = lean_ctor_get(v___x_4602_, 0);
lean_inc(v_size_4603_);
lean_dec(v___x_4602_);
v___x_4604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4604_, 0, v_size_4603_);
return v___x_4604_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4605_){
_start:
{
lean_object* v_res_4606_; 
v_res_4606_ = lean_get_num_attributes();
return v_res_4606_;
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
res = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2586810433____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_automationAttrsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_automationAttrsRef);
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
