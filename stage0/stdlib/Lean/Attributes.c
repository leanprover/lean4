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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object* v_ref_658_, lean_object* v_msg_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_toCold_663_; lean_object* v_currRecDepth_664_; lean_object* v_ref_665_; uint16_t v_optionFlags_666_; uint8_t v_suppressElabErrors_667_; uint8_t v_checkDeprecated_668_; uint8_t v_isRecordingDeps_669_; lean_object* v_ref_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_toCold_663_ = lean_ctor_get(v___y_660_, 0);
v_currRecDepth_664_ = lean_ctor_get(v___y_660_, 1);
v_ref_665_ = lean_ctor_get(v___y_660_, 2);
v_optionFlags_666_ = lean_ctor_get_uint16(v___y_660_, sizeof(void*)*3);
v_suppressElabErrors_667_ = lean_ctor_get_uint8(v___y_660_, sizeof(void*)*3 + 2);
v_checkDeprecated_668_ = lean_ctor_get_uint8(v___y_660_, sizeof(void*)*3 + 3);
v_isRecordingDeps_669_ = lean_ctor_get_uint8(v___y_660_, sizeof(void*)*3 + 4);
v_ref_670_ = l_Lean_replaceRef(v_ref_658_, v_ref_665_);
lean_inc(v_currRecDepth_664_);
lean_inc_ref(v_toCold_663_);
v___x_671_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_671_, 0, v_toCold_663_);
lean_ctor_set(v___x_671_, 1, v_currRecDepth_664_);
lean_ctor_set(v___x_671_, 2, v_ref_670_);
lean_ctor_set_uint16(v___x_671_, sizeof(void*)*3, v_optionFlags_666_);
lean_ctor_set_uint8(v___x_671_, sizeof(void*)*3 + 2, v_suppressElabErrors_667_);
lean_ctor_set_uint8(v___x_671_, sizeof(void*)*3 + 3, v_checkDeprecated_668_);
lean_ctor_set_uint8(v___x_671_, sizeof(void*)*3 + 4, v_isRecordingDeps_669_);
v___x_672_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_659_, v___x_671_, v___y_661_);
lean_dec_ref_known(v___x_671_, 3);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object* v_ref_673_, lean_object* v_msg_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_673_, v_msg_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v_ref_673_);
return v_res_678_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__3));
v___x_688_ = l_Lean_stringToMessageData(v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object* v_stx_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_699_; lean_object* v___x_709_; uint8_t v___x_710_; 
lean_inc(v_stx_695_);
v___x_699_ = l_Lean_Syntax_getKind(v_stx_695_);
v___x_709_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_710_ = lean_name_eq(v___x_699_, v___x_709_);
if (v___x_710_ == 0)
{
goto v___jp_700_;
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_711_ = lean_unsigned_to_nat(1u);
v___x_712_ = l_Lean_Syntax_getArg(v_stx_695_, v___x_711_);
v___x_713_ = l_Lean_Syntax_isNone(v___x_712_);
lean_dec(v___x_712_);
if (v___x_713_ == 0)
{
goto v___jp_700_;
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_714_ = lean_unsigned_to_nat(2u);
v___x_715_ = l_Lean_Syntax_getArg(v_stx_695_, v___x_714_);
v___x_716_ = l_Lean_Syntax_isNone(v___x_715_);
lean_dec(v___x_715_);
if (v___x_716_ == 0)
{
goto v___jp_700_;
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; 
lean_dec(v___x_699_);
lean_dec(v_stx_695_);
v___x_717_ = lean_box(0);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
return v___x_718_;
}
}
}
v___jp_700_:
{
lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_701_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__2));
v___x_702_ = lean_name_eq(v___x_699_, v___x_701_);
lean_dec(v___x_699_);
if (v___x_702_ == 0)
{
if (lean_obj_tag(v_stx_695_) == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_box(0);
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_obj_once(&l_Lean_Attribute_Builtin_ensureNoArgs___closed__4, &l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once, _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4);
v___x_706_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_695_, v___x_705_, v_a_696_, v_a_697_);
lean_dec(v_stx_695_);
return v___x_706_;
}
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec(v_stx_695_);
v___x_707_ = lean_box(0);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object* v_stx_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_719_, v_a_720_, v_a_721_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object* v_00_u03b1_724_, lean_object* v_ref_725_, lean_object* v_msg_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_725_, v_msg_726_, v___y_727_, v___y_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object* v_00_u03b1_731_, lean_object* v_ref_732_, lean_object* v_msg_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(v_00_u03b1_731_, v_ref_732_, v_msg_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v_ref_732_);
return v_res_737_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__4));
v___x_752_ = l_Lean_stringToMessageData(v___x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object* v_stx_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
lean_inc(v_stx_753_);
v___x_765_ = l_Lean_Syntax_getKind(v_stx_753_);
v___x_766_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_767_ = lean_name_eq(v___x_765_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_769_ = lean_name_eq(v___x_765_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_771_ = lean_name_eq(v___x_765_, v___x_770_);
lean_dec(v___x_765_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_773_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_753_, v___x_772_, v_a_754_, v_a_755_);
lean_dec(v_stx_753_);
return v___x_773_;
}
else
{
goto v___jp_757_;
}
}
else
{
lean_dec(v___x_765_);
goto v___jp_757_;
}
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
lean_dec(v___x_765_);
v___x_774_ = lean_unsigned_to_nat(1u);
v___x_775_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_774_);
lean_dec(v_stx_753_);
v___x_776_ = l_Lean_Syntax_isNone(v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = l_Lean_Syntax_getArg(v___x_775_, v___x_777_);
lean_dec(v___x_775_);
v___x_779_ = l_Lean_Syntax_isIdent(v___x_778_);
if (v___x_779_ == 0)
{
lean_dec(v___x_778_);
goto v___jp_762_;
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_778_);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
}
else
{
lean_dec(v___x_775_);
goto v___jp_762_;
}
}
v___jp_757_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_758_ = lean_unsigned_to_nat(1u);
v___x_759_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_758_);
lean_dec(v_stx_753_);
v___x_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
v___jp_762_:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_box(0);
v___x_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
return v___x_764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object* v_stx_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_782_, v_a_783_, v_a_784_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
return v_res_786_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent___closed__1(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent___closed__0));
v___x_789_ = l_Lean_stringToMessageData(v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v___x_794_; 
lean_inc(v_stx_790_);
v___x_794_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_790_, v_a_791_, v_a_792_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_808_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_808_ == 0)
{
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_808_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_808_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
if (lean_obj_tag(v_a_795_) == 0)
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
lean_del_object(v___x_797_);
v___x_799_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent___closed__1, &l_Lean_Attribute_Builtin_getIdent___closed__1_once, _init_l_Lean_Attribute_Builtin_getIdent___closed__1);
lean_inc(v_stx_790_);
v___x_800_ = l_Lean_MessageData_ofSyntax(v_stx_790_);
v___x_801_ = l_Lean_indentD(v___x_800_);
v___x_802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_799_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_790_, v___x_802_, v_a_791_, v_a_792_);
lean_dec(v_stx_790_);
return v___x_803_;
}
else
{
lean_object* v_val_804_; lean_object* v___x_806_; 
lean_dec(v_stx_790_);
v_val_804_ = lean_ctor_get(v_a_795_, 0);
lean_inc(v_val_804_);
lean_dec_ref_known(v_a_795_, 1);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v_val_804_);
v___x_806_ = v___x_797_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_val_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec(v_stx_790_);
v_a_809_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_794_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_794_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_Attribute_Builtin_getIdent(v_stx_817_, v_a_818_, v_a_819_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_822_, v_a_823_, v_a_824_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_847_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_847_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_847_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_847_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
if (lean_obj_tag(v_a_827_) == 0)
{
lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_831_ = lean_box(0);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_831_);
v___x_833_ = v___x_829_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
else
{
lean_object* v_val_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_846_; 
v_val_835_ = lean_ctor_get(v_a_827_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v_a_827_);
if (v_isSharedCheck_846_ == 0)
{
v___x_837_ = v_a_827_;
v_isShared_838_ = v_isSharedCheck_846_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_val_835_);
lean_dec(v_a_827_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_846_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_839_ = l_Lean_Syntax_getId(v_val_835_);
lean_dec(v_val_835_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_839_);
v___x_841_ = v___x_837_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_839_);
v___x_841_ = v_reuseFailAlloc_845_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
lean_object* v___x_843_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_841_);
v___x_843_ = v___x_829_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
v_a_848_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_826_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_826_);
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
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_856_, v_a_857_, v_a_858_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_Attribute_Builtin_getIdent(v_stx_861_, v_a_862_, v_a_863_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_874_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_874_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_874_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_874_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = l_Lean_Syntax_getId(v_a_866_);
lean_dec(v_a_866_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_870_);
v___x_872_ = v___x_868_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v_a_875_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_865_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_865_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Attribute_Builtin_getId(v_stx_883_, v_a_884_, v_a_885_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
return v_res_887_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_890_ = l_Lean_stringToMessageData(v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
uint8_t v___x_895_; 
v___x_895_ = l_Lean_Syntax_isNone(v_optPrioStx_891_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = l_Lean_Syntax_getArg(v_optPrioStx_891_, v___x_896_);
v___x_898_ = l_Lean_Syntax_isNatLit_x3f(v___x_897_);
lean_dec(v___x_897_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_899_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_891_);
v___x_900_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_891_);
v___x_901_ = l_Lean_indentD(v___x_900_);
v___x_902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_899_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_891_, v___x_902_, v_a_892_, v_a_893_);
lean_dec(v_optPrioStx_891_);
return v___x_903_;
}
else
{
lean_object* v_val_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec(v_optPrioStx_891_);
v_val_904_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_898_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_val_904_);
lean_dec(v___x_898_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
lean_ctor_set_tag(v___x_906_, 0);
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_val_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec(v_optPrioStx_891_);
v___x_912_ = lean_unsigned_to_nat(1000u);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object* v_optPrioStx_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_914_, v_a_915_, v_a_916_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
return v_res_918_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getPrio___closed__1(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l_Lean_Attribute_Builtin_getPrio___closed__0));
v___x_921_ = l_Lean_stringToMessageData(v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
lean_inc(v_stx_922_);
v___x_926_ = l_Lean_Syntax_getKind(v_stx_922_);
v___x_927_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_928_ = lean_name_eq(v___x_926_, v___x_927_);
lean_dec(v___x_926_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_929_ = lean_obj_once(&l_Lean_Attribute_Builtin_getPrio___closed__1, &l_Lean_Attribute_Builtin_getPrio___closed__1_once, _init_l_Lean_Attribute_Builtin_getPrio___closed__1);
lean_inc(v_stx_922_);
v___x_930_ = l_Lean_MessageData_ofSyntax(v_stx_922_);
v___x_931_ = l_Lean_indentD(v___x_930_);
v___x_932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_929_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_922_, v___x_932_, v_a_923_, v_a_924_);
lean_dec(v_stx_922_);
return v___x_933_;
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = lean_unsigned_to_nat(1u);
v___x_935_ = l_Lean_Syntax_getArg(v_stx_922_, v___x_934_);
lean_dec(v_stx_922_);
v___x_936_ = l_Lean_getAttrParamOptPrio(v___x_935_, v_a_923_, v_a_924_);
return v___x_936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_Attribute_Builtin_getPrio(v_stx_937_, v_a_938_, v_a_939_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
return v_res_941_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_944_ = l_Lean_stringToMessageData(v___x_943_);
return v___x_944_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_947_ = l_Lean_stringToMessageData(v___x_946_);
return v___x_947_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_950_ = l_Lean_stringToMessageData(v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_951_, lean_object* v_inst_952_, lean_object* v_name_953_, uint8_t v_kind_954_){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___y_961_; 
v___x_955_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_956_ = l_Lean_MessageData_ofName(v_name_953_);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
switch(v_kind_954_)
{
case 0:
{
lean_object* v___x_968_; 
v___x_968_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_961_ = v___x_968_;
goto v___jp_960_;
}
case 1:
{
lean_object* v___x_969_; 
v___x_969_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_961_ = v___x_969_;
goto v___jp_960_;
}
default: 
{
lean_object* v___x_970_; 
v___x_970_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_961_ = v___x_970_;
goto v___jp_960_;
}
}
v___jp_960_:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
lean_inc_ref(v___y_961_);
v___x_962_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_962_, 0, v___y_961_);
v___x_963_ = l_Lean_MessageData_ofFormat(v___x_962_);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_959_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = l_Lean_throwError___redArg(v_inst_951_, v_inst_952_, v___x_966_);
return v___x_967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_971_, lean_object* v_inst_972_, lean_object* v_name_973_, lean_object* v_kind_974_){
_start:
{
uint8_t v_kind_boxed_975_; lean_object* v_res_976_; 
v_kind_boxed_975_ = lean_unbox(v_kind_974_);
v_res_976_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_971_, v_inst_972_, v_name_973_, v_kind_boxed_975_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_977_, lean_object* v_inst_978_, lean_object* v_inst_979_, lean_object* v_00_u03b1_980_, lean_object* v_name_981_, uint8_t v_kind_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_978_, v_inst_979_, v_name_981_, v_kind_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_984_, lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_00_u03b1_987_, lean_object* v_name_988_, lean_object* v_kind_989_){
_start:
{
uint8_t v_kind_boxed_990_; lean_object* v_res_991_; 
v_kind_boxed_990_ = lean_unbox(v_kind_989_);
v_res_991_ = l_Lean_throwAttrMustBeGlobal(v_m_984_, v_inst_985_, v_inst_986_, v_00_u03b1_987_, v_name_988_, v_kind_boxed_990_);
return v_res_991_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_994_ = l_Lean_stringToMessageData(v___x_993_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_997_ = l_Lean_stringToMessageData(v___x_996_);
return v___x_997_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_1000_ = l_Lean_stringToMessageData(v___x_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_1001_, lean_object* v_inst_1002_, lean_object* v_attrName_1003_, lean_object* v_declName_1004_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1005_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1006_ = l_Lean_MessageData_ofName(v_attrName_1003_);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = 0;
v___x_1011_ = l_Lean_MessageData_ofConstName(v_declName_1004_, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1009_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = l_Lean_throwError___redArg(v_inst_1001_, v_inst_1002_, v___x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1016_, lean_object* v_inst_1017_, lean_object* v_inst_1018_, lean_object* v_00_u03b1_1019_, lean_object* v_attrName_1020_, lean_object* v_declName_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1017_, v_inst_1018_, v_attrName_1020_, v_declName_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1028_ = l_Lean_stringToMessageData(v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_attrName_1031_, lean_object* v_declName_1032_, lean_object* v_asyncPrefix_x3f_1033_){
_start:
{
lean_object* v___y_1035_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1033_) == 0)
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lean_MessageData_nil;
v___y_1035_ = v___x_1048_;
goto v___jp_1034_;
}
else
{
lean_object* v_val_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v_val_1049_ = lean_ctor_get(v_asyncPrefix_x3f_1033_, 0);
lean_inc(v_val_1049_);
lean_dec_ref_known(v_asyncPrefix_x3f_1033_, 1);
v___x_1050_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1051_ = l_Lean_MessageData_ofName(v_val_1049_);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___y_1035_ = v___x_1054_;
goto v___jp_1034_;
}
v___jp_1034_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1036_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1037_ = l_Lean_MessageData_ofName(v_attrName_1031_);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = 0;
v___x_1042_ = l_Lean_MessageData_ofConstName(v_declName_1032_, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1040_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v___y_1035_);
v___x_1047_ = l_Lean_throwError___redArg(v_inst_1029_, v_inst_1030_, v___x_1046_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1055_, lean_object* v_inst_1056_, lean_object* v_inst_1057_, lean_object* v_00_u03b1_1058_, lean_object* v_attrName_1059_, lean_object* v_declName_1060_, lean_object* v_asyncPrefix_x3f_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1056_, v_inst_1057_, v_attrName_1059_, v_declName_1060_, v_asyncPrefix_x3f_1061_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1065_ = l_Lean_stringToMessageData(v___x_1064_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1068_ = l_Lean_stringToMessageData(v___x_1067_);
return v___x_1068_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1071_ = l_Lean_stringToMessageData(v___x_1070_);
return v___x_1071_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1074_ = l_Lean_stringToMessageData(v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1075_, lean_object* v_inst_1076_, lean_object* v_attrName_1077_, lean_object* v_declName_1078_, lean_object* v_givenType_1079_, lean_object* v_expectedType_1080_){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1081_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1082_ = l_Lean_MessageData_ofName(v_attrName_1077_);
lean_inc_ref(v___x_1082_);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = 0;
v___x_1087_ = l_Lean_MessageData_ofConstName(v_declName_1078_, v___x_1086_);
v___x_1088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1085_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = l_Lean_indentExpr(v_givenType_1079_);
v___x_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v___x_1082_);
v___x_1096_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = l_Lean_indentExpr(v_expectedType_1080_);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = l_Lean_throwError___redArg(v_inst_1075_, v_inst_1076_, v___x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1101_, lean_object* v_inst_1102_, lean_object* v_inst_1103_, lean_object* v_00_u03b1_1104_, lean_object* v_attrName_1105_, lean_object* v_declName_1106_, lean_object* v_givenType_1107_, lean_object* v_expectedType_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1102_, v_inst_1103_, v_attrName_1105_, v_declName_1106_, v_givenType_1107_, v_expectedType_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1110_, uint8_t v_skipRealize_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; lean_object* v_env_1115_; uint8_t v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1114_ = lean_st_ref_get(v___y_1112_);
v_env_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc_ref(v_env_1115_);
lean_dec(v___x_1114_);
v___x_1116_ = l_Lean_Environment_contains(v_env_1115_, v_constName_1110_, v_skipRealize_1111_);
v___x_1117_ = lean_box(v___x_1116_);
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object* v_constName_1119_, lean_object* v_skipRealize_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
uint8_t v_skipRealize_boxed_1123_; lean_object* v_res_1124_; 
v_skipRealize_boxed_1123_ = lean_unbox(v_skipRealize_1120_);
v_res_1124_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1119_, v_skipRealize_boxed_1123_, v___y_1121_);
lean_dec(v___y_1121_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1125_, uint8_t v_skipRealize_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1125_, v_skipRealize_1126_, v___y_1128_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1131_, lean_object* v_skipRealize_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
uint8_t v_skipRealize_boxed_1136_; lean_object* v_res_1137_; 
v_skipRealize_boxed_1136_ = lean_unbox(v_skipRealize_1132_);
v_res_1137_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1131_, v_skipRealize_boxed_1136_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1138_, uint8_t v_isExporting_1139_, lean_object* v___x_1140_, lean_object* v_a_x3f_1141_){
_start:
{
lean_object* v___x_1143_; lean_object* v_env_1144_; lean_object* v_nextMacroScope_1145_; lean_object* v_ngen_1146_; lean_object* v_auxDeclNGen_1147_; lean_object* v_traceState_1148_; lean_object* v_recordedDeps_1149_; lean_object* v_messages_1150_; lean_object* v_infoState_1151_; lean_object* v_snapshotTasks_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1163_; 
v___x_1143_ = lean_st_ref_take(v___y_1138_);
v_env_1144_ = lean_ctor_get(v___x_1143_, 0);
v_nextMacroScope_1145_ = lean_ctor_get(v___x_1143_, 1);
v_ngen_1146_ = lean_ctor_get(v___x_1143_, 2);
v_auxDeclNGen_1147_ = lean_ctor_get(v___x_1143_, 3);
v_traceState_1148_ = lean_ctor_get(v___x_1143_, 4);
v_recordedDeps_1149_ = lean_ctor_get(v___x_1143_, 6);
v_messages_1150_ = lean_ctor_get(v___x_1143_, 7);
v_infoState_1151_ = lean_ctor_get(v___x_1143_, 8);
v_snapshotTasks_1152_ = lean_ctor_get(v___x_1143_, 9);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1163_ == 0)
{
lean_object* v_unused_1164_; 
v_unused_1164_ = lean_ctor_get(v___x_1143_, 5);
lean_dec(v_unused_1164_);
v___x_1154_ = v___x_1143_;
v_isShared_1155_ = v_isSharedCheck_1163_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_snapshotTasks_1152_);
lean_inc(v_infoState_1151_);
lean_inc(v_messages_1150_);
lean_inc(v_recordedDeps_1149_);
lean_inc(v_traceState_1148_);
lean_inc(v_auxDeclNGen_1147_);
lean_inc(v_ngen_1146_);
lean_inc(v_nextMacroScope_1145_);
lean_inc(v_env_1144_);
lean_dec(v___x_1143_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1163_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1156_ = lean_box(0);
v___x_1157_ = l_Lean_Environment_setExporting(v_env_1144_, v_isExporting_1139_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 5, v___x_1140_);
lean_ctor_set(v___x_1154_, 0, v___x_1157_);
v___x_1159_ = v___x_1154_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_nextMacroScope_1145_);
lean_ctor_set(v_reuseFailAlloc_1162_, 2, v_ngen_1146_);
lean_ctor_set(v_reuseFailAlloc_1162_, 3, v_auxDeclNGen_1147_);
lean_ctor_set(v_reuseFailAlloc_1162_, 4, v_traceState_1148_);
lean_ctor_set(v_reuseFailAlloc_1162_, 5, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1162_, 6, v_recordedDeps_1149_);
lean_ctor_set(v_reuseFailAlloc_1162_, 7, v_messages_1150_);
lean_ctor_set(v_reuseFailAlloc_1162_, 8, v_infoState_1151_);
lean_ctor_set(v_reuseFailAlloc_1162_, 9, v_snapshotTasks_1152_);
v___x_1159_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_st_ref_put(v___y_1138_, v___x_1159_);
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1156_);
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1165_, lean_object* v_isExporting_1166_, lean_object* v___x_1167_, lean_object* v_a_x3f_1168_, lean_object* v___y_1169_){
_start:
{
uint8_t v_isExporting_boxed_1170_; lean_object* v_res_1171_; 
v_isExporting_boxed_1170_ = lean_unbox(v_isExporting_1166_);
v_res_1171_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1165_, v_isExporting_boxed_1170_, v___x_1167_, v_a_x3f_1168_);
lean_dec(v_a_x3f_1168_);
lean_dec(v___y_1165_);
return v_res_1171_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0);
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
return v___x_1173_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1176_, uint8_t v_isExporting_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; lean_object* v_env_1182_; lean_object* v___x_1183_; uint8_t v_isModule_1184_; 
v___x_1181_ = lean_st_ref_get(v___y_1179_);
v_env_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc_ref(v_env_1182_);
lean_dec(v___x_1181_);
v___x_1183_ = l_Lean_Environment_header(v_env_1182_);
v_isModule_1184_ = lean_ctor_get_uint8(v___x_1183_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1183_);
if (v_isModule_1184_ == 0)
{
lean_object* v___x_1185_; 
lean_dec_ref(v_env_1182_);
lean_inc(v___y_1179_);
lean_inc_ref(v___y_1178_);
v___x_1185_ = lean_apply_3(v_x_1176_, v___y_1178_, v___y_1179_, lean_box(0));
return v___x_1185_;
}
else
{
uint8_t v_isExporting_1186_; 
v_isExporting_1186_ = lean_ctor_get_uint8(v_env_1182_, sizeof(void*)*13);
lean_dec_ref(v_env_1182_);
if (v_isExporting_1177_ == 0)
{
if (v_isExporting_1186_ == 0)
{
lean_object* v___x_1238_; 
lean_inc(v___y_1179_);
lean_inc_ref(v___y_1178_);
v___x_1238_ = lean_apply_3(v_x_1176_, v___y_1178_, v___y_1179_, lean_box(0));
return v___x_1238_;
}
else
{
goto v___jp_1187_;
}
}
else
{
if (v_isExporting_1186_ == 0)
{
goto v___jp_1187_;
}
else
{
lean_object* v___x_1239_; 
lean_inc(v___y_1179_);
lean_inc_ref(v___y_1178_);
v___x_1239_ = lean_apply_3(v_x_1176_, v___y_1178_, v___y_1179_, lean_box(0));
return v___x_1239_;
}
}
v___jp_1187_:
{
lean_object* v___x_1188_; lean_object* v_env_1189_; lean_object* v_nextMacroScope_1190_; lean_object* v_ngen_1191_; lean_object* v_auxDeclNGen_1192_; lean_object* v_traceState_1193_; lean_object* v_recordedDeps_1194_; lean_object* v_messages_1195_; lean_object* v_infoState_1196_; lean_object* v_snapshotTasks_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1236_; 
v___x_1188_ = lean_st_ref_take(v___y_1179_);
v_env_1189_ = lean_ctor_get(v___x_1188_, 0);
v_nextMacroScope_1190_ = lean_ctor_get(v___x_1188_, 1);
v_ngen_1191_ = lean_ctor_get(v___x_1188_, 2);
v_auxDeclNGen_1192_ = lean_ctor_get(v___x_1188_, 3);
v_traceState_1193_ = lean_ctor_get(v___x_1188_, 4);
v_recordedDeps_1194_ = lean_ctor_get(v___x_1188_, 6);
v_messages_1195_ = lean_ctor_get(v___x_1188_, 7);
v_infoState_1196_ = lean_ctor_get(v___x_1188_, 8);
v_snapshotTasks_1197_ = lean_ctor_get(v___x_1188_, 9);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; 
v_unused_1237_ = lean_ctor_get(v___x_1188_, 5);
lean_dec(v_unused_1237_);
v___x_1199_ = v___x_1188_;
v_isShared_1200_ = v_isSharedCheck_1236_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_snapshotTasks_1197_);
lean_inc(v_infoState_1196_);
lean_inc(v_messages_1195_);
lean_inc(v_recordedDeps_1194_);
lean_inc(v_traceState_1193_);
lean_inc(v_auxDeclNGen_1192_);
lean_inc(v_ngen_1191_);
lean_inc(v_nextMacroScope_1190_);
lean_inc(v_env_1189_);
lean_dec(v___x_1188_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1236_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1201_ = l_Lean_Environment_setExporting(v_env_1189_, v_isExporting_1177_);
v___x_1202_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 5, v___x_1202_);
lean_ctor_set(v___x_1199_, 0, v___x_1201_);
v___x_1204_ = v___x_1199_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_nextMacroScope_1190_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v_ngen_1191_);
lean_ctor_set(v_reuseFailAlloc_1235_, 3, v_auxDeclNGen_1192_);
lean_ctor_set(v_reuseFailAlloc_1235_, 4, v_traceState_1193_);
lean_ctor_set(v_reuseFailAlloc_1235_, 5, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1235_, 6, v_recordedDeps_1194_);
lean_ctor_set(v_reuseFailAlloc_1235_, 7, v_messages_1195_);
lean_ctor_set(v_reuseFailAlloc_1235_, 8, v_infoState_1196_);
lean_ctor_set(v_reuseFailAlloc_1235_, 9, v_snapshotTasks_1197_);
v___x_1204_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1205_; lean_object* v_r_1206_; 
v___x_1205_ = lean_st_ref_put(v___y_1179_, v___x_1204_);
lean_inc(v___y_1179_);
lean_inc_ref(v___y_1178_);
v_r_1206_ = lean_apply_3(v_x_1176_, v___y_1178_, v___y_1179_, lean_box(0));
if (lean_obj_tag(v_r_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1223_; 
v_a_1207_ = lean_ctor_get(v_r_1206_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_r_1206_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1209_ = v_r_1206_;
v_isShared_1210_ = v_isSharedCheck_1223_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v_r_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1223_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
lean_inc(v_a_1207_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set_tag(v___x_1209_, 1);
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
v___x_1213_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1179_, v_isExporting_1186_, v___x_1202_, v___x_1212_);
lean_dec_ref(v___x_1212_);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v___x_1213_, 0);
lean_dec(v_unused_1221_);
v___x_1215_ = v___x_1213_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_dec(v___x_1213_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v_a_1207_);
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1207_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
v_a_1224_ = lean_ctor_get(v_r_1206_, 0);
lean_inc(v_a_1224_);
lean_dec_ref_known(v_r_1206_, 1);
v___x_1225_ = lean_box(0);
v___x_1226_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1179_, v_isExporting_1186_, v___x_1202_, v___x_1225_);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; 
v_unused_1234_ = lean_ctor_get(v___x_1226_, 0);
lean_dec(v_unused_1234_);
v___x_1228_ = v___x_1226_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_dec(v___x_1226_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set_tag(v___x_1228_, 1);
lean_ctor_set(v___x_1228_, 0, v_a_1224_);
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1224_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1240_, lean_object* v_isExporting_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
uint8_t v_isExporting_boxed_1245_; lean_object* v_res_1246_; 
v_isExporting_boxed_1245_ = lean_unbox(v_isExporting_1241_);
v_res_1246_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1240_, v_isExporting_boxed_1245_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1247_, lean_object* v_x_1248_, uint8_t v_isExporting_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1248_, v_isExporting_1249_, v___y_1250_, v___y_1251_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1254_, lean_object* v_x_1255_, lean_object* v_isExporting_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
uint8_t v_isExporting_boxed_1260_; lean_object* v_res_1261_; 
v_isExporting_boxed_1260_ = lean_unbox(v_isExporting_1256_);
v_res_1261_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1254_, v_x_1255_, v_isExporting_boxed_1260_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
return v_res_1261_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1262_, lean_object* v_opt_1263_){
_start:
{
lean_object* v_name_1264_; lean_object* v_defValue_1265_; lean_object* v_map_1266_; lean_object* v___x_1267_; 
v_name_1264_ = lean_ctor_get(v_opt_1263_, 0);
v_defValue_1265_ = lean_ctor_get(v_opt_1263_, 1);
v_map_1266_ = lean_ctor_get(v_opts_1262_, 0);
v___x_1267_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1266_, v_name_1264_);
if (lean_obj_tag(v___x_1267_) == 0)
{
uint8_t v___x_1268_; 
v___x_1268_ = lean_unbox(v_defValue_1265_);
return v___x_1268_;
}
else
{
lean_object* v_val_1269_; 
v_val_1269_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_val_1269_);
lean_dec_ref_known(v___x_1267_, 1);
if (lean_obj_tag(v_val_1269_) == 1)
{
uint8_t v_v_1270_; 
v_v_1270_ = lean_ctor_get_uint8(v_val_1269_, 0);
lean_dec_ref_known(v_val_1269_, 0);
return v_v_1270_;
}
else
{
uint8_t v___x_1271_; 
lean_dec(v_val_1269_);
v___x_1271_ = lean_unbox(v_defValue_1265_);
return v___x_1271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1272_, lean_object* v_opt_1273_){
_start:
{
uint8_t v_res_1274_; lean_object* v_r_1275_; 
v_res_1274_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1272_, v_opt_1273_);
lean_dec_ref(v_opt_1273_);
lean_dec_ref(v_opts_1272_);
v_r_1275_ = lean_box(v_res_1274_);
return v_r_1275_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_1283_, lean_object* v_x_1284_){
_start:
{
if (lean_obj_tag(v_x_1284_) == 1)
{
lean_object* v_pre_1285_; 
v_pre_1285_ = lean_ctor_get(v_x_1284_, 0);
switch(lean_obj_tag(v_pre_1285_))
{
case 1:
{
lean_object* v_pre_1286_; 
v_pre_1286_ = lean_ctor_get(v_pre_1285_, 0);
switch(lean_obj_tag(v_pre_1286_))
{
case 0:
{
lean_object* v_str_1287_; lean_object* v_str_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v_str_1287_ = lean_ctor_get(v_x_1284_, 1);
v_str_1288_ = lean_ctor_get(v_pre_1285_, 1);
v___x_1289_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1290_ = lean_string_dec_eq(v_str_1288_, v___x_1289_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1291_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1292_ = lean_string_dec_eq(v_str_1288_, v___x_1291_);
if (v___x_1292_ == 0)
{
return v___x_1292_;
}
else
{
lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1293_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1294_ = lean_string_dec_eq(v_str_1287_, v___x_1293_);
if (v___x_1294_ == 0)
{
return v___x_1294_;
}
else
{
return v_suppressElabErrors_1283_;
}
}
}
else
{
lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1296_ = lean_string_dec_eq(v_str_1287_, v___x_1295_);
if (v___x_1296_ == 0)
{
return v___x_1296_;
}
else
{
return v_suppressElabErrors_1283_;
}
}
}
case 1:
{
lean_object* v_pre_1297_; 
v_pre_1297_ = lean_ctor_get(v_pre_1286_, 0);
if (lean_obj_tag(v_pre_1297_) == 0)
{
lean_object* v_str_1298_; lean_object* v_str_1299_; lean_object* v_str_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v_str_1298_ = lean_ctor_get(v_x_1284_, 1);
v_str_1299_ = lean_ctor_get(v_pre_1285_, 1);
v_str_1300_ = lean_ctor_get(v_pre_1286_, 1);
v___x_1301_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1302_ = lean_string_dec_eq(v_str_1300_, v___x_1301_);
if (v___x_1302_ == 0)
{
return v___x_1302_;
}
else
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1304_ = lean_string_dec_eq(v_str_1299_, v___x_1303_);
if (v___x_1304_ == 0)
{
return v___x_1304_;
}
else
{
lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1305_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1306_ = lean_string_dec_eq(v_str_1298_, v___x_1305_);
if (v___x_1306_ == 0)
{
return v___x_1306_;
}
else
{
return v_suppressElabErrors_1283_;
}
}
}
}
else
{
uint8_t v___x_1307_; 
v___x_1307_ = 0;
return v___x_1307_;
}
}
default: 
{
uint8_t v___x_1308_; 
v___x_1308_ = 0;
return v___x_1308_;
}
}
}
case 0:
{
lean_object* v_str_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v_str_1309_ = lean_ctor_get(v_x_1284_, 1);
v___x_1310_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1311_ = lean_string_dec_eq(v_str_1309_, v___x_1310_);
if (v___x_1311_ == 0)
{
return v___x_1311_;
}
else
{
return v_suppressElabErrors_1283_;
}
}
default: 
{
uint8_t v___x_1312_; 
v___x_1312_ = 0;
return v___x_1312_;
}
}
}
else
{
uint8_t v___x_1313_; 
v___x_1313_ = 0;
return v___x_1313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_1314_, lean_object* v_x_1315_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1316_; uint8_t v_res_1317_; lean_object* v_r_1318_; 
v_suppressElabErrors_boxed_1316_ = lean_unbox(v_suppressElabErrors_1314_);
v_res_1317_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_1316_, v_x_1315_);
lean_dec(v_x_1315_);
v_r_1318_ = lean_box(v_res_1317_);
return v_r_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1319_, lean_object* v_msgData_1320_, uint8_t v_severity_1321_, uint8_t v_isSilent_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___y_1327_; lean_object* v___y_1328_; uint8_t v___y_1329_; uint8_t v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v_toCold_1334_; lean_object* v___y_1335_; lean_object* v___y_1364_; lean_object* v___y_1365_; uint8_t v___y_1366_; lean_object* v___y_1367_; uint8_t v___y_1368_; uint8_t v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1391_; lean_object* v___y_1392_; uint8_t v___y_1393_; uint8_t v___y_1394_; uint8_t v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; uint8_t v___y_1401_; uint8_t v___y_1402_; uint8_t v___x_1412_; uint8_t v___y_1414_; uint8_t v___x_1420_; 
v___x_1412_ = 2;
v___x_1420_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1321_, v___x_1412_);
if (v___x_1420_ == 0)
{
v___y_1414_ = v___x_1420_;
goto v___jp_1413_;
}
else
{
uint8_t v___x_1421_; 
lean_inc_ref(v_msgData_1320_);
v___x_1421_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1320_);
if (v___x_1421_ == 0)
{
v___y_1414_ = v___x_1421_;
goto v___jp_1413_;
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_dec_ref(v_msgData_1320_);
v___x_1422_ = lean_box(0);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
return v___x_1423_;
}
}
v___jp_1326_:
{
lean_object* v_currNamespace_1336_; lean_object* v_openDecls_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v_env_1342_; lean_object* v_nextMacroScope_1343_; lean_object* v_ngen_1344_; lean_object* v_auxDeclNGen_1345_; lean_object* v_traceState_1346_; lean_object* v_cache_1347_; lean_object* v_recordedDeps_1348_; lean_object* v_messages_1349_; lean_object* v_infoState_1350_; lean_object* v_snapshotTasks_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1362_; 
v_currNamespace_1336_ = lean_ctor_get(v_toCold_1334_, 4);
v_openDecls_1337_ = lean_ctor_get(v_toCold_1334_, 5);
lean_inc(v_openDecls_1337_);
lean_inc(v_currNamespace_1336_);
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v_currNamespace_1336_);
lean_ctor_set(v___x_1338_, 1, v_openDecls_1337_);
v___x_1339_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
lean_ctor_set(v___x_1339_, 1, v___y_1332_);
lean_inc_ref(v___y_1327_);
lean_inc_ref(v___y_1333_);
v___x_1340_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1340_, 0, v___y_1333_);
lean_ctor_set(v___x_1340_, 1, v___y_1328_);
lean_ctor_set(v___x_1340_, 2, v___y_1331_);
lean_ctor_set(v___x_1340_, 3, v___y_1327_);
lean_ctor_set(v___x_1340_, 4, v___x_1339_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*5, v___y_1330_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*5 + 1, v___y_1329_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*5 + 2, v_isSilent_1322_);
v___x_1341_ = lean_st_ref_take(v___y_1335_);
v_env_1342_ = lean_ctor_get(v___x_1341_, 0);
v_nextMacroScope_1343_ = lean_ctor_get(v___x_1341_, 1);
v_ngen_1344_ = lean_ctor_get(v___x_1341_, 2);
v_auxDeclNGen_1345_ = lean_ctor_get(v___x_1341_, 3);
v_traceState_1346_ = lean_ctor_get(v___x_1341_, 4);
v_cache_1347_ = lean_ctor_get(v___x_1341_, 5);
v_recordedDeps_1348_ = lean_ctor_get(v___x_1341_, 6);
v_messages_1349_ = lean_ctor_get(v___x_1341_, 7);
v_infoState_1350_ = lean_ctor_get(v___x_1341_, 8);
v_snapshotTasks_1351_ = lean_ctor_get(v___x_1341_, 9);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1353_ = v___x_1341_;
v_isShared_1354_ = v_isSharedCheck_1362_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_snapshotTasks_1351_);
lean_inc(v_infoState_1350_);
lean_inc(v_messages_1349_);
lean_inc(v_recordedDeps_1348_);
lean_inc(v_cache_1347_);
lean_inc(v_traceState_1346_);
lean_inc(v_auxDeclNGen_1345_);
lean_inc(v_ngen_1344_);
lean_inc(v_nextMacroScope_1343_);
lean_inc(v_env_1342_);
lean_dec(v___x_1341_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1362_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1355_ = lean_box(0);
v___x_1356_ = l_Lean_MessageLog_add(v___x_1340_, v_messages_1349_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 7, v___x_1356_);
v___x_1358_ = v___x_1353_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_env_1342_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_nextMacroScope_1343_);
lean_ctor_set(v_reuseFailAlloc_1361_, 2, v_ngen_1344_);
lean_ctor_set(v_reuseFailAlloc_1361_, 3, v_auxDeclNGen_1345_);
lean_ctor_set(v_reuseFailAlloc_1361_, 4, v_traceState_1346_);
lean_ctor_set(v_reuseFailAlloc_1361_, 5, v_cache_1347_);
lean_ctor_set(v_reuseFailAlloc_1361_, 6, v_recordedDeps_1348_);
lean_ctor_set(v_reuseFailAlloc_1361_, 7, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1361_, 8, v_infoState_1350_);
lean_ctor_set(v_reuseFailAlloc_1361_, 9, v_snapshotTasks_1351_);
v___x_1358_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = lean_st_ref_put(v___y_1335_, v___x_1358_);
v___x_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1355_);
return v___x_1360_;
}
}
}
v___jp_1363_:
{
lean_object* v_fileName_1372_; lean_object* v_fileMap_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1389_; 
v_fileName_1372_ = lean_ctor_get(v___y_1367_, 0);
v_fileMap_1373_ = lean_ctor_get(v___y_1367_, 1);
v___x_1374_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1320_);
v___x_1375_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v___x_1374_, v___y_1323_, v___y_1324_);
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1389_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1389_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_inc_ref_n(v_fileMap_1373_, 2);
v___x_1380_ = l_Lean_FileMap_toPosition(v_fileMap_1373_, v___y_1370_);
lean_dec(v___y_1370_);
v___x_1381_ = l_Lean_FileMap_toPosition(v_fileMap_1373_, v___y_1371_);
lean_dec(v___y_1371_);
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
v___x_1383_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1366_ == 0)
{
lean_del_object(v___x_1378_);
lean_dec_ref(v___y_1364_);
v___y_1327_ = v___x_1383_;
v___y_1328_ = v___x_1380_;
v___y_1329_ = v___y_1369_;
v___y_1330_ = v___y_1368_;
v___y_1331_ = v___x_1382_;
v___y_1332_ = v_a_1376_;
v___y_1333_ = v_fileName_1372_;
v_toCold_1334_ = v___y_1365_;
v___y_1335_ = v___y_1324_;
goto v___jp_1326_;
}
else
{
uint8_t v___x_1384_; 
lean_inc(v_a_1376_);
v___x_1384_ = l_Lean_MessageData_hasTag(v___y_1364_, v_a_1376_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
lean_dec_ref_known(v___x_1382_, 1);
lean_dec_ref(v___x_1380_);
lean_dec(v_a_1376_);
v___x_1385_ = lean_box(0);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1385_);
v___x_1387_ = v___x_1378_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
else
{
lean_del_object(v___x_1378_);
v___y_1327_ = v___x_1383_;
v___y_1328_ = v___x_1380_;
v___y_1329_ = v___y_1369_;
v___y_1330_ = v___y_1368_;
v___y_1331_ = v___x_1382_;
v___y_1332_ = v_a_1376_;
v___y_1333_ = v_fileName_1372_;
v_toCold_1334_ = v___y_1365_;
v___y_1335_ = v___y_1324_;
goto v___jp_1326_;
}
}
}
}
v___jp_1390_:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_Syntax_getTailPos_x3f(v___y_1396_, v___y_1395_);
lean_dec(v___y_1396_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_inc(v___y_1397_);
v___y_1364_ = v___y_1391_;
v___y_1365_ = v___y_1392_;
v___y_1366_ = v___y_1393_;
v___y_1367_ = v___y_1392_;
v___y_1368_ = v___y_1395_;
v___y_1369_ = v___y_1394_;
v___y_1370_ = v___y_1397_;
v___y_1371_ = v___y_1397_;
goto v___jp_1363_;
}
else
{
lean_object* v_val_1399_; 
v_val_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_val_1399_);
lean_dec_ref_known(v___x_1398_, 1);
v___y_1364_ = v___y_1391_;
v___y_1365_ = v___y_1392_;
v___y_1366_ = v___y_1393_;
v___y_1367_ = v___y_1392_;
v___y_1368_ = v___y_1395_;
v___y_1369_ = v___y_1394_;
v___y_1370_ = v___y_1397_;
v___y_1371_ = v_val_1399_;
goto v___jp_1363_;
}
}
v___jp_1400_:
{
lean_object* v_toCold_1403_; lean_object* v_ref_1404_; uint8_t v_suppressElabErrors_1405_; lean_object* v___x_1406_; lean_object* v___f_1407_; lean_object* v_ref_1408_; lean_object* v___x_1409_; 
v_toCold_1403_ = lean_ctor_get(v___y_1323_, 0);
v_ref_1404_ = lean_ctor_get(v___y_1323_, 2);
v_suppressElabErrors_1405_ = lean_ctor_get_uint8(v___y_1323_, sizeof(void*)*3 + 2);
v___x_1406_ = lean_box(v_suppressElabErrors_1405_);
v___f_1407_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1407_, 0, v___x_1406_);
v_ref_1408_ = l_Lean_replaceRef(v_ref_1319_, v_ref_1404_);
v___x_1409_ = l_Lean_Syntax_getPos_x3f(v_ref_1408_, v___y_1401_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v___x_1410_; 
v___x_1410_ = lean_unsigned_to_nat(0u);
v___y_1391_ = v___f_1407_;
v___y_1392_ = v_toCold_1403_;
v___y_1393_ = v_suppressElabErrors_1405_;
v___y_1394_ = v___y_1402_;
v___y_1395_ = v___y_1401_;
v___y_1396_ = v_ref_1408_;
v___y_1397_ = v___x_1410_;
goto v___jp_1390_;
}
else
{
lean_object* v_val_1411_; 
v_val_1411_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_val_1411_);
lean_dec_ref_known(v___x_1409_, 1);
v___y_1391_ = v___f_1407_;
v___y_1392_ = v_toCold_1403_;
v___y_1393_ = v_suppressElabErrors_1405_;
v___y_1394_ = v___y_1402_;
v___y_1395_ = v___y_1401_;
v___y_1396_ = v_ref_1408_;
v___y_1397_ = v_val_1411_;
goto v___jp_1390_;
}
}
v___jp_1413_:
{
uint8_t v___x_1415_; uint8_t v___x_1416_; 
v___x_1415_ = 1;
v___x_1416_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1321_, v___x_1415_);
if (v___x_1416_ == 0)
{
v___y_1401_ = v___y_1414_;
v___y_1402_ = v_severity_1321_;
goto v___jp_1400_;
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1417_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1323_);
v___x_1418_ = l_Lean_warningAsError;
v___x_1419_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v___x_1417_, v___x_1418_);
lean_dec_ref(v___x_1417_);
if (v___x_1419_ == 0)
{
v___y_1401_ = v___y_1414_;
v___y_1402_ = v_severity_1321_;
goto v___jp_1400_;
}
else
{
v___y_1401_ = v___y_1414_;
v___y_1402_ = v___x_1412_;
goto v___jp_1400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1424_, lean_object* v_msgData_1425_, lean_object* v_severity_1426_, lean_object* v_isSilent_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
uint8_t v_severity_boxed_1431_; uint8_t v_isSilent_boxed_1432_; lean_object* v_res_1433_; 
v_severity_boxed_1431_ = lean_unbox(v_severity_1426_);
v_isSilent_boxed_1432_ = lean_unbox(v_isSilent_1427_);
v_res_1433_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1424_, v_msgData_1425_, v_severity_boxed_1431_, v_isSilent_boxed_1432_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v_ref_1424_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1434_, uint8_t v_severity_1435_, uint8_t v_isSilent_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_ref_1440_; lean_object* v___x_1441_; 
v_ref_1440_ = lean_ctor_get(v___y_1437_, 2);
v___x_1441_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1440_, v_msgData_1434_, v_severity_1435_, v_isSilent_1436_, v___y_1437_, v___y_1438_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1442_, lean_object* v_severity_1443_, lean_object* v_isSilent_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
uint8_t v_severity_boxed_1448_; uint8_t v_isSilent_boxed_1449_; lean_object* v_res_1450_; 
v_severity_boxed_1448_ = lean_unbox(v_severity_1443_);
v_isSilent_boxed_1449_ = lean_unbox(v_isSilent_1444_);
v_res_1450_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1442_, v_severity_boxed_1448_, v_isSilent_boxed_1449_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
uint8_t v___x_1455_; uint8_t v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = 1;
v___x_1456_ = 0;
v___x_1457_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1451_, v___x_1455_, v___x_1456_, v___y_1452_, v___y_1453_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1458_, v___y_1459_, v___y_1460_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___x_1466_; uint8_t v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1466_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1464_);
v___x_1467_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v___x_1466_, v_opt_1463_);
lean_dec_ref(v___x_1466_);
v___x_1468_ = lean_box(v___x_1467_);
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1470_, v___y_1471_);
lean_dec_ref(v___y_1471_);
lean_dec_ref(v_opt_1470_);
return v_res_1473_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1476_ = l_Lean_stringToMessageData(v___x_1475_);
return v___x_1476_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1479_ = l_Lean_stringToMessageData(v___x_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___x_1484_; lean_object* v_env_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1507_; 
v___x_1484_ = lean_st_ref_get(v___y_1482_);
v_env_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc_ref(v_env_1485_);
lean_dec(v___x_1484_);
v___x_1486_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1487_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1486_, v___y_1481_);
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1490_ = v___x_1487_;
v_isShared_1491_ = v_isSharedCheck_1507_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1487_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1507_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
uint8_t v_isExporting_1497_; 
v_isExporting_1497_ = lean_ctor_get_uint8(v_env_1485_, sizeof(void*)*13);
lean_dec_ref(v_env_1485_);
if (v_isExporting_1497_ == 0)
{
lean_dec(v_a_1488_);
lean_dec(v_id_1480_);
goto v___jp_1492_;
}
else
{
uint8_t v___x_1498_; 
v___x_1498_ = l_Lean_isPrivateName(v_id_1480_);
if (v___x_1498_ == 0)
{
lean_dec(v_a_1488_);
lean_dec(v_id_1480_);
goto v___jp_1492_;
}
else
{
uint8_t v___x_1499_; 
v___x_1499_ = lean_unbox(v_a_1488_);
lean_dec(v_a_1488_);
if (v___x_1499_ == 0)
{
lean_dec(v_id_1480_);
goto v___jp_1492_;
}
else
{
lean_object* v___x_1500_; uint8_t v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_del_object(v___x_1490_);
v___x_1500_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1501_ = 0;
v___x_1502_ = l_Lean_MessageData_ofConstName(v_id_1480_, v___x_1501_);
v___x_1503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1500_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v___x_1504_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1503_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
v___x_1506_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1505_, v___y_1481_, v___y_1482_);
return v___x_1506_;
}
}
}
v___jp_1492_:
{
lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1493_ = lean_box(0);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v___x_1493_);
v___x_1495_ = v___x_1490_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1508_, v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
return v_res_1512_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1515_ = l_Lean_stringToMessageData(v___x_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1516_, uint8_t v_isModule_1517_, lean_object* v_attrName_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___x_1522_; 
lean_inc(v_declName_1516_);
v___x_1522_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1516_, v___y_1519_, v___y_1520_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v___x_1523_; lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1544_; 
lean_dec_ref_known(v___x_1522_, 1);
lean_inc(v_declName_1516_);
v___x_1523_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1516_, v_isModule_1517_, v___y_1520_);
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1526_ = v___x_1523_;
v_isShared_1527_ = v_isSharedCheck_1544_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1523_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1544_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
uint8_t v___x_1528_; 
v___x_1528_ = lean_unbox(v_a_1524_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
lean_del_object(v___x_1526_);
v___x_1529_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1530_ = l_Lean_MessageData_ofName(v_attrName_1518_);
v___x_1531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = lean_unbox(v_a_1524_);
lean_dec(v_a_1524_);
v___x_1535_ = l_Lean_MessageData_ofConstName(v_declName_1516_, v___x_1534_);
v___x_1536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1533_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1538_, v___y_1519_, v___y_1520_);
return v___x_1539_;
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1542_; 
lean_dec(v_a_1524_);
lean_dec(v_attrName_1518_);
lean_dec(v_declName_1516_);
v___x_1540_ = lean_box(0);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1540_);
v___x_1542_ = v___x_1526_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
else
{
lean_dec(v_attrName_1518_);
lean_dec(v_declName_1516_);
return v___x_1522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1545_, lean_object* v_isModule_1546_, lean_object* v_attrName_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
uint8_t v_isModule_boxed_1551_; lean_object* v_res_1552_; 
v_isModule_boxed_1551_ = lean_unbox(v_isModule_1546_);
v_res_1552_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1545_, v_isModule_boxed_1551_, v_attrName_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1553_, lean_object* v_declName_1554_, uint8_t v_attrKind_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v___x_1559_; lean_object* v_env_1563_; lean_object* v___x_1564_; uint8_t v_isModule_1565_; 
v___x_1559_ = lean_st_ref_get(v_a_1557_);
v_env_1563_ = lean_ctor_get(v___x_1559_, 0);
lean_inc_ref(v_env_1563_);
lean_dec(v___x_1559_);
v___x_1564_ = l_Lean_Environment_header(v_env_1563_);
lean_dec_ref(v_env_1563_);
v_isModule_1565_ = lean_ctor_get_uint8(v___x_1564_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1564_);
if (v_isModule_1565_ == 0)
{
lean_dec(v_declName_1554_);
lean_dec(v_attrName_1553_);
goto v___jp_1560_;
}
else
{
uint8_t v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = 1;
v___x_1567_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1555_, v___x_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; lean_object* v___f_1569_; lean_object* v___x_1570_; 
v___x_1568_ = lean_box(v_isModule_1565_);
v___f_1569_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1569_, 0, v_declName_1554_);
lean_closure_set(v___f_1569_, 1, v___x_1568_);
lean_closure_set(v___f_1569_, 2, v_attrName_1553_);
v___x_1570_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1569_, v_isModule_1565_, v_a_1556_, v_a_1557_);
return v___x_1570_;
}
else
{
lean_dec(v_declName_1554_);
lean_dec(v_attrName_1553_);
goto v___jp_1560_;
}
}
v___jp_1560_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_box(0);
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
return v___x_1562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1571_, lean_object* v_declName_1572_, lean_object* v_attrKind_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_){
_start:
{
uint8_t v_attrKind_boxed_1577_; lean_object* v_res_1578_; 
v_attrKind_boxed_1577_ = lean_unbox(v_attrKind_1573_);
v_res_1578_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1571_, v_declName_1572_, v_attrKind_boxed_1577_, v_a_1574_, v_a_1575_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1579_, v___y_1580_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v_opt_1584_);
return v_res_1588_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1591_ = l_Lean_stringToMessageData(v___x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1592_, lean_object* v_declName_1593_, uint8_t v_attrKind_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v___x_1598_; lean_object* v_env_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v_isModule_1602_; 
v___x_1598_ = lean_st_ref_get(v_a_1596_);
v_env_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc_ref(v_env_1599_);
lean_dec(v___x_1598_);
v___x_1600_ = lean_st_ref_get(v_a_1596_);
v___x_1601_ = l_Lean_Environment_header(v_env_1599_);
lean_dec_ref(v_env_1599_);
v_isModule_1602_ = lean_ctor_get_uint8(v___x_1601_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1601_);
if (v_isModule_1602_ == 0)
{
lean_object* v___x_1603_; 
lean_dec(v___x_1600_);
v___x_1603_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1592_, v_declName_1593_, v_attrKind_1594_, v_a_1595_, v_a_1596_);
return v___x_1603_;
}
else
{
lean_object* v_env_1604_; uint8_t v___x_1605_; 
v_env_1604_ = lean_ctor_get(v___x_1600_, 0);
lean_inc_ref(v_env_1604_);
lean_dec(v___x_1600_);
lean_inc(v_declName_1593_);
v___x_1605_ = l_Lean_isMarkedMeta(v_env_1604_, v_declName_1593_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1606_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1607_ = l_Lean_MessageData_ofName(v_attrName_1592_);
v___x_1608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1608_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = l_Lean_MessageData_ofConstName(v_declName_1593_, v___x_1605_);
v___x_1612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1614_, v_a_1595_, v_a_1596_);
return v___x_1615_;
}
else
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1592_, v_declName_1593_, v_attrKind_1594_, v_a_1595_, v_a_1596_);
return v___x_1616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1617_, lean_object* v_declName_1618_, lean_object* v_attrKind_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
uint8_t v_attrKind_boxed_1623_; lean_object* v_res_1624_; 
v_attrKind_boxed_1623_ = lean_unbox(v_attrKind_1619_);
v_res_1624_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1617_, v_declName_1618_, v_attrKind_boxed_1623_, v_a_1620_, v_a_1621_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1633_, v___y_1634_);
lean_dec_ref(v___y_1634_);
lean_dec_ref(v_x_1633_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1637_, lean_object* v_x_1638_){
_start:
{
lean_inc(v_s_1637_);
return v_s_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1639_, lean_object* v_x_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1639_, v_x_1640_);
lean_dec(v_x_1640_);
lean_dec(v_s_1639_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1646_, lean_object* v_x_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1649_, lean_object* v_x_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1649_, v_x_1650_);
lean_dec(v_x_1650_);
lean_dec_ref(v_x_1649_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_box(0);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1654_);
lean_dec(v_x_1654_);
return v_res_1655_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_1660_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1661_; lean_object* v___f_1662_; lean_object* v___f_1663_; lean_object* v___f_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___f_1661_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1662_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1663_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1664_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1665_ = lean_box(0);
v___x_1666_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1667_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
lean_ctor_set(v___x_1667_, 1, v___x_1665_);
lean_ctor_set(v___x_1667_, 2, v___f_1664_);
lean_ctor_set(v___x_1667_, 3, v___f_1663_);
lean_ctor_set(v___x_1667_, 4, v___f_1662_);
lean_ctor_set(v___x_1667_, 5, v___f_1661_);
return v___x_1667_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1668_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1669_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
lean_ctor_set(v___x_1670_, 1, v___x_1668_);
return v___x_1670_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1671_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1672_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1674_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_registerTagAttribute___lam__0(v_x_1676_);
lean_dec(v_x_1676_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1678_, lean_object* v_x_1679_, lean_object* v_x_1680_){
_start:
{
if (lean_obj_tag(v_x_1680_) == 0)
{
return v_x_1679_;
}
else
{
lean_object* v_head_1681_; lean_object* v_tail_1682_; uint8_t v___x_1683_; 
v_head_1681_ = lean_ctor_get(v_x_1680_, 0);
lean_inc(v_head_1681_);
v_tail_1682_ = lean_ctor_get(v_x_1680_, 1);
lean_inc(v_tail_1682_);
lean_dec_ref_known(v_x_1680_, 2);
v___x_1683_ = l_Lean_NameSet_contains(v_newState_1678_, v_head_1681_);
if (v___x_1683_ == 0)
{
lean_dec(v_head_1681_);
v_x_1680_ = v_tail_1682_;
goto _start;
}
else
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_NameSet_insert(v_x_1679_, v_head_1681_);
v_x_1679_ = v___x_1685_;
v_x_1680_ = v_tail_1682_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1687_, lean_object* v_x_1688_, lean_object* v_x_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1687_, v_x_1688_, v_x_1689_);
lean_dec(v_newState_1687_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1691_, lean_object* v_newState_1692_, lean_object* v_newConsts_1693_, lean_object* v_s_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1692_, v_s_1694_, v_newConsts_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1696_, lean_object* v_newState_1697_, lean_object* v_newConsts_1698_, lean_object* v_s_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_registerTagAttribute___lam__1(v_x_1696_, v_newState_1697_, v_newConsts_1698_, v_s_1699_);
lean_dec(v_newState_1697_);
lean_dec(v_x_1696_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1713_){
_start:
{
lean_object* v___x_1714_; lean_object* v___y_1716_; 
v___x_1714_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1713_) == 0)
{
lean_object* v_size_1720_; 
v_size_1720_ = lean_ctor_get(v_s_1713_, 0);
lean_inc(v_size_1720_);
lean_dec_ref_known(v_s_1713_, 5);
v___y_1716_ = v_size_1720_;
goto v___jp_1715_;
}
else
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_unsigned_to_nat(0u);
v___y_1716_ = v___x_1721_;
goto v___jp_1715_;
}
v___jp_1715_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = l_Nat_reprFast(v___y_1716_);
v___x_1718_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
v___x_1719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1714_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
return v___x_1719_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1722_, lean_object* v_pivot_1723_, lean_object* v_as_1724_, lean_object* v_i_1725_, lean_object* v_k_1726_){
_start:
{
uint8_t v___x_1727_; 
v___x_1727_ = lean_nat_dec_lt(v_k_1726_, v_hi_1722_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_dec(v_k_1726_);
v___x_1728_ = lean_array_fswap(v_as_1724_, v_i_1725_, v_hi_1722_);
v___x_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1729_, 0, v_i_1725_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
return v___x_1729_;
}
else
{
lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1730_ = lean_array_fget_borrowed(v_as_1724_, v_k_1726_);
v___x_1731_ = l_Lean_Name_quickLt(v___x_1730_, v_pivot_1723_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = lean_unsigned_to_nat(1u);
v___x_1733_ = lean_nat_add(v_k_1726_, v___x_1732_);
lean_dec(v_k_1726_);
v_k_1726_ = v___x_1733_;
goto _start;
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1735_ = lean_array_fswap(v_as_1724_, v_i_1725_, v_k_1726_);
v___x_1736_ = lean_unsigned_to_nat(1u);
v___x_1737_ = lean_nat_add(v_i_1725_, v___x_1736_);
lean_dec(v_i_1725_);
v___x_1738_ = lean_nat_add(v_k_1726_, v___x_1736_);
lean_dec(v_k_1726_);
v_as_1724_ = v___x_1735_;
v_i_1725_ = v___x_1737_;
v_k_1726_ = v___x_1738_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1740_, lean_object* v_pivot_1741_, lean_object* v_as_1742_, lean_object* v_i_1743_, lean_object* v_k_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1740_, v_pivot_1741_, v_as_1742_, v_i_1743_, v_k_1744_);
lean_dec(v_pivot_1741_);
lean_dec(v_hi_1740_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1746_, lean_object* v_as_1747_, lean_object* v_lo_1748_, lean_object* v_hi_1749_){
_start:
{
lean_object* v___y_1751_; uint8_t v___x_1761_; 
v___x_1761_ = lean_nat_dec_lt(v_lo_1748_, v_hi_1749_);
if (v___x_1761_ == 0)
{
lean_dec(v_lo_1748_);
return v_as_1747_;
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v_mid_1764_; lean_object* v___y_1766_; lean_object* v___y_1772_; lean_object* v___x_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1762_ = lean_nat_add(v_lo_1748_, v_hi_1749_);
v___x_1763_ = lean_unsigned_to_nat(1u);
v_mid_1764_ = lean_nat_shiftr(v___x_1762_, v___x_1763_);
lean_dec(v___x_1762_);
v___x_1777_ = lean_array_fget_borrowed(v_as_1747_, v_mid_1764_);
v___x_1778_ = lean_array_fget_borrowed(v_as_1747_, v_lo_1748_);
v___x_1779_ = l_Lean_Name_quickLt(v___x_1777_, v___x_1778_);
if (v___x_1779_ == 0)
{
v___y_1772_ = v_as_1747_;
goto v___jp_1771_;
}
else
{
lean_object* v___x_1780_; 
v___x_1780_ = lean_array_fswap(v_as_1747_, v_lo_1748_, v_mid_1764_);
v___y_1772_ = v___x_1780_;
goto v___jp_1771_;
}
v___jp_1765_:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1767_ = lean_array_fget_borrowed(v___y_1766_, v_mid_1764_);
v___x_1768_ = lean_array_fget_borrowed(v___y_1766_, v_hi_1749_);
v___x_1769_ = l_Lean_Name_quickLt(v___x_1767_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_dec(v_mid_1764_);
v___y_1751_ = v___y_1766_;
goto v___jp_1750_;
}
else
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_array_fswap(v___y_1766_, v_mid_1764_, v_hi_1749_);
lean_dec(v_mid_1764_);
v___y_1751_ = v___x_1770_;
goto v___jp_1750_;
}
}
v___jp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v___x_1773_ = lean_array_fget_borrowed(v___y_1772_, v_hi_1749_);
v___x_1774_ = lean_array_fget_borrowed(v___y_1772_, v_lo_1748_);
v___x_1775_ = l_Lean_Name_quickLt(v___x_1773_, v___x_1774_);
if (v___x_1775_ == 0)
{
v___y_1766_ = v___y_1772_;
goto v___jp_1765_;
}
else
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_array_fswap(v___y_1772_, v_lo_1748_, v_hi_1749_);
v___y_1766_ = v___x_1776_;
goto v___jp_1765_;
}
}
}
v___jp_1750_:
{
lean_object* v_pivot_1752_; lean_object* v___x_1753_; lean_object* v_fst_1754_; lean_object* v_snd_1755_; uint8_t v___x_1756_; 
v_pivot_1752_ = lean_array_fget(v___y_1751_, v_hi_1749_);
lean_inc_n(v_lo_1748_, 2);
v___x_1753_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1749_, v_pivot_1752_, v___y_1751_, v_lo_1748_, v_lo_1748_);
lean_dec(v_pivot_1752_);
v_fst_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_fst_1754_);
v_snd_1755_ = lean_ctor_get(v___x_1753_, 1);
lean_inc(v_snd_1755_);
lean_dec_ref(v___x_1753_);
v___x_1756_ = lean_nat_dec_le(v_hi_1749_, v_fst_1754_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1746_, v_snd_1755_, v_lo_1748_, v_fst_1754_);
v___x_1758_ = lean_unsigned_to_nat(1u);
v___x_1759_ = lean_nat_add(v_fst_1754_, v___x_1758_);
lean_dec(v_fst_1754_);
v_as_1747_ = v___x_1757_;
v_lo_1748_ = v___x_1759_;
goto _start;
}
else
{
lean_dec(v_fst_1754_);
lean_dec(v_lo_1748_);
return v_snd_1755_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1781_, lean_object* v_as_1782_, lean_object* v_lo_1783_, lean_object* v_hi_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1781_, v_as_1782_, v_lo_1783_, v_hi_1784_);
lean_dec(v_hi_1784_);
lean_dec(v_n_1781_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1786_, lean_object* v_as_1787_, size_t v_i_1788_, size_t v_stop_1789_, lean_object* v_b_1790_){
_start:
{
lean_object* v___y_1792_; uint8_t v___x_1796_; 
v___x_1796_ = lean_usize_dec_eq(v_i_1788_, v_stop_1789_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; uint8_t v___x_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v___x_1797_ = lean_array_uget_borrowed(v_as_1787_, v_i_1788_);
v___x_1798_ = 1;
lean_inc_ref(v_env_1786_);
v___x_1799_ = l_Lean_Environment_setExporting(v_env_1786_, v___x_1798_);
lean_inc(v___x_1797_);
v___x_1800_ = l_Lean_Environment_contains(v___x_1799_, v___x_1797_, v___x_1796_);
if (v___x_1800_ == 0)
{
v___y_1792_ = v_b_1790_;
goto v___jp_1791_;
}
else
{
lean_object* v___x_1801_; 
lean_inc(v___x_1797_);
v___x_1801_ = lean_array_push(v_b_1790_, v___x_1797_);
v___y_1792_ = v___x_1801_;
goto v___jp_1791_;
}
}
else
{
lean_dec_ref(v_env_1786_);
return v_b_1790_;
}
v___jp_1791_:
{
size_t v___x_1793_; size_t v___x_1794_; 
v___x_1793_ = ((size_t)1ULL);
v___x_1794_ = lean_usize_add(v_i_1788_, v___x_1793_);
v_i_1788_ = v___x_1794_;
v_b_1790_ = v___y_1792_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1802_, lean_object* v_as_1803_, lean_object* v_i_1804_, lean_object* v_stop_1805_, lean_object* v_b_1806_){
_start:
{
size_t v_i_boxed_1807_; size_t v_stop_boxed_1808_; lean_object* v_res_1809_; 
v_i_boxed_1807_ = lean_unbox_usize(v_i_1804_);
lean_dec(v_i_1804_);
v_stop_boxed_1808_ = lean_unbox_usize(v_stop_1805_);
lean_dec(v_stop_1805_);
v_res_1809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1802_, v_as_1803_, v_i_boxed_1807_, v_stop_boxed_1808_, v_b_1806_);
lean_dec_ref(v_as_1803_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1810_, lean_object* v_x_1811_){
_start:
{
if (lean_obj_tag(v_x_1811_) == 0)
{
lean_object* v_k_1812_; lean_object* v_l_1813_; lean_object* v_r_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v_k_1812_ = lean_ctor_get(v_x_1811_, 1);
lean_inc(v_k_1812_);
v_l_1813_ = lean_ctor_get(v_x_1811_, 3);
lean_inc(v_l_1813_);
v_r_1814_ = lean_ctor_get(v_x_1811_, 4);
lean_inc(v_r_1814_);
lean_dec_ref_known(v_x_1811_, 5);
v___x_1815_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1810_, v_l_1813_);
v___x_1816_ = lean_array_push(v___x_1815_, v_k_1812_);
v_init_1810_ = v___x_1816_;
v_x_1811_ = v_r_1814_;
goto _start;
}
else
{
return v_init_1810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1818_, lean_object* v_es_1819_){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___y_1823_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___y_1834_; lean_object* v___y_1835_; uint8_t v___x_1837_; 
v___x_1820_ = lean_unsigned_to_nat(0u);
v___x_1821_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1831_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1821_, v_es_1819_);
v___x_1832_ = lean_array_get_size(v___x_1831_);
v___x_1837_ = lean_nat_dec_eq(v___x_1832_, v___x_1820_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___y_1841_; uint8_t v___x_1843_; 
v___x_1838_ = lean_unsigned_to_nat(1u);
v___x_1839_ = lean_nat_sub(v___x_1832_, v___x_1838_);
v___x_1843_ = lean_nat_dec_le(v___x_1820_, v___x_1839_);
if (v___x_1843_ == 0)
{
lean_inc(v___x_1839_);
v___y_1841_ = v___x_1839_;
goto v___jp_1840_;
}
else
{
v___y_1841_ = v___x_1820_;
goto v___jp_1840_;
}
v___jp_1840_:
{
uint8_t v___x_1842_; 
v___x_1842_ = lean_nat_dec_le(v___y_1841_, v___x_1839_);
if (v___x_1842_ == 0)
{
lean_dec(v___x_1839_);
lean_inc(v___y_1841_);
v___y_1834_ = v___y_1841_;
v___y_1835_ = v___y_1841_;
goto v___jp_1833_;
}
else
{
v___y_1834_ = v___y_1841_;
v___y_1835_ = v___x_1839_;
goto v___jp_1833_;
}
}
}
else
{
v___y_1823_ = v___x_1831_;
goto v___jp_1822_;
}
v___jp_1822_:
{
lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1824_ = lean_array_get_size(v___y_1823_);
v___x_1825_ = lean_nat_dec_lt(v___x_1820_, v___x_1824_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; 
lean_dec_ref(v_env_1818_);
v___x_1826_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1821_);
lean_ctor_set(v___x_1826_, 1, v___x_1821_);
lean_ctor_set(v___x_1826_, 2, v___y_1823_);
return v___x_1826_;
}
else
{
size_t v___x_1827_; size_t v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1827_ = ((size_t)0ULL);
v___x_1828_ = lean_usize_of_nat(v___x_1824_);
v___x_1829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1818_, v___y_1823_, v___x_1827_, v___x_1828_, v___x_1821_);
lean_inc_ref(v___x_1829_);
v___x_1830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
lean_ctor_set(v___x_1830_, 2, v___y_1823_);
return v___x_1830_;
}
}
v___jp_1833_:
{
lean_object* v___x_1836_; 
v___x_1836_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1832_, v___x_1831_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
v___y_1823_ = v___x_1836_;
goto v___jp_1822_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v_name_1844_, lean_object* v_decl_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1849_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1850_ = l_Lean_MessageData_ofName(v_name_1844_);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1849_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1851_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1853_, v___y_1846_, v___y_1847_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v_name_1855_, lean_object* v_decl_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_registerTagAttribute___lam__4(v_name_1855_, v_decl_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v_decl_1856_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1861_, lean_object* v_x_1862_, lean_object* v_x_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1861_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1866_, lean_object* v_x_1867_, lean_object* v_x_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_registerTagAttribute___lam__5(v___x_1866_, v_x_1867_, v_x_1868_);
lean_dec_ref(v_x_1868_);
lean_dec_ref(v_x_1867_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v___x_1871_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1871_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v___x_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_registerTagAttribute___lam__6(v___x_1874_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_a_1877_, lean_object* v_decl_1878_, lean_object* v_s_1879_){
_start:
{
lean_object* v_addEntryFn_1880_; lean_object* v_importedEntries_1881_; lean_object* v_state_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1890_; 
v_addEntryFn_1880_ = lean_ctor_get(v_a_1877_, 3);
lean_inc(v_addEntryFn_1880_);
lean_dec_ref(v_a_1877_);
v_importedEntries_1881_ = lean_ctor_get(v_s_1879_, 0);
v_state_1882_ = lean_ctor_get(v_s_1879_, 1);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_s_1879_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1884_ = v_s_1879_;
v_isShared_1885_ = v_isSharedCheck_1890_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_state_1882_);
lean_inc(v_importedEntries_1881_);
lean_dec(v_s_1879_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1890_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v_state_1886_; lean_object* v___x_1888_; 
v_state_1886_ = lean_apply_2(v_addEntryFn_1880_, v_state_1882_, v_decl_1878_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 1, v_state_1886_);
v___x_1888_ = v___x_1884_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_importedEntries_1881_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_state_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1891_, lean_object* v_declName_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1896_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1897_ = l_Lean_MessageData_ofName(v_attrName_1891_);
v___x_1898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1896_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1898_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = 0;
v___x_1902_ = l_Lean_MessageData_ofConstName(v_declName_1892_, v___x_1901_);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1900_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1905_, v___y_1893_, v___y_1894_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1907_, lean_object* v_declName_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1907_, v_declName_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1913_, lean_object* v_declName_1914_, lean_object* v_asyncPrefix_x3f_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v___y_1920_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1915_) == 0)
{
lean_object* v___x_1933_; 
v___x_1933_ = l_Lean_MessageData_nil;
v___y_1920_ = v___x_1933_;
goto v___jp_1919_;
}
else
{
lean_object* v_val_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_val_1934_ = lean_ctor_get(v_asyncPrefix_x3f_1915_, 0);
lean_inc(v_val_1934_);
lean_dec_ref_known(v_asyncPrefix_x3f_1915_, 1);
v___x_1935_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1936_ = l_Lean_MessageData_ofName(v_val_1934_);
v___x_1937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1935_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1937_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___y_1920_ = v___x_1939_;
goto v___jp_1919_;
}
v___jp_1919_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1921_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1922_ = l_Lean_MessageData_ofName(v_attrName_1913_);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = 0;
v___x_1927_ = l_Lean_MessageData_ofConstName(v_declName_1914_, v___x_1926_);
v___x_1928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1925_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1928_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
lean_ctor_set(v___x_1931_, 1, v___y_1920_);
v___x_1932_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1931_, v___y_1916_, v___y_1917_);
return v___x_1932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1940_, lean_object* v_declName_1941_, lean_object* v_asyncPrefix_x3f_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1940_, v_declName_1941_, v_asyncPrefix_x3f_1942_, v___y_1943_, v___y_1944_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1947_, uint8_t v_kind_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___y_1958_; 
v___x_1952_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1953_ = l_Lean_MessageData_ofName(v_name_1947_);
v___x_1954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1952_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
v___x_1955_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1954_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
switch(v_kind_1948_)
{
case 0:
{
lean_object* v___x_1965_; 
v___x_1965_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1958_ = v___x_1965_;
goto v___jp_1957_;
}
case 1:
{
lean_object* v___x_1966_; 
v___x_1966_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1958_ = v___x_1966_;
goto v___jp_1957_;
}
default: 
{
lean_object* v___x_1967_; 
v___x_1967_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1958_ = v___x_1967_;
goto v___jp_1957_;
}
}
v___jp_1957_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_inc_ref(v___y_1958_);
v___x_1959_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1959_, 0, v___y_1958_);
v___x_1960_ = l_Lean_MessageData_ofFormat(v___x_1959_);
v___x_1961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1956_);
lean_ctor_set(v___x_1961_, 1, v___x_1960_);
v___x_1962_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1961_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1963_, v___y_1949_, v___y_1950_);
return v___x_1964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_1968_, lean_object* v_kind_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
uint8_t v_kind_boxed_1973_; lean_object* v_res_1974_; 
v_kind_boxed_1973_ = lean_unbox(v_kind_1969_);
v_res_1974_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1968_, v_kind_boxed_1973_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__8(lean_object* v_a_1975_, lean_object* v_validate_1976_, lean_object* v_name_1977_, lean_object* v_decl_1978_, lean_object* v_stx_1979_, uint8_t v_kind_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v_nextMacroScope_1987_; lean_object* v_ngen_1988_; lean_object* v_auxDeclNGen_1989_; lean_object* v_traceState_1990_; lean_object* v_recordedDeps_1991_; lean_object* v_messages_1992_; lean_object* v_infoState_1993_; lean_object* v_snapshotTasks_1994_; lean_object* v___y_1995_; lean_object* v___f_2000_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___x_2037_; 
lean_inc(v_decl_1978_);
lean_inc_ref(v_a_1975_);
v___f_2000_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7), 3, 2);
lean_closure_set(v___f_2000_, 0, v_a_1975_);
lean_closure_set(v___f_2000_, 1, v_decl_1978_);
v___x_2037_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1979_, v___y_1981_, v___y_1982_);
if (lean_obj_tag(v___x_2037_) == 0)
{
uint8_t v___x_2038_; uint8_t v___x_2039_; 
lean_dec_ref_known(v___x_2037_, 1);
v___x_2038_ = 0;
v___x_2039_ = l_Lean_instBEqAttributeKind_beq(v_kind_1980_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; 
lean_dec_ref(v___f_2000_);
lean_dec(v_decl_1978_);
lean_dec_ref(v_validate_1976_);
lean_dec_ref(v_a_1975_);
v___x_2040_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1977_, v_kind_1980_, v___y_1981_, v___y_1982_);
return v___x_2040_;
}
else
{
goto v___jp_2032_;
}
}
else
{
lean_dec_ref(v___f_2000_);
lean_dec(v_decl_1978_);
lean_dec(v_name_1977_);
lean_dec_ref(v_validate_1976_);
lean_dec_ref(v_a_1975_);
return v___x_2037_;
}
v___jp_1984_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1996_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_1997_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1997_, 0, v___y_1995_);
lean_ctor_set(v___x_1997_, 1, v_nextMacroScope_1987_);
lean_ctor_set(v___x_1997_, 2, v_ngen_1988_);
lean_ctor_set(v___x_1997_, 3, v_auxDeclNGen_1989_);
lean_ctor_set(v___x_1997_, 4, v_traceState_1990_);
lean_ctor_set(v___x_1997_, 5, v___x_1996_);
lean_ctor_set(v___x_1997_, 6, v_recordedDeps_1991_);
lean_ctor_set(v___x_1997_, 7, v_messages_1992_);
lean_ctor_set(v___x_1997_, 8, v_infoState_1993_);
lean_ctor_set(v___x_1997_, 9, v_snapshotTasks_1994_);
v___x_1998_ = lean_st_ref_put(v___y_1985_, v___x_1997_);
v___x_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1999_, 0, v___y_1986_);
return v___x_1999_;
}
v___jp_2001_:
{
lean_object* v___x_2004_; 
lean_inc(v___y_2003_);
lean_inc_ref(v___y_2002_);
lean_inc(v_decl_1978_);
v___x_2004_ = lean_apply_4(v_validate_1976_, v_decl_1978_, v___y_2002_, v___y_2003_, lean_box(0));
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v___x_2005_; lean_object* v_toEnvExtension_2006_; lean_object* v_env_2007_; lean_object* v_nextMacroScope_2008_; lean_object* v_ngen_2009_; lean_object* v_auxDeclNGen_2010_; lean_object* v_traceState_2011_; lean_object* v_recordedDeps_2012_; lean_object* v_messages_2013_; lean_object* v_infoState_2014_; lean_object* v_snapshotTasks_2015_; lean_object* v_asyncMode_2016_; uint8_t v_logWrites_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; 
lean_dec_ref_known(v___x_2004_, 1);
v___x_2005_ = lean_st_ref_take(v___y_2003_);
v_toEnvExtension_2006_ = lean_ctor_get(v_a_1975_, 0);
lean_inc_ref(v_toEnvExtension_2006_);
lean_dec_ref(v_a_1975_);
v_env_2007_ = lean_ctor_get(v___x_2005_, 0);
lean_inc_ref(v_env_2007_);
v_nextMacroScope_2008_ = lean_ctor_get(v___x_2005_, 1);
lean_inc(v_nextMacroScope_2008_);
v_ngen_2009_ = lean_ctor_get(v___x_2005_, 2);
lean_inc_ref(v_ngen_2009_);
v_auxDeclNGen_2010_ = lean_ctor_get(v___x_2005_, 3);
lean_inc_ref(v_auxDeclNGen_2010_);
v_traceState_2011_ = lean_ctor_get(v___x_2005_, 4);
lean_inc_ref(v_traceState_2011_);
v_recordedDeps_2012_ = lean_ctor_get(v___x_2005_, 6);
lean_inc_ref(v_recordedDeps_2012_);
v_messages_2013_ = lean_ctor_get(v___x_2005_, 7);
lean_inc_ref(v_messages_2013_);
v_infoState_2014_ = lean_ctor_get(v___x_2005_, 8);
lean_inc_ref(v_infoState_2014_);
v_snapshotTasks_2015_ = lean_ctor_get(v___x_2005_, 9);
lean_inc_ref(v_snapshotTasks_2015_);
lean_dec(v___x_2005_);
v_asyncMode_2016_ = lean_ctor_get(v_toEnvExtension_2006_, 2);
lean_inc(v_asyncMode_2016_);
v_logWrites_2017_ = lean_ctor_get_uint8(v_toEnvExtension_2006_, sizeof(void*)*6);
v___x_2018_ = lean_box(0);
v___x_2019_ = 1;
if (v_logWrites_2017_ == 0)
{
lean_object* v___x_2020_; 
v___x_2020_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2006_, v_env_2007_, v___f_2000_, v_asyncMode_2016_, v_decl_1978_, v___x_2019_);
lean_dec(v_asyncMode_2016_);
v___y_1985_ = v___y_2003_;
v___y_1986_ = v___x_2018_;
v_nextMacroScope_1987_ = v_nextMacroScope_2008_;
v_ngen_1988_ = v_ngen_2009_;
v_auxDeclNGen_1989_ = v_auxDeclNGen_2010_;
v_traceState_1990_ = v_traceState_2011_;
v_recordedDeps_1991_ = v_recordedDeps_2012_;
v_messages_1992_ = v_messages_2013_;
v_infoState_1993_ = v_infoState_2014_;
v_snapshotTasks_1994_ = v_snapshotTasks_2015_;
v___y_1995_ = v___x_2020_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_inc(v_decl_1978_);
v___x_2021_ = l_Lean_Environment_logDeclChange(v_env_2007_, v_decl_1978_);
v___x_2022_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2006_, v___x_2021_, v___f_2000_, v_asyncMode_2016_, v_decl_1978_, v___x_2019_);
lean_dec(v_asyncMode_2016_);
v___y_1985_ = v___y_2003_;
v___y_1986_ = v___x_2018_;
v_nextMacroScope_1987_ = v_nextMacroScope_2008_;
v_ngen_1988_ = v_ngen_2009_;
v_auxDeclNGen_1989_ = v_auxDeclNGen_2010_;
v_traceState_1990_ = v_traceState_2011_;
v_recordedDeps_1991_ = v_recordedDeps_2012_;
v_messages_1992_ = v_messages_2013_;
v_infoState_1993_ = v_infoState_2014_;
v_snapshotTasks_1994_ = v_snapshotTasks_2015_;
v___y_1995_ = v___x_2022_;
goto v___jp_1984_;
}
}
else
{
lean_dec_ref(v___f_2000_);
lean_dec(v_decl_1978_);
lean_dec_ref(v_a_1975_);
return v___x_2004_;
}
}
v___jp_2023_:
{
lean_object* v_toEnvExtension_2027_; lean_object* v_asyncMode_2028_; uint8_t v___x_2029_; 
v_toEnvExtension_2027_ = lean_ctor_get(v_a_1975_, 0);
v_asyncMode_2028_ = lean_ctor_get(v_toEnvExtension_2027_, 2);
lean_inc(v_decl_1978_);
lean_inc_ref(v___y_2024_);
v___x_2029_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2024_, v_decl_1978_, v_asyncMode_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
lean_dec_ref(v___f_2000_);
lean_dec_ref(v_validate_1976_);
lean_dec_ref(v_a_1975_);
v___x_2030_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2024_);
v___x_2031_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_1977_, v_decl_1978_, v___x_2030_, v___y_2025_, v___y_2026_);
return v___x_2031_;
}
else
{
lean_dec_ref(v___y_2024_);
lean_dec(v_name_1977_);
v___y_2002_ = v___y_2025_;
v___y_2003_ = v___y_2026_;
goto v___jp_2001_;
}
}
v___jp_2032_:
{
lean_object* v___x_2033_; lean_object* v_env_2034_; lean_object* v___x_2035_; 
v___x_2033_ = lean_st_ref_get(v___y_1982_);
v_env_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc_ref(v_env_2034_);
lean_dec(v___x_2033_);
v___x_2035_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2034_, v_decl_1978_);
if (lean_obj_tag(v___x_2035_) == 0)
{
v___y_2024_ = v_env_2034_;
v___y_2025_ = v___y_1981_;
v___y_2026_ = v___y_1982_;
goto v___jp_2023_;
}
else
{
lean_object* v___x_2036_; 
lean_dec_ref_known(v___x_2035_, 1);
lean_dec_ref(v_env_2034_);
lean_dec_ref(v___f_2000_);
lean_dec_ref(v_validate_1976_);
lean_dec_ref(v_a_1975_);
v___x_2036_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_1977_, v_decl_1978_, v___y_1981_, v___y_1982_);
return v___x_2036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__8___boxed(lean_object* v_a_2041_, lean_object* v_validate_2042_, lean_object* v_name_2043_, lean_object* v_decl_2044_, lean_object* v_stx_2045_, lean_object* v_kind_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
uint8_t v_kind_boxed_2050_; lean_object* v_res_2051_; 
v_kind_boxed_2050_ = lean_unbox(v_kind_2046_);
v_res_2051_ = l_Lean_registerTagAttribute___lam__8(v_a_2041_, v_validate_2042_, v_name_2043_, v_decl_2044_, v_stx_2045_, v_kind_boxed_2050_, v___y_2047_, v___y_2048_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
return v_res_2051_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___f_2058_; 
v___x_2057_ = l_Lean_NameSet_empty;
v___f_2058_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 4, 1);
lean_closure_set(v___f_2058_, 0, v___x_2057_);
return v___f_2058_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___f_2060_; 
v___x_2059_ = l_Lean_NameSet_empty;
v___f_2060_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 2, 1);
lean_closure_set(v___f_2060_, 0, v___x_2059_);
return v___f_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2063_, lean_object* v_descr_2064_, lean_object* v_validate_2065_, lean_object* v_ref_2066_, uint8_t v_applicationTime_2067_, lean_object* v_asyncMode_2068_, uint8_t v_logWrites_2069_){
_start:
{
lean_object* v___f_2071_; lean_object* v___f_2072_; lean_object* v___f_2073_; lean_object* v___f_2074_; lean_object* v___f_2075_; lean_object* v___f_2076_; lean_object* v___f_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___f_2071_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2072_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2073_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2074_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
lean_inc(v_name_2063_);
v___f_2075_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 5, 1);
lean_closure_set(v___f_2075_, 0, v_name_2063_);
v___f_2076_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2077_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2078_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
v___x_2079_ = 0;
lean_inc(v_ref_2066_);
v___x_2080_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2080_, 0, v_ref_2066_);
lean_ctor_set(v___x_2080_, 1, v___f_2077_);
lean_ctor_set(v___x_2080_, 2, v___f_2076_);
lean_ctor_set(v___x_2080_, 3, v___f_2074_);
lean_ctor_set(v___x_2080_, 4, v___f_2073_);
lean_ctor_set(v___x_2080_, 5, v___f_2072_);
lean_ctor_set(v___x_2080_, 6, v_asyncMode_2068_);
lean_ctor_set(v___x_2080_, 7, v___x_2078_);
lean_ctor_set_uint8(v___x_2080_, sizeof(void*)*8, v___x_2079_);
lean_ctor_set_uint8(v___x_2080_, sizeof(void*)*8 + 1, v_logWrites_2069_);
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
lean_ctor_set(v___x_2081_, 1, v___f_2071_);
v___x_2082_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2081_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___f_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc_n(v_a_2083_, 2);
lean_dec_ref_known(v___x_2082_, 1);
lean_inc(v_name_2063_);
v___f_2084_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__8___boxed), 9, 3);
lean_closure_set(v___f_2084_, 0, v_a_2083_);
lean_closure_set(v___f_2084_, 1, v_validate_2065_);
lean_closure_set(v___f_2084_, 2, v_name_2063_);
v___x_2085_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2085_, 0, v_ref_2066_);
lean_ctor_set(v___x_2085_, 1, v_name_2063_);
lean_ctor_set(v___x_2085_, 2, v_descr_2064_);
lean_ctor_set_uint8(v___x_2085_, sizeof(void*)*3, v_applicationTime_2067_);
v___x_2086_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
lean_ctor_set(v___x_2086_, 1, v___f_2084_);
lean_ctor_set(v___x_2086_, 2, v___f_2075_);
lean_inc_ref(v___x_2086_);
v___x_2087_ = l_Lean_registerBuiltinAttribute(v___x_2086_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2095_; 
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2095_ == 0)
{
lean_object* v_unused_2096_; 
v_unused_2096_ = lean_ctor_get(v___x_2087_, 0);
lean_dec(v_unused_2096_);
v___x_2089_ = v___x_2087_;
v_isShared_2090_ = v_isSharedCheck_2095_;
goto v_resetjp_2088_;
}
else
{
lean_dec(v___x_2087_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2095_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2086_);
lean_ctor_set(v___x_2091_, 1, v_a_2083_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2091_);
v___x_2093_ = v___x_2089_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec_ref_known(v___x_2086_, 3);
lean_dec(v_a_2083_);
v_a_2097_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2087_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2087_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec_ref(v___f_2075_);
lean_dec(v_ref_2066_);
lean_dec_ref(v_validate_2065_);
lean_dec_ref(v_descr_2064_);
lean_dec(v_name_2063_);
v_a_2105_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2082_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2082_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2113_, lean_object* v_descr_2114_, lean_object* v_validate_2115_, lean_object* v_ref_2116_, lean_object* v_applicationTime_2117_, lean_object* v_asyncMode_2118_, lean_object* v_logWrites_2119_, lean_object* v_a_2120_){
_start:
{
uint8_t v_applicationTime_boxed_2121_; uint8_t v_logWrites_boxed_2122_; lean_object* v_res_2123_; 
v_applicationTime_boxed_2121_ = lean_unbox(v_applicationTime_2117_);
v_logWrites_boxed_2122_ = lean_unbox(v_logWrites_2119_);
v_res_2123_ = l_Lean_registerTagAttribute(v_name_2113_, v_descr_2114_, v_validate_2115_, v_ref_2116_, v_applicationTime_boxed_2121_, v_asyncMode_2118_, v_logWrites_boxed_2122_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2124_, lean_object* v_t_2125_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2124_, v_t_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2127_, lean_object* v_as_2128_, lean_object* v_lo_2129_, lean_object* v_hi_2130_, lean_object* v_w_2131_, lean_object* v_hlo_2132_, lean_object* v_hhi_2133_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2127_, v_as_2128_, v_lo_2129_, v_hi_2130_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2135_, lean_object* v_as_2136_, lean_object* v_lo_2137_, lean_object* v_hi_2138_, lean_object* v_w_2139_, lean_object* v_hlo_2140_, lean_object* v_hhi_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2135_, v_as_2136_, v_lo_2137_, v_hi_2138_, v_w_2139_, v_hlo_2140_, v_hhi_2141_);
lean_dec(v_hi_2138_);
lean_dec(v_n_2135_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2143_, lean_object* v_attrName_2144_, lean_object* v_declName_2145_, lean_object* v_asyncPrefix_x3f_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2144_, v_declName_2145_, v_asyncPrefix_x3f_2146_, v___y_2147_, v___y_2148_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2151_, lean_object* v_attrName_2152_, lean_object* v_declName_2153_, lean_object* v_asyncPrefix_x3f_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2151_, v_attrName_2152_, v_declName_2153_, v_asyncPrefix_x3f_2154_, v___y_2155_, v___y_2156_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2159_, lean_object* v_attrName_2160_, lean_object* v_declName_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2160_, v_declName_2161_, v___y_2162_, v___y_2163_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2166_, lean_object* v_attrName_2167_, lean_object* v_declName_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2166_, v_attrName_2167_, v_declName_2168_, v___y_2169_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2173_, lean_object* v_name_2174_, uint8_t v_kind_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2174_, v_kind_2175_, v___y_2176_, v___y_2177_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2180_, lean_object* v_name_2181_, lean_object* v_kind_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
uint8_t v_kind_boxed_2186_; lean_object* v_res_2187_; 
v_kind_boxed_2186_ = lean_unbox(v_kind_2182_);
v_res_2187_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2180_, v_name_2181_, v_kind_boxed_2186_, v___y_2183_, v___y_2184_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2188_, lean_object* v_lo_2189_, lean_object* v_hi_2190_, lean_object* v_hhi_2191_, lean_object* v_pivot_2192_, lean_object* v_as_2193_, lean_object* v_i_2194_, lean_object* v_k_2195_, lean_object* v_ilo_2196_, lean_object* v_ik_2197_, lean_object* v_w_2198_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2190_, v_pivot_2192_, v_as_2193_, v_i_2194_, v_k_2195_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2200_, lean_object* v_lo_2201_, lean_object* v_hi_2202_, lean_object* v_hhi_2203_, lean_object* v_pivot_2204_, lean_object* v_as_2205_, lean_object* v_i_2206_, lean_object* v_k_2207_, lean_object* v_ilo_2208_, lean_object* v_ik_2209_, lean_object* v_w_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2200_, v_lo_2201_, v_hi_2202_, v_hhi_2203_, v_pivot_2204_, v_as_2205_, v_i_2206_, v_k_2207_, v_ilo_2208_, v_ik_2209_, v_w_2210_);
lean_dec(v_pivot_2204_);
lean_dec(v_hi_2202_);
lean_dec(v_lo_2201_);
lean_dec(v_n_2200_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_addEntryFn_2212_, lean_object* v_decl_2213_, lean_object* v_s_2214_){
_start:
{
lean_object* v_importedEntries_2215_; lean_object* v_state_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2224_; 
v_importedEntries_2215_ = lean_ctor_get(v_s_2214_, 0);
v_state_2216_ = lean_ctor_get(v_s_2214_, 1);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_s_2214_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2218_ = v_s_2214_;
v_isShared_2219_ = v_isSharedCheck_2224_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_state_2216_);
lean_inc(v_importedEntries_2215_);
lean_dec(v_s_2214_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2224_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v_state_2220_; lean_object* v___x_2222_; 
v_state_2220_ = lean_apply_2(v_addEntryFn_2212_, v_state_2216_, v_decl_2213_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v_state_2220_);
v___x_2222_ = v___x_2218_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_importedEntries_2215_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_state_2220_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_attr_2225_, lean_object* v_decl_2226_, lean_object* v_env_2227_){
_start:
{
lean_object* v_ext_2228_; lean_object* v_toEnvExtension_2229_; lean_object* v_addEntryFn_2230_; lean_object* v_asyncMode_2231_; uint8_t v_logWrites_2232_; lean_object* v___f_2233_; uint8_t v___x_2234_; 
v_ext_2228_ = lean_ctor_get(v_attr_2225_, 1);
lean_inc_ref(v_ext_2228_);
lean_dec_ref(v_attr_2225_);
v_toEnvExtension_2229_ = lean_ctor_get(v_ext_2228_, 0);
lean_inc_ref(v_toEnvExtension_2229_);
v_addEntryFn_2230_ = lean_ctor_get(v_ext_2228_, 3);
lean_inc(v_addEntryFn_2230_);
lean_dec_ref(v_ext_2228_);
v_asyncMode_2231_ = lean_ctor_get(v_toEnvExtension_2229_, 2);
lean_inc(v_asyncMode_2231_);
v_logWrites_2232_ = lean_ctor_get_uint8(v_toEnvExtension_2229_, sizeof(void*)*6);
lean_inc(v_decl_2226_);
v___f_2233_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2233_, 0, v_addEntryFn_2230_);
lean_closure_set(v___f_2233_, 1, v_decl_2226_);
v___x_2234_ = 1;
if (v_logWrites_2232_ == 0)
{
lean_object* v___x_2235_; 
v___x_2235_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2229_, v_env_2227_, v___f_2233_, v_asyncMode_2231_, v_decl_2226_, v___x_2234_);
lean_dec(v_asyncMode_2231_);
return v___x_2235_;
}
else
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
lean_inc_ref(v_toEnvExtension_2229_);
v___x_2236_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2229_, v_env_2227_);
lean_dec_ref(v_env_2227_);
v___x_2237_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2229_, v___x_2236_, v___f_2233_, v_asyncMode_2231_, v_decl_2226_, v___x_2234_);
lean_dec(v_asyncMode_2231_);
return v___x_2237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_modifyEnv_2238_, lean_object* v___f_2239_, lean_object* v_____r_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = lean_apply_1(v_modifyEnv_2238_, v___f_2239_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v_attr_2242_, lean_object* v_env_2243_, lean_object* v_decl_2244_, lean_object* v_inst_2245_, lean_object* v_inst_2246_, lean_object* v_toBind_2247_, lean_object* v___f_2248_, lean_object* v_modifyEnv_2249_, lean_object* v___f_2250_, lean_object* v_____r_2251_){
_start:
{
lean_object* v_ext_2252_; lean_object* v_toEnvExtension_2253_; lean_object* v_attr_2254_; lean_object* v_asyncMode_2255_; uint8_t v___x_2256_; 
v_ext_2252_ = lean_ctor_get(v_attr_2242_, 1);
v_toEnvExtension_2253_ = lean_ctor_get(v_ext_2252_, 0);
lean_inc_ref(v_toEnvExtension_2253_);
v_attr_2254_ = lean_ctor_get(v_attr_2242_, 0);
lean_inc_ref(v_attr_2254_);
lean_dec_ref(v_attr_2242_);
v_asyncMode_2255_ = lean_ctor_get(v_toEnvExtension_2253_, 2);
lean_inc(v_asyncMode_2255_);
lean_dec_ref(v_toEnvExtension_2253_);
lean_inc(v_decl_2244_);
lean_inc_ref(v_env_2243_);
v___x_2256_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2243_, v_decl_2244_, v_asyncMode_2255_);
lean_dec(v_asyncMode_2255_);
if (v___x_2256_ == 0)
{
lean_object* v_toAttributeImplCore_2257_; lean_object* v_name_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_dec_ref(v___f_2250_);
lean_dec(v_modifyEnv_2249_);
v_toAttributeImplCore_2257_ = lean_ctor_get(v_attr_2254_, 0);
lean_inc_ref(v_toAttributeImplCore_2257_);
lean_dec_ref(v_attr_2254_);
v_name_2258_ = lean_ctor_get(v_toAttributeImplCore_2257_, 1);
lean_inc(v_name_2258_);
lean_dec_ref(v_toAttributeImplCore_2257_);
v___x_2259_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2243_);
v___x_2260_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2245_, v_inst_2246_, v_name_2258_, v_decl_2244_, v___x_2259_);
v___x_2261_ = lean_apply_4(v_toBind_2247_, lean_box(0), lean_box(0), v___x_2260_, v___f_2248_);
return v___x_2261_;
}
else
{
lean_object* v___x_2262_; 
lean_dec_ref(v_attr_2254_);
lean_dec(v___f_2248_);
lean_dec(v_toBind_2247_);
lean_dec_ref(v_inst_2246_);
lean_dec_ref(v_inst_2245_);
lean_dec(v_decl_2244_);
lean_dec_ref(v_env_2243_);
v___x_2262_ = lean_apply_1(v_modifyEnv_2249_, v___f_2250_);
return v___x_2262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v___f_2263_, lean_object* v_____r_2264_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = lean_apply_1(v___f_2263_, v_____r_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__5(lean_object* v_attr_2266_, lean_object* v_decl_2267_, lean_object* v_inst_2268_, lean_object* v_inst_2269_, lean_object* v_toBind_2270_, lean_object* v___f_2271_, lean_object* v_modifyEnv_2272_, lean_object* v___f_2273_, lean_object* v_env_2274_){
_start:
{
lean_object* v___f_2275_; lean_object* v___x_2276_; 
lean_inc_ref(v___f_2273_);
lean_inc(v_modifyEnv_2272_);
lean_inc(v___f_2271_);
lean_inc(v_toBind_2270_);
lean_inc_ref(v_inst_2269_);
lean_inc_ref(v_inst_2268_);
lean_inc(v_decl_2267_);
lean_inc_ref(v_env_2274_);
lean_inc_ref(v_attr_2266_);
v___f_2275_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 10, 9);
lean_closure_set(v___f_2275_, 0, v_attr_2266_);
lean_closure_set(v___f_2275_, 1, v_env_2274_);
lean_closure_set(v___f_2275_, 2, v_decl_2267_);
lean_closure_set(v___f_2275_, 3, v_inst_2268_);
lean_closure_set(v___f_2275_, 4, v_inst_2269_);
lean_closure_set(v___f_2275_, 5, v_toBind_2270_);
lean_closure_set(v___f_2275_, 6, v___f_2271_);
lean_closure_set(v___f_2275_, 7, v_modifyEnv_2272_);
lean_closure_set(v___f_2275_, 8, v___f_2273_);
v___x_2276_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2274_, v_decl_2267_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
lean_dec_ref(v___f_2275_);
v___x_2277_ = lean_box(0);
v___x_2278_ = l_Lean_TagAttribute_setTag___redArg___lam__3(v_attr_2266_, v_env_2274_, v_decl_2267_, v_inst_2268_, v_inst_2269_, v_toBind_2270_, v___f_2271_, v_modifyEnv_2272_, v___f_2273_, v___x_2277_);
return v___x_2278_;
}
else
{
lean_object* v_attr_2279_; lean_object* v_toAttributeImplCore_2280_; lean_object* v_name_2281_; lean_object* v___f_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
lean_dec_ref_known(v___x_2276_, 1);
lean_dec_ref(v_env_2274_);
lean_dec_ref(v___f_2273_);
lean_dec(v_modifyEnv_2272_);
lean_dec(v___f_2271_);
v_attr_2279_ = lean_ctor_get(v_attr_2266_, 0);
lean_inc_ref(v_attr_2279_);
lean_dec_ref(v_attr_2266_);
v_toAttributeImplCore_2280_ = lean_ctor_get(v_attr_2279_, 0);
lean_inc_ref(v_toAttributeImplCore_2280_);
lean_dec_ref(v_attr_2279_);
v_name_2281_ = lean_ctor_get(v_toAttributeImplCore_2280_, 1);
lean_inc(v_name_2281_);
lean_dec_ref(v_toAttributeImplCore_2280_);
v___f_2282_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2282_, 0, v___f_2275_);
v___x_2283_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2268_, v_inst_2269_, v_name_2281_, v_decl_2267_);
v___x_2284_ = lean_apply_4(v_toBind_2270_, lean_box(0), lean_box(0), v___x_2283_, v___f_2282_);
return v___x_2284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2285_, lean_object* v_inst_2286_, lean_object* v_inst_2287_, lean_object* v_attr_2288_, lean_object* v_decl_2289_){
_start:
{
lean_object* v_toBind_2290_; lean_object* v_getEnv_2291_; lean_object* v_modifyEnv_2292_; lean_object* v___f_2293_; lean_object* v___f_2294_; lean_object* v___f_2295_; lean_object* v___x_2296_; 
v_toBind_2290_ = lean_ctor_get(v_inst_2285_, 1);
lean_inc_n(v_toBind_2290_, 2);
v_getEnv_2291_ = lean_ctor_get(v_inst_2287_, 0);
lean_inc(v_getEnv_2291_);
v_modifyEnv_2292_ = lean_ctor_get(v_inst_2287_, 1);
lean_inc_n(v_modifyEnv_2292_, 2);
lean_dec_ref(v_inst_2287_);
lean_inc(v_decl_2289_);
lean_inc_ref(v_attr_2288_);
v___f_2293_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2293_, 0, v_attr_2288_);
lean_closure_set(v___f_2293_, 1, v_decl_2289_);
lean_inc_ref(v___f_2293_);
v___f_2294_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2294_, 0, v_modifyEnv_2292_);
lean_closure_set(v___f_2294_, 1, v___f_2293_);
v___f_2295_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__5), 9, 8);
lean_closure_set(v___f_2295_, 0, v_attr_2288_);
lean_closure_set(v___f_2295_, 1, v_decl_2289_);
lean_closure_set(v___f_2295_, 2, v_inst_2285_);
lean_closure_set(v___f_2295_, 3, v_inst_2286_);
lean_closure_set(v___f_2295_, 4, v_toBind_2290_);
lean_closure_set(v___f_2295_, 5, v___f_2294_);
lean_closure_set(v___f_2295_, 6, v_modifyEnv_2292_);
lean_closure_set(v___f_2295_, 7, v___f_2293_);
v___x_2296_ = lean_apply_4(v_toBind_2290_, lean_box(0), lean_box(0), v_getEnv_2291_, v___f_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2297_, lean_object* v_inst_2298_, lean_object* v_inst_2299_, lean_object* v_inst_2300_, lean_object* v_attr_2301_, lean_object* v_decl_2302_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2298_, v_inst_2299_, v_inst_2300_, v_attr_2301_, v_decl_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2304_, lean_object* v_env_2305_, lean_object* v_decl_2306_){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = lean_box(1);
v___x_2308_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2305_, v_decl_2306_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_ext_2309_; lean_object* v_toEnvExtension_2310_; lean_object* v_asyncMode_2311_; uint8_t v___x_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v_ext_2309_ = lean_ctor_get(v_attr_2304_, 1);
v_toEnvExtension_2310_ = lean_ctor_get(v_ext_2309_, 0);
v_asyncMode_2311_ = lean_ctor_get(v_toEnvExtension_2310_, 2);
v___x_2312_ = 0;
lean_inc(v_decl_2306_);
v___x_2313_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2307_, v_ext_2309_, v_env_2305_, v_asyncMode_2311_, v_decl_2306_, v___x_2312_);
v___x_2314_ = l_Lean_NameSet_contains(v___x_2313_, v_decl_2306_);
lean_dec(v_decl_2306_);
lean_dec(v___x_2313_);
return v___x_2314_;
}
else
{
lean_object* v_val_2315_; lean_object* v_ext_2316_; uint8_t v___x_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; 
v_val_2315_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_val_2315_);
lean_dec_ref_known(v___x_2308_, 1);
v_ext_2316_ = lean_ctor_get(v_attr_2304_, 1);
v___x_2317_ = 0;
v___x_2318_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2307_, v_ext_2316_, v_env_2305_, v_val_2315_, v___x_2317_);
lean_dec(v_val_2315_);
lean_dec_ref(v_env_2305_);
v___x_2319_ = l_Lean_containsSortedName(v___x_2318_, v_decl_2306_);
lean_dec(v_decl_2306_);
lean_dec_ref(v___x_2318_);
return v___x_2319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2320_, lean_object* v_env_2321_, lean_object* v_decl_2322_){
_start:
{
uint8_t v_res_2323_; lean_object* v_r_2324_; 
v_res_2323_ = l_Lean_TagAttribute_hasTag(v_attr_2320_, v_env_2321_, v_decl_2322_);
lean_dec_ref(v_attr_2320_);
v_r_2324_ = lean_box(v_res_2323_);
return v_r_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(lean_object* v_x_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0___boxed(lean_object* v_x_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(v_x_2330_, v___y_2331_);
lean_dec_ref(v___y_2331_);
lean_dec_ref(v_x_2330_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(lean_object* v_s_2334_, lean_object* v_x_2335_){
_start:
{
lean_inc_ref(v_s_2334_);
return v_s_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1___boxed(lean_object* v_s_2336_, lean_object* v_x_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(v_s_2336_, v_x_2337_);
lean_dec_ref(v_x_2337_);
lean_dec_ref(v_s_2336_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(lean_object* v_x_2343_, lean_object* v_x_2344_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___boxed(lean_object* v_x_2346_, lean_object* v_x_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(v_x_2346_, v_x_2347_);
lean_dec_ref(v_x_2347_);
lean_dec_ref(v_x_2346_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(lean_object* v_x_2349_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = lean_box(0);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3___boxed(lean_object* v_x_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(v_x_2351_);
lean_dec_ref(v_x_2351_);
return v_res_2352_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4(void){
_start:
{
lean_object* v___f_2357_; lean_object* v___f_2358_; lean_object* v___f_2359_; lean_object* v___f_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___f_2357_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3));
v___f_2358_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2));
v___f_2359_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1));
v___f_2360_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0));
v___x_2361_ = lean_box(0);
v___x_2362_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_2363_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
lean_ctor_set(v___x_2363_, 1, v___x_2361_);
lean_ctor_set(v___x_2363_, 2, v___f_2360_);
lean_ctor_set(v___x_2363_, 3, v___f_2359_);
lean_ctor_set(v___x_2363_, 4, v___f_2358_);
lean_ctor_set(v___x_2363_, 5, v___f_2357_);
return v___x_2363_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5(void){
_start:
{
uint8_t v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2364_ = 0;
v___x_2365_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4);
v___x_2366_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2367_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
lean_ctor_set(v___x_2367_, 1, v___x_2365_);
lean_ctor_set_uint8(v___x_2367_, sizeof(void*)*2, v___x_2364_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg(){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___boxed(lean_object* v___dummy_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v_res_2371_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__0(void){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2373_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg(){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg___boxed(lean_object* v___dummy_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_instInhabitedParametricAttribute___redArg();
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2379_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object* v_x_2381_, lean_object* v_p_2382_){
_start:
{
lean_object* v_fst_2383_; lean_object* v_snd_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2401_; 
v_fst_2383_ = lean_ctor_get(v_x_2381_, 0);
v_snd_2384_ = lean_ctor_get(v_x_2381_, 1);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_x_2381_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2386_ = v_x_2381_;
v_isShared_2387_ = v_isSharedCheck_2401_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_snd_2384_);
lean_inc(v_fst_2383_);
lean_dec(v_x_2381_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2401_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v_fst_2388_; lean_object* v_snd_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2400_; 
v_fst_2388_ = lean_ctor_get(v_p_2382_, 0);
v_snd_2389_ = lean_ctor_get(v_p_2382_, 1);
v_isSharedCheck_2400_ = !lean_is_exclusive(v_p_2382_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2391_ = v_p_2382_;
v_isShared_2392_ = v_isSharedCheck_2400_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_snd_2389_);
lean_inc(v_fst_2388_);
lean_dec(v_p_2382_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2400_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
lean_inc(v_fst_2388_);
if (v_isShared_2387_ == 0)
{
lean_ctor_set_tag(v___x_2386_, 1);
lean_ctor_set(v___x_2386_, 1, v_fst_2383_);
lean_ctor_set(v___x_2386_, 0, v_fst_2388_);
v___x_2394_ = v___x_2386_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_fst_2388_);
lean_ctor_set(v_reuseFailAlloc_2399_, 1, v_fst_2383_);
v___x_2394_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
lean_object* v___x_2395_; lean_object* v___x_2397_; 
v___x_2395_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2388_, v_snd_2389_, v_snd_2384_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 1, v___x_2395_);
lean_ctor_set(v___x_2391_, 0, v___x_2394_);
v___x_2397_ = v___x_2391_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object* v_init_2402_, lean_object* v_x_2403_){
_start:
{
if (lean_obj_tag(v_x_2403_) == 0)
{
lean_object* v_k_2404_; lean_object* v_v_2405_; lean_object* v_l_2406_; lean_object* v_r_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v_k_2404_ = lean_ctor_get(v_x_2403_, 1);
v_v_2405_ = lean_ctor_get(v_x_2403_, 2);
v_l_2406_ = lean_ctor_get(v_x_2403_, 3);
v_r_2407_ = lean_ctor_get(v_x_2403_, 4);
v___x_2408_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2402_, v_l_2406_);
lean_inc(v_v_2405_);
lean_inc(v_k_2404_);
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v_k_2404_);
lean_ctor_set(v___x_2409_, 1, v_v_2405_);
v___x_2410_ = lean_array_push(v___x_2408_, v___x_2409_);
v_init_2402_ = v___x_2410_;
v_x_2403_ = v_r_2407_;
goto _start;
}
else
{
return v_init_2402_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object* v_init_2412_, lean_object* v_x_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2412_, v_x_2413_);
lean_dec(v_x_2413_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object* v_snd_2415_, lean_object* v_as_2416_, size_t v_i_2417_, size_t v_stop_2418_, lean_object* v_b_2419_){
_start:
{
lean_object* v___y_2421_; uint8_t v___x_2425_; 
v___x_2425_ = lean_usize_dec_eq(v_i_2417_, v_stop_2418_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = lean_array_uget_borrowed(v_as_2416_, v_i_2417_);
v___x_2427_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2415_, v___x_2426_);
if (lean_obj_tag(v___x_2427_) == 0)
{
v___y_2421_ = v_b_2419_;
goto v___jp_2420_;
}
else
{
lean_object* v_val_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v_val_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_val_2428_);
lean_dec_ref_known(v___x_2427_, 1);
lean_inc(v___x_2426_);
v___x_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2426_);
lean_ctor_set(v___x_2429_, 1, v_val_2428_);
v___x_2430_ = lean_array_push(v_b_2419_, v___x_2429_);
v___y_2421_ = v___x_2430_;
goto v___jp_2420_;
}
}
else
{
return v_b_2419_;
}
v___jp_2420_:
{
size_t v___x_2422_; size_t v___x_2423_; 
v___x_2422_ = ((size_t)1ULL);
v___x_2423_ = lean_usize_add(v_i_2417_, v___x_2422_);
v_i_2417_ = v___x_2423_;
v_b_2419_ = v___y_2421_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2431_, lean_object* v_as_2432_, lean_object* v_i_2433_, lean_object* v_stop_2434_, lean_object* v_b_2435_){
_start:
{
size_t v_i_boxed_2436_; size_t v_stop_boxed_2437_; lean_object* v_res_2438_; 
v_i_boxed_2436_ = lean_unbox_usize(v_i_2433_);
lean_dec(v_i_2433_);
v_stop_boxed_2437_ = lean_unbox_usize(v_stop_2434_);
lean_dec(v_stop_2434_);
v_res_2438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2431_, v_as_2432_, v_i_boxed_2436_, v_stop_boxed_2437_, v_b_2435_);
lean_dec_ref(v_as_2432_);
lean_dec(v_snd_2431_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object* v_snd_2439_, lean_object* v_as_2440_, lean_object* v_start_2441_, lean_object* v_stop_2442_){
_start:
{
lean_object* v___x_2443_; uint8_t v___x_2444_; 
v___x_2443_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2444_ = lean_nat_dec_lt(v_start_2441_, v_stop_2442_);
if (v___x_2444_ == 0)
{
return v___x_2443_;
}
else
{
lean_object* v___x_2445_; uint8_t v___x_2446_; 
v___x_2445_ = lean_array_get_size(v_as_2440_);
v___x_2446_ = lean_nat_dec_le(v_stop_2442_, v___x_2445_);
if (v___x_2446_ == 0)
{
uint8_t v___x_2447_; 
v___x_2447_ = lean_nat_dec_lt(v_start_2441_, v___x_2445_);
if (v___x_2447_ == 0)
{
return v___x_2443_;
}
else
{
size_t v___x_2448_; size_t v___x_2449_; lean_object* v___x_2450_; 
v___x_2448_ = lean_usize_of_nat(v_start_2441_);
v___x_2449_ = lean_usize_of_nat(v___x_2445_);
v___x_2450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2439_, v_as_2440_, v___x_2448_, v___x_2449_, v___x_2443_);
return v___x_2450_;
}
}
else
{
size_t v___x_2451_; size_t v___x_2452_; lean_object* v___x_2453_; 
v___x_2451_ = lean_usize_of_nat(v_start_2441_);
v___x_2452_ = lean_usize_of_nat(v_stop_2442_);
v___x_2453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2439_, v_as_2440_, v___x_2451_, v___x_2452_, v___x_2443_);
return v___x_2453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object* v_snd_2454_, lean_object* v_as_2455_, lean_object* v_start_2456_, lean_object* v_stop_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2454_, v_as_2455_, v_start_2456_, v_stop_2457_);
lean_dec(v_stop_2457_);
lean_dec(v_start_2456_);
lean_dec_ref(v_as_2455_);
lean_dec(v_snd_2454_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object* v_hi_2459_, lean_object* v_pivot_2460_, lean_object* v_as_2461_, lean_object* v_i_2462_, lean_object* v_k_2463_){
_start:
{
uint8_t v___x_2464_; 
v___x_2464_ = lean_nat_dec_lt(v_k_2463_, v_hi_2459_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
lean_dec(v_k_2463_);
v___x_2465_ = lean_array_fswap(v_as_2461_, v_i_2462_, v_hi_2459_);
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v_i_2462_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
return v___x_2466_;
}
else
{
lean_object* v___x_2467_; lean_object* v_fst_2468_; lean_object* v_fst_2469_; uint8_t v___x_2470_; 
v___x_2467_ = lean_array_fget_borrowed(v_as_2461_, v_k_2463_);
v_fst_2468_ = lean_ctor_get(v___x_2467_, 0);
v_fst_2469_ = lean_ctor_get(v_pivot_2460_, 0);
v___x_2470_ = l_Lean_Name_quickLt(v_fst_2468_, v_fst_2469_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = lean_unsigned_to_nat(1u);
v___x_2472_ = lean_nat_add(v_k_2463_, v___x_2471_);
lean_dec(v_k_2463_);
v_k_2463_ = v___x_2472_;
goto _start;
}
else
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2474_ = lean_array_fswap(v_as_2461_, v_i_2462_, v_k_2463_);
v___x_2475_ = lean_unsigned_to_nat(1u);
v___x_2476_ = lean_nat_add(v_i_2462_, v___x_2475_);
lean_dec(v_i_2462_);
v___x_2477_ = lean_nat_add(v_k_2463_, v___x_2475_);
lean_dec(v_k_2463_);
v_as_2461_ = v___x_2474_;
v_i_2462_ = v___x_2476_;
v_k_2463_ = v___x_2477_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2479_, lean_object* v_pivot_2480_, lean_object* v_as_2481_, lean_object* v_i_2482_, lean_object* v_k_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2479_, v_pivot_2480_, v_as_2481_, v_i_2482_, v_k_2483_);
lean_dec_ref(v_pivot_2480_);
lean_dec(v_hi_2479_);
return v_res_2484_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object* v_a_2485_, lean_object* v_b_2486_){
_start:
{
lean_object* v_fst_2487_; lean_object* v_fst_2488_; uint8_t v___x_2489_; 
v_fst_2487_ = lean_ctor_get(v_a_2485_, 0);
v_fst_2488_ = lean_ctor_get(v_b_2486_, 0);
v___x_2489_ = l_Lean_Name_quickLt(v_fst_2487_, v_fst_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object* v_a_2490_, lean_object* v_b_2491_){
_start:
{
uint8_t v_res_2492_; lean_object* v_r_2493_; 
v_res_2492_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2490_, v_b_2491_);
lean_dec_ref(v_b_2491_);
lean_dec_ref(v_a_2490_);
v_r_2493_ = lean_box(v_res_2492_);
return v_r_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object* v_n_2494_, lean_object* v_as_2495_, lean_object* v_lo_2496_, lean_object* v_hi_2497_){
_start:
{
lean_object* v___y_2499_; uint8_t v___x_2509_; 
v___x_2509_ = lean_nat_dec_lt(v_lo_2496_, v_hi_2497_);
if (v___x_2509_ == 0)
{
lean_dec(v_lo_2496_);
return v_as_2495_;
}
else
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v_mid_2512_; lean_object* v___y_2514_; lean_object* v___y_2520_; lean_object* v___x_2525_; lean_object* v___x_2526_; uint8_t v___x_2527_; 
v___x_2510_ = lean_nat_add(v_lo_2496_, v_hi_2497_);
v___x_2511_ = lean_unsigned_to_nat(1u);
v_mid_2512_ = lean_nat_shiftr(v___x_2510_, v___x_2511_);
lean_dec(v___x_2510_);
v___x_2525_ = lean_array_fget_borrowed(v_as_2495_, v_mid_2512_);
v___x_2526_ = lean_array_fget_borrowed(v_as_2495_, v_lo_2496_);
v___x_2527_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2525_, v___x_2526_);
if (v___x_2527_ == 0)
{
v___y_2520_ = v_as_2495_;
goto v___jp_2519_;
}
else
{
lean_object* v___x_2528_; 
v___x_2528_ = lean_array_fswap(v_as_2495_, v_lo_2496_, v_mid_2512_);
v___y_2520_ = v___x_2528_;
goto v___jp_2519_;
}
v___jp_2513_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; 
v___x_2515_ = lean_array_fget_borrowed(v___y_2514_, v_mid_2512_);
v___x_2516_ = lean_array_fget_borrowed(v___y_2514_, v_hi_2497_);
v___x_2517_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2515_, v___x_2516_);
if (v___x_2517_ == 0)
{
lean_dec(v_mid_2512_);
v___y_2499_ = v___y_2514_;
goto v___jp_2498_;
}
else
{
lean_object* v___x_2518_; 
v___x_2518_ = lean_array_fswap(v___y_2514_, v_mid_2512_, v_hi_2497_);
lean_dec(v_mid_2512_);
v___y_2499_ = v___x_2518_;
goto v___jp_2498_;
}
}
v___jp_2519_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
v___x_2521_ = lean_array_fget_borrowed(v___y_2520_, v_hi_2497_);
v___x_2522_ = lean_array_fget_borrowed(v___y_2520_, v_lo_2496_);
v___x_2523_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2521_, v___x_2522_);
if (v___x_2523_ == 0)
{
v___y_2514_ = v___y_2520_;
goto v___jp_2513_;
}
else
{
lean_object* v___x_2524_; 
v___x_2524_ = lean_array_fswap(v___y_2520_, v_lo_2496_, v_hi_2497_);
v___y_2514_ = v___x_2524_;
goto v___jp_2513_;
}
}
}
v___jp_2498_:
{
lean_object* v_pivot_2500_; lean_object* v___x_2501_; lean_object* v_fst_2502_; lean_object* v_snd_2503_; uint8_t v___x_2504_; 
v_pivot_2500_ = lean_array_fget(v___y_2499_, v_hi_2497_);
lean_inc_n(v_lo_2496_, 2);
v___x_2501_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2497_, v_pivot_2500_, v___y_2499_, v_lo_2496_, v_lo_2496_);
lean_dec(v_pivot_2500_);
v_fst_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_fst_2502_);
v_snd_2503_ = lean_ctor_get(v___x_2501_, 1);
lean_inc(v_snd_2503_);
lean_dec_ref(v___x_2501_);
v___x_2504_ = lean_nat_dec_le(v_hi_2497_, v_fst_2502_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2505_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2494_, v_snd_2503_, v_lo_2496_, v_fst_2502_);
v___x_2506_ = lean_unsigned_to_nat(1u);
v___x_2507_ = lean_nat_add(v_fst_2502_, v___x_2506_);
lean_dec(v_fst_2502_);
v_as_2495_ = v___x_2505_;
v_lo_2496_ = v___x_2507_;
goto _start;
}
else
{
lean_dec(v_fst_2502_);
lean_dec(v_lo_2496_);
return v_snd_2503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object* v_n_2529_, lean_object* v_as_2530_, lean_object* v_lo_2531_, lean_object* v_hi_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2529_, v_as_2530_, v_lo_2531_, v_hi_2532_);
lean_dec(v_hi_2532_);
lean_dec(v_n_2529_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object* v_filterExport_2534_, lean_object* v_env_2535_, lean_object* v_as_2536_, size_t v_i_2537_, size_t v_stop_2538_, lean_object* v_b_2539_){
_start:
{
lean_object* v___y_2541_; uint8_t v___x_2545_; 
v___x_2545_ = lean_usize_dec_eq(v_i_2537_, v_stop_2538_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2546_; lean_object* v_fst_2547_; lean_object* v_snd_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; 
v___x_2546_ = lean_array_uget_borrowed(v_as_2536_, v_i_2537_);
v_fst_2547_ = lean_ctor_get(v___x_2546_, 0);
v_snd_2548_ = lean_ctor_get(v___x_2546_, 1);
lean_inc_ref(v_filterExport_2534_);
lean_inc(v_snd_2548_);
lean_inc(v_fst_2547_);
lean_inc_ref(v_env_2535_);
v___x_2549_ = lean_apply_3(v_filterExport_2534_, v_env_2535_, v_fst_2547_, v_snd_2548_);
v___x_2550_ = lean_unbox(v___x_2549_);
if (v___x_2550_ == 0)
{
v___y_2541_ = v_b_2539_;
goto v___jp_2540_;
}
else
{
lean_object* v___x_2551_; 
lean_inc(v___x_2546_);
v___x_2551_ = lean_array_push(v_b_2539_, v___x_2546_);
v___y_2541_ = v___x_2551_;
goto v___jp_2540_;
}
}
else
{
lean_dec_ref(v_env_2535_);
lean_dec_ref(v_filterExport_2534_);
return v_b_2539_;
}
v___jp_2540_:
{
size_t v___x_2542_; size_t v___x_2543_; 
v___x_2542_ = ((size_t)1ULL);
v___x_2543_ = lean_usize_add(v_i_2537_, v___x_2542_);
v_i_2537_ = v___x_2543_;
v_b_2539_ = v___y_2541_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object* v_filterExport_2552_, lean_object* v_env_2553_, lean_object* v_as_2554_, lean_object* v_i_2555_, lean_object* v_stop_2556_, lean_object* v_b_2557_){
_start:
{
size_t v_i_boxed_2558_; size_t v_stop_boxed_2559_; lean_object* v_res_2560_; 
v_i_boxed_2558_ = lean_unbox_usize(v_i_2555_);
lean_dec(v_i_2555_);
v_stop_boxed_2559_ = lean_unbox_usize(v_stop_2556_);
lean_dec(v_stop_2556_);
v_res_2560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2552_, v_env_2553_, v_as_2554_, v_i_boxed_2558_, v_stop_boxed_2559_, v_b_2557_);
lean_dec_ref(v_as_2554_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object* v_filterExport_2561_, uint8_t v_preserveOrder_2562_, lean_object* v_env_2563_, lean_object* v_x_2564_){
_start:
{
lean_object* v___y_2566_; 
if (v_preserveOrder_2562_ == 0)
{
lean_object* v_snd_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v_r_2579_; lean_object* v___x_2580_; lean_object* v___y_2582_; lean_object* v___y_2583_; uint8_t v___x_2585_; 
v_snd_2576_ = lean_ctor_get(v_x_2564_, 1);
lean_inc(v_snd_2576_);
lean_dec_ref(v_x_2564_);
v___x_2577_ = lean_unsigned_to_nat(0u);
v___x_2578_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v_r_2579_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_2578_, v_snd_2576_);
lean_dec(v_snd_2576_);
v___x_2580_ = lean_array_get_size(v_r_2579_);
v___x_2585_ = lean_nat_dec_eq(v___x_2580_, v___x_2577_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___y_2589_; uint8_t v___x_2591_; 
v___x_2586_ = lean_unsigned_to_nat(1u);
v___x_2587_ = lean_nat_sub(v___x_2580_, v___x_2586_);
v___x_2591_ = lean_nat_dec_le(v___x_2577_, v___x_2587_);
if (v___x_2591_ == 0)
{
lean_inc(v___x_2587_);
v___y_2589_ = v___x_2587_;
goto v___jp_2588_;
}
else
{
v___y_2589_ = v___x_2577_;
goto v___jp_2588_;
}
v___jp_2588_:
{
uint8_t v___x_2590_; 
v___x_2590_ = lean_nat_dec_le(v___y_2589_, v___x_2587_);
if (v___x_2590_ == 0)
{
lean_dec(v___x_2587_);
lean_inc(v___y_2589_);
v___y_2582_ = v___y_2589_;
v___y_2583_ = v___y_2589_;
goto v___jp_2581_;
}
else
{
v___y_2582_ = v___y_2589_;
v___y_2583_ = v___x_2587_;
goto v___jp_2581_;
}
}
}
else
{
v___y_2566_ = v_r_2579_;
goto v___jp_2565_;
}
v___jp_2581_:
{
lean_object* v___x_2584_; 
v___x_2584_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_2580_, v_r_2579_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2583_);
v___y_2566_ = v___x_2584_;
goto v___jp_2565_;
}
}
else
{
lean_object* v_fst_2592_; lean_object* v_snd_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v_fst_2592_ = lean_ctor_get(v_x_2564_, 0);
lean_inc(v_fst_2592_);
v_snd_2593_ = lean_ctor_get(v_x_2564_, 1);
lean_inc(v_snd_2593_);
lean_dec_ref(v_x_2564_);
v___x_2594_ = lean_array_mk(v_fst_2592_);
v___x_2595_ = l_Array_reverse___redArg(v___x_2594_);
v___x_2596_ = lean_unsigned_to_nat(0u);
v___x_2597_ = lean_array_get_size(v___x_2595_);
v___x_2598_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2593_, v___x_2595_, v___x_2596_, v___x_2597_);
lean_dec_ref(v___x_2595_);
lean_dec(v_snd_2593_);
v___y_2566_ = v___x_2598_;
goto v___jp_2565_;
}
v___jp_2565_:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v___x_2567_ = lean_unsigned_to_nat(0u);
v___x_2568_ = lean_array_get_size(v___y_2566_);
v___x_2569_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2570_ = lean_nat_dec_lt(v___x_2567_, v___x_2568_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; 
lean_dec_ref(v_env_2563_);
lean_dec_ref(v_filterExport_2561_);
v___x_2571_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2569_);
lean_ctor_set(v___x_2571_, 1, v___x_2569_);
lean_ctor_set(v___x_2571_, 2, v___y_2566_);
return v___x_2571_;
}
else
{
size_t v___x_2572_; size_t v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2572_ = ((size_t)0ULL);
v___x_2573_ = lean_usize_of_nat(v___x_2568_);
v___x_2574_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2561_, v_env_2563_, v___y_2566_, v___x_2572_, v___x_2573_, v___x_2569_);
lean_inc_ref(v___x_2574_);
v___x_2575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
lean_ctor_set(v___x_2575_, 2, v___y_2566_);
return v___x_2575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object* v_filterExport_2599_, lean_object* v_preserveOrder_2600_, lean_object* v_env_2601_, lean_object* v_x_2602_){
_start:
{
uint8_t v_preserveOrder_boxed_2603_; lean_object* v_res_2604_; 
v_preserveOrder_boxed_2603_ = lean_unbox(v_preserveOrder_2600_);
v_res_2604_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2599_, v_preserveOrder_boxed_2603_, v_env_2601_, v_x_2602_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object* v_x_2614_){
_start:
{
lean_object* v_snd_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2629_; 
v_snd_2615_ = lean_ctor_get(v_x_2614_, 1);
v_isSharedCheck_2629_ = !lean_is_exclusive(v_x_2614_);
if (v_isSharedCheck_2629_ == 0)
{
lean_object* v_unused_2630_; 
v_unused_2630_ = lean_ctor_get(v_x_2614_, 0);
lean_dec(v_unused_2630_);
v___x_2617_ = v_x_2614_;
v_isShared_2618_ = v_isSharedCheck_2629_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_snd_2615_);
lean_dec(v_x_2614_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2629_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___y_2621_; 
v___x_2619_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2615_) == 0)
{
lean_object* v_size_2627_; 
v_size_2627_ = lean_ctor_get(v_snd_2615_, 0);
lean_inc(v_size_2627_);
lean_dec_ref_known(v_snd_2615_, 5);
v___y_2621_ = v_size_2627_;
goto v___jp_2620_;
}
else
{
lean_object* v___x_2628_; 
v___x_2628_ = lean_unsigned_to_nat(0u);
v___y_2621_ = v___x_2628_;
goto v___jp_2620_;
}
v___jp_2620_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2622_ = l_Nat_reprFast(v___y_2621_);
v___x_2623_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set_tag(v___x_2617_, 5);
lean_ctor_set(v___x_2617_, 1, v___x_2623_);
lean_ctor_set(v___x_2617_, 0, v___x_2619_);
v___x_2625_ = v___x_2617_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object* v_x_2631_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object* v_x_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_Lean_registerParametricAttributeExt___redArg___lam__3(v_x_2633_);
lean_dec_ref(v_x_2633_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object* v___x_2635_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2635_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object* v___x_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2638_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object* v___x_2641_, lean_object* v_x_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2641_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object* v___x_2646_, lean_object* v_x_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2646_, v_x_2647_, v___y_2648_);
lean_dec_ref(v___y_2648_);
lean_dec_ref(v_x_2647_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object* v_ref_2661_, uint8_t v_preserveOrder_2662_, lean_object* v_filterExport_2663_, uint8_t v_logWrites_2664_){
_start:
{
lean_object* v___f_2666_; lean_object* v___x_2667_; lean_object* v___f_2668_; lean_object* v___f_2669_; lean_object* v___f_2670_; lean_object* v___f_2671_; lean_object* v___f_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___f_2666_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__0));
v___x_2667_ = lean_box(v_preserveOrder_2662_);
v___f_2668_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2668_, 0, v_filterExport_2663_);
lean_closure_set(v___f_2668_, 1, v___x_2667_);
v___f_2669_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__1));
v___f_2670_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__2));
v___f_2671_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__4));
v___f_2672_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__5));
v___x_2673_ = lean_box(2);
v___x_2674_ = lean_box(0);
v___x_2675_ = 0;
v___x_2676_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2676_, 0, v_ref_2661_);
lean_ctor_set(v___x_2676_, 1, v___f_2671_);
lean_ctor_set(v___x_2676_, 2, v___f_2672_);
lean_ctor_set(v___x_2676_, 3, v___f_2666_);
lean_ctor_set(v___x_2676_, 4, v___f_2668_);
lean_ctor_set(v___x_2676_, 5, v___f_2669_);
lean_ctor_set(v___x_2676_, 6, v___x_2673_);
lean_ctor_set(v___x_2676_, 7, v___x_2674_);
lean_ctor_set_uint8(v___x_2676_, sizeof(void*)*8, v___x_2675_);
lean_ctor_set_uint8(v___x_2676_, sizeof(void*)*8 + 1, v_logWrites_2664_);
v___x_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2676_);
lean_ctor_set(v___x_2677_, 1, v___f_2670_);
v___x_2678_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object* v_ref_2679_, lean_object* v_preserveOrder_2680_, lean_object* v_filterExport_2681_, lean_object* v_logWrites_2682_, lean_object* v_a_2683_){
_start:
{
uint8_t v_preserveOrder_boxed_2684_; uint8_t v_logWrites_boxed_2685_; lean_object* v_res_2686_; 
v_preserveOrder_boxed_2684_ = lean_unbox(v_preserveOrder_2680_);
v_logWrites_boxed_2685_ = lean_unbox(v_logWrites_2682_);
v_res_2686_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2679_, v_preserveOrder_boxed_2684_, v_filterExport_2681_, v_logWrites_boxed_2685_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object* v_00_u03b1_2687_, lean_object* v_ref_2688_, uint8_t v_preserveOrder_2689_, lean_object* v_filterExport_2690_, uint8_t v_logWrites_2691_){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2688_, v_preserveOrder_2689_, v_filterExport_2690_, v_logWrites_2691_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object* v_00_u03b1_2694_, lean_object* v_ref_2695_, lean_object* v_preserveOrder_2696_, lean_object* v_filterExport_2697_, lean_object* v_logWrites_2698_, lean_object* v_a_2699_){
_start:
{
uint8_t v_preserveOrder_boxed_2700_; uint8_t v_logWrites_boxed_2701_; lean_object* v_res_2702_; 
v_preserveOrder_boxed_2700_ = lean_unbox(v_preserveOrder_2696_);
v_logWrites_boxed_2701_ = lean_unbox(v_logWrites_2698_);
v_res_2702_ = l_Lean_registerParametricAttributeExt(v_00_u03b1_2694_, v_ref_2695_, v_preserveOrder_boxed_2700_, v_filterExport_2697_, v_logWrites_boxed_2701_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object* v_00_u03b1_2703_, lean_object* v_filterExport_2704_, lean_object* v_env_2705_, lean_object* v_as_2706_, size_t v_i_2707_, size_t v_stop_2708_, lean_object* v_b_2709_){
_start:
{
lean_object* v___x_2710_; 
v___x_2710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2704_, v_env_2705_, v_as_2706_, v_i_2707_, v_stop_2708_, v_b_2709_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object* v_00_u03b1_2711_, lean_object* v_filterExport_2712_, lean_object* v_env_2713_, lean_object* v_as_2714_, lean_object* v_i_2715_, lean_object* v_stop_2716_, lean_object* v_b_2717_){
_start:
{
size_t v_i_boxed_2718_; size_t v_stop_boxed_2719_; lean_object* v_res_2720_; 
v_i_boxed_2718_ = lean_unbox_usize(v_i_2715_);
lean_dec(v_i_2715_);
v_stop_boxed_2719_ = lean_unbox_usize(v_stop_2716_);
lean_dec(v_stop_2716_);
v_res_2720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(v_00_u03b1_2711_, v_filterExport_2712_, v_env_2713_, v_as_2714_, v_i_boxed_2718_, v_stop_boxed_2719_, v_b_2717_);
lean_dec_ref(v_as_2714_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object* v_init_2721_, lean_object* v_t_2722_){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2721_, v_t_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object* v_init_2724_, lean_object* v_t_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(v_init_2724_, v_t_2725_);
lean_dec(v_t_2725_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object* v_00_u03b1_2727_, lean_object* v_init_2728_, lean_object* v_t_2729_){
_start:
{
lean_object* v___x_2730_; 
v___x_2730_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2728_, v_t_2729_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object* v_00_u03b1_2731_, lean_object* v_init_2732_, lean_object* v_t_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(v_00_u03b1_2731_, v_init_2732_, v_t_2733_);
lean_dec(v_t_2733_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object* v_00_u03b1_2735_, lean_object* v_n_2736_, lean_object* v_as_2737_, lean_object* v_lo_2738_, lean_object* v_hi_2739_, lean_object* v_w_2740_, lean_object* v_hlo_2741_, lean_object* v_hhi_2742_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2736_, v_as_2737_, v_lo_2738_, v_hi_2739_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object* v_00_u03b1_2744_, lean_object* v_n_2745_, lean_object* v_as_2746_, lean_object* v_lo_2747_, lean_object* v_hi_2748_, lean_object* v_w_2749_, lean_object* v_hlo_2750_, lean_object* v_hhi_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(v_00_u03b1_2744_, v_n_2745_, v_as_2746_, v_lo_2747_, v_hi_2748_, v_w_2749_, v_hlo_2750_, v_hhi_2751_);
lean_dec(v_hi_2748_);
lean_dec(v_n_2745_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object* v_00_u03b1_2753_, lean_object* v_snd_2754_, lean_object* v_as_2755_, lean_object* v_start_2756_, lean_object* v_stop_2757_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2754_, v_as_2755_, v_start_2756_, v_stop_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object* v_00_u03b1_2759_, lean_object* v_snd_2760_, lean_object* v_as_2761_, lean_object* v_start_2762_, lean_object* v_stop_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(v_00_u03b1_2759_, v_snd_2760_, v_as_2761_, v_start_2762_, v_stop_2763_);
lean_dec(v_stop_2763_);
lean_dec(v_start_2762_);
lean_dec_ref(v_as_2761_);
lean_dec(v_snd_2760_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object* v_00_u03b1_2765_, lean_object* v_init_2766_, lean_object* v_x_2767_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2766_, v_x_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2769_, lean_object* v_init_2770_, lean_object* v_x_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(v_00_u03b1_2769_, v_init_2770_, v_x_2771_);
lean_dec(v_x_2771_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object* v_00_u03b1_2773_, lean_object* v_n_2774_, lean_object* v_lo_2775_, lean_object* v_hi_2776_, lean_object* v_hhi_2777_, lean_object* v_pivot_2778_, lean_object* v_as_2779_, lean_object* v_i_2780_, lean_object* v_k_2781_, lean_object* v_ilo_2782_, lean_object* v_ik_2783_, lean_object* v_w_2784_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2776_, v_pivot_2778_, v_as_2779_, v_i_2780_, v_k_2781_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2786_, lean_object* v_n_2787_, lean_object* v_lo_2788_, lean_object* v_hi_2789_, lean_object* v_hhi_2790_, lean_object* v_pivot_2791_, lean_object* v_as_2792_, lean_object* v_i_2793_, lean_object* v_k_2794_, lean_object* v_ilo_2795_, lean_object* v_ik_2796_, lean_object* v_w_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(v_00_u03b1_2786_, v_n_2787_, v_lo_2788_, v_hi_2789_, v_hhi_2790_, v_pivot_2791_, v_as_2792_, v_i_2793_, v_k_2794_, v_ilo_2795_, v_ik_2796_, v_w_2797_);
lean_dec_ref(v_pivot_2791_);
lean_dec(v_hi_2789_);
lean_dec(v_lo_2788_);
lean_dec(v_n_2787_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object* v_00_u03b1_2799_, lean_object* v_snd_2800_, lean_object* v_as_2801_, size_t v_i_2802_, size_t v_stop_2803_, lean_object* v_b_2804_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2800_, v_as_2801_, v_i_2802_, v_stop_2803_, v_b_2804_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2806_, lean_object* v_snd_2807_, lean_object* v_as_2808_, lean_object* v_i_2809_, lean_object* v_stop_2810_, lean_object* v_b_2811_){
_start:
{
size_t v_i_boxed_2812_; size_t v_stop_boxed_2813_; lean_object* v_res_2814_; 
v_i_boxed_2812_ = lean_unbox_usize(v_i_2809_);
lean_dec(v_i_2809_);
v_stop_boxed_2813_ = lean_unbox_usize(v_stop_2810_);
lean_dec(v_stop_2810_);
v_res_2814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(v_00_u03b1_2806_, v_snd_2807_, v_as_2808_, v_i_boxed_2812_, v_stop_boxed_2813_, v_b_2811_);
lean_dec_ref(v_as_2808_);
lean_dec(v_snd_2807_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object* v_env_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v___x_2818_; lean_object* v_nextMacroScope_2819_; lean_object* v_ngen_2820_; lean_object* v_auxDeclNGen_2821_; lean_object* v_traceState_2822_; lean_object* v_recordedDeps_2823_; lean_object* v_messages_2824_; lean_object* v_infoState_2825_; lean_object* v_snapshotTasks_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2837_; 
v___x_2818_ = lean_st_ref_take(v___y_2816_);
v_nextMacroScope_2819_ = lean_ctor_get(v___x_2818_, 1);
v_ngen_2820_ = lean_ctor_get(v___x_2818_, 2);
v_auxDeclNGen_2821_ = lean_ctor_get(v___x_2818_, 3);
v_traceState_2822_ = lean_ctor_get(v___x_2818_, 4);
v_recordedDeps_2823_ = lean_ctor_get(v___x_2818_, 6);
v_messages_2824_ = lean_ctor_get(v___x_2818_, 7);
v_infoState_2825_ = lean_ctor_get(v___x_2818_, 8);
v_snapshotTasks_2826_ = lean_ctor_get(v___x_2818_, 9);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2837_ == 0)
{
lean_object* v_unused_2838_; lean_object* v_unused_2839_; 
v_unused_2838_ = lean_ctor_get(v___x_2818_, 5);
lean_dec(v_unused_2838_);
v_unused_2839_ = lean_ctor_get(v___x_2818_, 0);
lean_dec(v_unused_2839_);
v___x_2828_ = v___x_2818_;
v_isShared_2829_ = v_isSharedCheck_2837_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_snapshotTasks_2826_);
lean_inc(v_infoState_2825_);
lean_inc(v_messages_2824_);
lean_inc(v_recordedDeps_2823_);
lean_inc(v_traceState_2822_);
lean_inc(v_auxDeclNGen_2821_);
lean_inc(v_ngen_2820_);
lean_inc(v_nextMacroScope_2819_);
lean_dec(v___x_2818_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2837_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2833_; 
v___x_2830_ = lean_box(0);
v___x_2831_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 5, v___x_2831_);
lean_ctor_set(v___x_2828_, 0, v_env_2815_);
v___x_2833_ = v___x_2828_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_env_2815_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_nextMacroScope_2819_);
lean_ctor_set(v_reuseFailAlloc_2836_, 2, v_ngen_2820_);
lean_ctor_set(v_reuseFailAlloc_2836_, 3, v_auxDeclNGen_2821_);
lean_ctor_set(v_reuseFailAlloc_2836_, 4, v_traceState_2822_);
lean_ctor_set(v_reuseFailAlloc_2836_, 5, v___x_2831_);
lean_ctor_set(v_reuseFailAlloc_2836_, 6, v_recordedDeps_2823_);
lean_ctor_set(v_reuseFailAlloc_2836_, 7, v_messages_2824_);
lean_ctor_set(v_reuseFailAlloc_2836_, 8, v_infoState_2825_);
lean_ctor_set(v_reuseFailAlloc_2836_, 9, v_snapshotTasks_2826_);
v___x_2833_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = lean_st_ref_put(v___y_2816_, v___x_2833_);
v___x_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2830_);
return v___x_2835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object* v_env_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2840_, v___y_2841_);
lean_dec(v___y_2841_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object* v_env_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2844_, v___y_2846_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object* v_env_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(v_env_2849_, v___y_2850_, v___y_2851_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object* v_addEntryFn_2854_, lean_object* v___x_2855_, lean_object* v_s_2856_){
_start:
{
lean_object* v_importedEntries_2857_; lean_object* v_state_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2866_; 
v_importedEntries_2857_ = lean_ctor_get(v_s_2856_, 0);
v_state_2858_ = lean_ctor_get(v_s_2856_, 1);
v_isSharedCheck_2866_ = !lean_is_exclusive(v_s_2856_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2860_ = v_s_2856_;
v_isShared_2861_ = v_isSharedCheck_2866_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_state_2858_);
lean_inc(v_importedEntries_2857_);
lean_dec(v_s_2856_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2866_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v_state_2862_; lean_object* v___x_2864_; 
v_state_2862_ = lean_apply_2(v_addEntryFn_2854_, v_state_2858_, v___x_2855_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 1, v_state_2862_);
v___x_2864_ = v___x_2860_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_importedEntries_2857_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v_state_2862_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object* v_afterSet_2867_, lean_object* v_getParam_2868_, lean_object* v_ext_2869_, lean_object* v_toAttributeImplCore_2870_, lean_object* v_decl_2871_, lean_object* v_stx_2872_, uint8_t v_kind_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v_nextMacroScope_2882_; lean_object* v_ngen_2883_; lean_object* v_auxDeclNGen_2884_; lean_object* v_traceState_2885_; lean_object* v_recordedDeps_2886_; lean_object* v_messages_2887_; lean_object* v_infoState_2888_; lean_object* v_snapshotTasks_2889_; lean_object* v___y_2890_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; uint8_t v___x_2939_; uint8_t v___x_2940_; 
v___x_2939_ = 0;
v___x_2940_ = l_Lean_instBEqAttributeKind_beq(v_kind_2873_, v___x_2939_);
if (v___x_2940_ == 0)
{
lean_object* v_name_2941_; lean_object* v___x_2942_; 
lean_dec(v_stx_2872_);
lean_dec(v_decl_2871_);
lean_dec_ref(v_ext_2869_);
lean_dec_ref(v_getParam_2868_);
lean_dec_ref(v_afterSet_2867_);
v_name_2941_ = lean_ctor_get(v_toAttributeImplCore_2870_, 1);
lean_inc(v_name_2941_);
lean_dec_ref(v_toAttributeImplCore_2870_);
v___x_2942_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2941_, v_kind_2873_, v___y_2874_, v___y_2875_);
return v___x_2942_;
}
else
{
goto v___jp_2933_;
}
v___jp_2877_:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2891_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_2892_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2892_, 0, v___y_2890_);
lean_ctor_set(v___x_2892_, 1, v_nextMacroScope_2882_);
lean_ctor_set(v___x_2892_, 2, v_ngen_2883_);
lean_ctor_set(v___x_2892_, 3, v_auxDeclNGen_2884_);
lean_ctor_set(v___x_2892_, 4, v_traceState_2885_);
lean_ctor_set(v___x_2892_, 5, v___x_2891_);
lean_ctor_set(v___x_2892_, 6, v_recordedDeps_2886_);
lean_ctor_set(v___x_2892_, 7, v_messages_2887_);
lean_ctor_set(v___x_2892_, 8, v_infoState_2888_);
lean_ctor_set(v___x_2892_, 9, v_snapshotTasks_2889_);
v___x_2893_ = lean_st_ref_put(v___y_2879_, v___x_2892_);
lean_inc(v___y_2879_);
lean_inc_ref(v___y_2881_);
v___x_2894_ = lean_apply_5(v_afterSet_2867_, v_decl_2871_, v___y_2880_, v___y_2881_, v___y_2879_, lean_box(0));
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_dec_ref(v___y_2878_);
return v___x_2894_;
}
else
{
lean_object* v_a_2895_; uint8_t v___x_2896_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
v___x_2896_ = l_Lean_Exception_isInterrupt(v_a_2895_);
if (v___x_2896_ == 0)
{
uint8_t v___x_2897_; 
v___x_2897_ = l_Lean_Exception_isRuntime(v_a_2895_);
if (v___x_2897_ == 0)
{
lean_object* v___x_2898_; 
lean_dec_ref_known(v___x_2894_, 1);
v___x_2898_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v___y_2878_, v___y_2879_);
return v___x_2898_;
}
else
{
lean_dec_ref(v___y_2878_);
return v___x_2894_;
}
}
else
{
lean_dec(v_a_2895_);
lean_dec_ref(v___y_2878_);
return v___x_2894_;
}
}
}
v___jp_2899_:
{
lean_object* v___x_2903_; 
lean_inc(v___y_2902_);
lean_inc_ref(v___y_2901_);
lean_inc(v_decl_2871_);
v___x_2903_ = lean_apply_5(v_getParam_2868_, v_decl_2871_, v_stx_2872_, v___y_2901_, v___y_2902_, lean_box(0));
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2905_; lean_object* v_toEnvExtension_2906_; lean_object* v_env_2907_; lean_object* v_nextMacroScope_2908_; lean_object* v_ngen_2909_; lean_object* v_auxDeclNGen_2910_; lean_object* v_traceState_2911_; lean_object* v_recordedDeps_2912_; lean_object* v_messages_2913_; lean_object* v_infoState_2914_; lean_object* v_snapshotTasks_2915_; lean_object* v_addEntryFn_2916_; lean_object* v_asyncMode_2917_; uint8_t v_logWrites_2918_; lean_object* v___x_2919_; lean_object* v___f_2920_; uint8_t v___x_2921_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc_n(v_a_2904_, 2);
lean_dec_ref_known(v___x_2903_, 1);
v___x_2905_ = lean_st_ref_take(v___y_2902_);
v_toEnvExtension_2906_ = lean_ctor_get(v_ext_2869_, 0);
lean_inc_ref(v_toEnvExtension_2906_);
v_env_2907_ = lean_ctor_get(v___x_2905_, 0);
lean_inc_ref(v_env_2907_);
v_nextMacroScope_2908_ = lean_ctor_get(v___x_2905_, 1);
lean_inc(v_nextMacroScope_2908_);
v_ngen_2909_ = lean_ctor_get(v___x_2905_, 2);
lean_inc_ref(v_ngen_2909_);
v_auxDeclNGen_2910_ = lean_ctor_get(v___x_2905_, 3);
lean_inc_ref(v_auxDeclNGen_2910_);
v_traceState_2911_ = lean_ctor_get(v___x_2905_, 4);
lean_inc_ref(v_traceState_2911_);
v_recordedDeps_2912_ = lean_ctor_get(v___x_2905_, 6);
lean_inc_ref(v_recordedDeps_2912_);
v_messages_2913_ = lean_ctor_get(v___x_2905_, 7);
lean_inc_ref(v_messages_2913_);
v_infoState_2914_ = lean_ctor_get(v___x_2905_, 8);
lean_inc_ref(v_infoState_2914_);
v_snapshotTasks_2915_ = lean_ctor_get(v___x_2905_, 9);
lean_inc_ref(v_snapshotTasks_2915_);
lean_dec(v___x_2905_);
v_addEntryFn_2916_ = lean_ctor_get(v_ext_2869_, 3);
lean_inc(v_addEntryFn_2916_);
lean_dec_ref(v_ext_2869_);
v_asyncMode_2917_ = lean_ctor_get(v_toEnvExtension_2906_, 2);
lean_inc(v_asyncMode_2917_);
v_logWrites_2918_ = lean_ctor_get_uint8(v_toEnvExtension_2906_, sizeof(void*)*6);
lean_inc(v_decl_2871_);
v___x_2919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2919_, 0, v_decl_2871_);
lean_ctor_set(v___x_2919_, 1, v_a_2904_);
v___f_2920_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2920_, 0, v_addEntryFn_2916_);
lean_closure_set(v___f_2920_, 1, v___x_2919_);
v___x_2921_ = 1;
if (v_logWrites_2918_ == 0)
{
lean_object* v___x_2922_; 
lean_inc(v_decl_2871_);
v___x_2922_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2906_, v_env_2907_, v___f_2920_, v_asyncMode_2917_, v_decl_2871_, v___x_2921_);
lean_dec(v_asyncMode_2917_);
v___y_2878_ = v___y_2900_;
v___y_2879_ = v___y_2902_;
v___y_2880_ = v_a_2904_;
v___y_2881_ = v___y_2901_;
v_nextMacroScope_2882_ = v_nextMacroScope_2908_;
v_ngen_2883_ = v_ngen_2909_;
v_auxDeclNGen_2884_ = v_auxDeclNGen_2910_;
v_traceState_2885_ = v_traceState_2911_;
v_recordedDeps_2886_ = v_recordedDeps_2912_;
v_messages_2887_ = v_messages_2913_;
v_infoState_2888_ = v_infoState_2914_;
v_snapshotTasks_2889_ = v_snapshotTasks_2915_;
v___y_2890_ = v___x_2922_;
goto v___jp_2877_;
}
else
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
lean_inc_n(v_decl_2871_, 2);
v___x_2923_ = l_Lean_Environment_logDeclChange(v_env_2907_, v_decl_2871_);
v___x_2924_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2906_, v___x_2923_, v___f_2920_, v_asyncMode_2917_, v_decl_2871_, v___x_2921_);
lean_dec(v_asyncMode_2917_);
v___y_2878_ = v___y_2900_;
v___y_2879_ = v___y_2902_;
v___y_2880_ = v_a_2904_;
v___y_2881_ = v___y_2901_;
v_nextMacroScope_2882_ = v_nextMacroScope_2908_;
v_ngen_2883_ = v_ngen_2909_;
v_auxDeclNGen_2884_ = v_auxDeclNGen_2910_;
v_traceState_2885_ = v_traceState_2911_;
v_recordedDeps_2886_ = v_recordedDeps_2912_;
v_messages_2887_ = v_messages_2913_;
v_infoState_2888_ = v_infoState_2914_;
v_snapshotTasks_2889_ = v_snapshotTasks_2915_;
v___y_2890_ = v___x_2924_;
goto v___jp_2877_;
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec_ref(v___y_2900_);
lean_dec(v_decl_2871_);
lean_dec_ref(v_ext_2869_);
lean_dec_ref(v_afterSet_2867_);
v_a_2925_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2903_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2903_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
v___jp_2933_:
{
lean_object* v___x_2934_; lean_object* v_env_2935_; lean_object* v___x_2936_; 
v___x_2934_ = lean_st_ref_get(v___y_2875_);
v_env_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc_ref(v_env_2935_);
lean_dec(v___x_2934_);
v___x_2936_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2935_, v_decl_2871_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_dec_ref(v_toAttributeImplCore_2870_);
v___y_2900_ = v_env_2935_;
v___y_2901_ = v___y_2874_;
v___y_2902_ = v___y_2875_;
goto v___jp_2899_;
}
else
{
lean_object* v_name_2937_; lean_object* v___x_2938_; 
lean_dec_ref_known(v___x_2936_, 1);
lean_dec_ref(v_env_2935_);
lean_dec(v_stx_2872_);
lean_dec_ref(v_ext_2869_);
lean_dec_ref(v_getParam_2868_);
lean_dec_ref(v_afterSet_2867_);
v_name_2937_ = lean_ctor_get(v_toAttributeImplCore_2870_, 1);
lean_inc(v_name_2937_);
lean_dec_ref(v_toAttributeImplCore_2870_);
v___x_2938_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2937_, v_decl_2871_, v___y_2874_, v___y_2875_);
return v___x_2938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object* v_afterSet_2943_, lean_object* v_getParam_2944_, lean_object* v_ext_2945_, lean_object* v_toAttributeImplCore_2946_, lean_object* v_decl_2947_, lean_object* v_stx_2948_, lean_object* v_kind_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
uint8_t v_kind_boxed_2953_; lean_object* v_res_2954_; 
v_kind_boxed_2953_ = lean_unbox(v_kind_2949_);
v_res_2954_ = l_Lean_registerParametricAttributeForExt___redArg___lam__1(v_afterSet_2943_, v_getParam_2944_, v_ext_2945_, v_toAttributeImplCore_2946_, v_decl_2947_, v_stx_2948_, v_kind_boxed_2953_, v___y_2950_, v___y_2951_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__2(lean_object* v_toAttributeImplCore_2955_, lean_object* v_decl_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
lean_object* v_name_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_name_2960_ = lean_ctor_get(v_toAttributeImplCore_2955_, 1);
lean_inc(v_name_2960_);
lean_dec_ref(v_toAttributeImplCore_2955_);
v___x_2961_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_2962_ = l_Lean_MessageData_ofName(v_name_2960_);
v___x_2963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2961_);
lean_ctor_set(v___x_2963_, 1, v___x_2962_);
v___x_2964_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_2965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2963_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
v___x_2966_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2965_, v___y_2957_, v___y_2958_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__2___boxed(lean_object* v_toAttributeImplCore_2967_, lean_object* v_decl_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Lean_registerParametricAttributeForExt___redArg___lam__2(v_toAttributeImplCore_2967_, v_decl_2968_, v___y_2969_, v___y_2970_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v_decl_2968_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object* v_impl_2973_, lean_object* v_ext_2974_){
_start:
{
lean_object* v_toAttributeImplCore_2976_; lean_object* v_getParam_2977_; lean_object* v_afterSet_2978_; uint8_t v_preserveOrder_2979_; lean_object* v___f_2980_; lean_object* v___f_2981_; lean_object* v_attrImpl_2982_; lean_object* v___x_2983_; 
v_toAttributeImplCore_2976_ = lean_ctor_get(v_impl_2973_, 0);
lean_inc_ref_n(v_toAttributeImplCore_2976_, 3);
v_getParam_2977_ = lean_ctor_get(v_impl_2973_, 1);
lean_inc_ref(v_getParam_2977_);
v_afterSet_2978_ = lean_ctor_get(v_impl_2973_, 2);
lean_inc_ref(v_afterSet_2978_);
v_preserveOrder_2979_ = lean_ctor_get_uint8(v_impl_2973_, sizeof(void*)*4);
lean_dec_ref(v_impl_2973_);
lean_inc_ref(v_ext_2974_);
v___f_2980_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_2980_, 0, v_afterSet_2978_);
lean_closure_set(v___f_2980_, 1, v_getParam_2977_);
lean_closure_set(v___f_2980_, 2, v_ext_2974_);
lean_closure_set(v___f_2980_, 3, v_toAttributeImplCore_2976_);
v___f_2981_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__2___boxed), 5, 1);
lean_closure_set(v___f_2981_, 0, v_toAttributeImplCore_2976_);
v_attrImpl_2982_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_attrImpl_2982_, 0, v_toAttributeImplCore_2976_);
lean_ctor_set(v_attrImpl_2982_, 1, v___f_2980_);
lean_ctor_set(v_attrImpl_2982_, 2, v___f_2981_);
lean_inc_ref(v_attrImpl_2982_);
v___x_2983_ = l_Lean_registerBuiltinAttribute(v_attrImpl_2982_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2991_; 
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_2991_ == 0)
{
lean_object* v_unused_2992_; 
v_unused_2992_ = lean_ctor_get(v___x_2983_, 0);
lean_dec(v_unused_2992_);
v___x_2985_ = v___x_2983_;
v_isShared_2986_ = v_isSharedCheck_2991_;
goto v_resetjp_2984_;
}
else
{
lean_dec(v___x_2983_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2991_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2987_; lean_object* v___x_2989_; 
v___x_2987_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2987_, 0, v_attrImpl_2982_);
lean_ctor_set(v___x_2987_, 1, v_ext_2974_);
lean_ctor_set_uint8(v___x_2987_, sizeof(void*)*2, v_preserveOrder_2979_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 0, v___x_2987_);
v___x_2989_ = v___x_2985_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2987_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec_ref_known(v_attrImpl_2982_, 3);
lean_dec_ref(v_ext_2974_);
v_a_2993_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2983_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2983_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object* v_impl_3001_, lean_object* v_ext_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3001_, v_ext_3002_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object* v_00_u03b1_3005_, lean_object* v_impl_3006_, lean_object* v_ext_3007_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3006_, v_ext_3007_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object* v_00_u03b1_3010_, lean_object* v_impl_3011_, lean_object* v_ext_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Lean_registerParametricAttributeForExt(v_00_u03b1_3010_, v_impl_3011_, v_ext_3012_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_3015_){
_start:
{
lean_object* v_toAttributeImplCore_3017_; uint8_t v_preserveOrder_3018_; lean_object* v_filterExport_3019_; lean_object* v_ref_3020_; uint8_t v___x_3021_; lean_object* v___x_3022_; 
v_toAttributeImplCore_3017_ = lean_ctor_get(v_impl_3015_, 0);
v_preserveOrder_3018_ = lean_ctor_get_uint8(v_impl_3015_, sizeof(void*)*4);
v_filterExport_3019_ = lean_ctor_get(v_impl_3015_, 3);
v_ref_3020_ = lean_ctor_get(v_toAttributeImplCore_3017_, 0);
v___x_3021_ = 0;
lean_inc_ref(v_filterExport_3019_);
lean_inc(v_ref_3020_);
v___x_3022_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_3020_, v_preserveOrder_3018_, v_filterExport_3019_, v___x_3021_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v___x_3024_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref_known(v___x_3022_, 1);
v___x_3024_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3015_, v_a_3023_);
return v___x_3024_;
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec_ref(v_impl_3015_);
v_a_3025_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_3022_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3022_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Lean_registerParametricAttribute___redArg(v_impl_3033_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_3036_, lean_object* v_impl_3037_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Lean_registerParametricAttribute___redArg(v_impl_3037_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_3040_, lean_object* v_impl_3041_, lean_object* v_a_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lean_registerParametricAttribute(v_00_u03b1_3040_, v_impl_3041_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object* v_inst_3049_, lean_object* v_ext_3050_, uint8_t v_preserveOrder_3051_, lean_object* v_env_3052_, lean_object* v_decl_3053_){
_start:
{
lean_object* v___y_3055_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3067_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3052_, v_decl_3053_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_toEnvExtension_3068_; lean_object* v_asyncMode_3069_; lean_object* v___x_3070_; uint8_t v___x_3071_; lean_object* v___x_3072_; lean_object* v_snd_3073_; lean_object* v___x_3074_; 
lean_dec(v_inst_3049_);
v_toEnvExtension_3068_ = lean_ctor_get(v_ext_3050_, 0);
v_asyncMode_3069_ = lean_ctor_get(v_toEnvExtension_3068_, 2);
v___x_3070_ = lean_box(0);
v___x_3071_ = 0;
v___x_3072_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3066_, v_ext_3050_, v_env_3052_, v_asyncMode_3069_, v___x_3070_, v___x_3071_);
v_snd_3073_ = lean_ctor_get(v___x_3072_, 1);
lean_inc(v_snd_3073_);
lean_dec(v___x_3072_);
v___x_3074_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3073_, v_decl_3053_);
lean_dec(v_decl_3053_);
lean_dec(v_snd_3073_);
return v___x_3074_;
}
else
{
if (v_preserveOrder_3051_ == 0)
{
lean_object* v_val_3075_; uint8_t v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; uint8_t v___x_3080_; 
v_val_3075_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_val_3075_);
lean_dec_ref_known(v___x_3067_, 1);
v___x_3076_ = 0;
v___x_3077_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3066_, v_ext_3050_, v_env_3052_, v_val_3075_, v___x_3076_);
lean_dec(v_val_3075_);
lean_dec_ref(v_env_3052_);
v___x_3078_ = lean_unsigned_to_nat(0u);
v___x_3079_ = lean_array_get_size(v___x_3077_);
v___x_3080_ = lean_nat_dec_lt(v___x_3078_, v___x_3079_);
if (v___x_3080_ == 0)
{
lean_object* v___x_3081_; 
lean_dec_ref(v___x_3077_);
lean_dec(v_decl_3053_);
lean_dec(v_inst_3049_);
v___x_3081_ = lean_box(0);
return v___x_3081_;
}
else
{
lean_object* v___x_3082_; lean_object* v___x_3083_; uint8_t v___x_3084_; 
v___x_3082_ = lean_unsigned_to_nat(1u);
v___x_3083_ = lean_nat_sub(v___x_3079_, v___x_3082_);
v___x_3084_ = lean_nat_dec_le(v___x_3078_, v___x_3083_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; 
lean_dec(v___x_3083_);
lean_dec_ref(v___x_3077_);
lean_dec(v_decl_3053_);
lean_dec(v_inst_3049_);
v___x_3085_ = lean_box(0);
return v___x_3085_;
}
else
{
lean_object* v___f_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___f_3086_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
v___x_3087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3087_, 0, v_decl_3053_);
lean_ctor_set(v___x_3087_, 1, v_inst_3049_);
v___x_3088_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3089_ = l_Array_binSearchAux___redArg(v___f_3086_, v___x_3088_, v___x_3077_, v___x_3087_, v___x_3078_, v___x_3083_);
lean_dec_ref(v___x_3077_);
v___y_3055_ = v___x_3089_;
goto v___jp_3054_;
}
}
}
else
{
lean_object* v_val_3090_; uint8_t v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
lean_dec(v_inst_3049_);
v_val_3090_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_val_3090_);
lean_dec_ref_known(v___x_3067_, 1);
v___x_3091_ = 0;
v___x_3092_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3066_, v_ext_3050_, v_env_3052_, v_val_3090_, v___x_3091_);
lean_dec(v_val_3090_);
lean_dec_ref(v_env_3052_);
v___x_3093_ = l_Lean_findByName_x3f___redArg(v___x_3092_, v_decl_3053_);
lean_dec(v_decl_3053_);
lean_dec_ref(v___x_3092_);
v___y_3055_ = v___x_3093_;
goto v___jp_3054_;
}
}
v___jp_3054_:
{
if (lean_obj_tag(v___y_3055_) == 0)
{
lean_object* v___x_3056_; 
v___x_3056_ = lean_box(0);
return v___x_3056_;
}
else
{
lean_object* v_val_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3065_; 
v_val_3057_ = lean_ctor_get(v___y_3055_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___y_3055_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3059_ = v___y_3055_;
v_isShared_3060_ = v_isSharedCheck_3065_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_val_3057_);
lean_dec(v___y_3055_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3065_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v_snd_3061_; lean_object* v___x_3063_; 
v_snd_3061_ = lean_ctor_get(v_val_3057_, 1);
lean_inc(v_snd_3061_);
lean_dec(v_val_3057_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v_snd_3061_);
v___x_3063_ = v___x_3059_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_snd_3061_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object* v_inst_3094_, lean_object* v_ext_3095_, lean_object* v_preserveOrder_3096_, lean_object* v_env_3097_, lean_object* v_decl_3098_){
_start:
{
uint8_t v_preserveOrder_boxed_3099_; lean_object* v_res_3100_; 
v_preserveOrder_boxed_3099_ = lean_unbox(v_preserveOrder_3096_);
v_res_3100_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3094_, v_ext_3095_, v_preserveOrder_boxed_3099_, v_env_3097_, v_decl_3098_);
lean_dec_ref(v_ext_3095_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object* v_00_u03b1_3101_, lean_object* v_inst_3102_, lean_object* v_ext_3103_, uint8_t v_preserveOrder_3104_, lean_object* v_env_3105_, lean_object* v_decl_3106_){
_start:
{
lean_object* v___x_3107_; 
v___x_3107_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3102_, v_ext_3103_, v_preserveOrder_3104_, v_env_3105_, v_decl_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object* v_00_u03b1_3108_, lean_object* v_inst_3109_, lean_object* v_ext_3110_, lean_object* v_preserveOrder_3111_, lean_object* v_env_3112_, lean_object* v_decl_3113_){
_start:
{
uint8_t v_preserveOrder_boxed_3114_; lean_object* v_res_3115_; 
v_preserveOrder_boxed_3114_ = lean_unbox(v_preserveOrder_3111_);
v_res_3115_ = l_Lean_ParametricAttribute_getParamFromExt_x3f(v_00_u03b1_3108_, v_inst_3109_, v_ext_3110_, v_preserveOrder_boxed_3114_, v_env_3112_, v_decl_3113_);
lean_dec_ref(v_ext_3110_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3116_, lean_object* v_attr_3117_, lean_object* v_env_3118_, lean_object* v_decl_3119_){
_start:
{
lean_object* v_ext_3120_; uint8_t v_preserveOrder_3121_; lean_object* v___x_3122_; 
v_ext_3120_ = lean_ctor_get(v_attr_3117_, 1);
v_preserveOrder_3121_ = lean_ctor_get_uint8(v_attr_3117_, sizeof(void*)*2);
v___x_3122_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3116_, v_ext_3120_, v_preserveOrder_3121_, v_env_3118_, v_decl_3119_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3123_, lean_object* v_attr_3124_, lean_object* v_env_3125_, lean_object* v_decl_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3123_, v_attr_3124_, v_env_3125_, v_decl_3126_);
lean_dec_ref(v_attr_3124_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3128_, lean_object* v_inst_3129_, lean_object* v_attr_3130_, lean_object* v_env_3131_, lean_object* v_decl_3132_){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3129_, v_attr_3130_, v_env_3131_, v_decl_3132_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3134_, lean_object* v_inst_3135_, lean_object* v_attr_3136_, lean_object* v_env_3137_, lean_object* v_decl_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3134_, v_inst_3135_, v_attr_3136_, v_env_3137_, v_decl_3138_);
lean_dec_ref(v_attr_3136_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object* v_ext_3144_, lean_object* v_attr_3145_, lean_object* v_env_3146_, lean_object* v_decl_3147_, lean_object* v_param_3148_){
_start:
{
lean_object* v___x_3149_; 
v___x_3149_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3146_, v_decl_3147_);
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_object* v_toEnvExtension_3150_; lean_object* v_addEntryFn_3151_; lean_object* v_asyncMode_3152_; uint8_t v_logWrites_3153_; uint8_t v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v_snd_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3193_; 
v_toEnvExtension_3150_ = lean_ctor_get(v_ext_3144_, 0);
lean_inc_ref(v_toEnvExtension_3150_);
v_addEntryFn_3151_ = lean_ctor_get(v_ext_3144_, 3);
lean_inc(v_addEntryFn_3151_);
v_asyncMode_3152_ = lean_ctor_get(v_toEnvExtension_3150_, 2);
lean_inc(v_asyncMode_3152_);
v_logWrites_3153_ = lean_ctor_get_uint8(v_toEnvExtension_3150_, sizeof(void*)*6);
v___x_3154_ = 0;
v___x_3155_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3156_ = lean_box(0);
lean_inc_ref(v_env_3146_);
v___x_3157_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3155_, v_ext_3144_, v_env_3146_, v_asyncMode_3152_, v___x_3156_, v___x_3154_);
lean_dec_ref(v_ext_3144_);
v_snd_3158_ = lean_ctor_get(v___x_3157_, 1);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3193_ == 0)
{
lean_object* v_unused_3194_; 
v_unused_3194_ = lean_ctor_get(v___x_3157_, 0);
lean_dec(v_unused_3194_);
v___x_3160_ = v___x_3157_;
v_isShared_3161_ = v_isSharedCheck_3193_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_snd_3158_);
lean_dec(v___x_3157_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3193_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3162_; 
v___x_3162_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3158_, v_decl_3147_);
lean_dec(v_snd_3158_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v___x_3164_; 
lean_dec_ref(v_attr_3145_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 1, v_param_3148_);
lean_ctor_set(v___x_3160_, 0, v_decl_3147_);
v___x_3164_ = v___x_3160_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_decl_3147_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_param_3148_);
v___x_3164_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
lean_object* v___f_3165_; uint8_t v___x_3166_; 
v___f_3165_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3165_, 0, v_addEntryFn_3151_);
lean_closure_set(v___f_3165_, 1, v___x_3164_);
v___x_3166_ = 1;
if (v_logWrites_3153_ == 0)
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3167_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3150_, v_env_3146_, v___f_3165_, v_asyncMode_3152_, v___x_3156_, v___x_3166_);
lean_dec(v_asyncMode_3152_);
v___x_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
return v___x_3168_;
}
else
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
lean_inc_ref(v_toEnvExtension_3150_);
v___x_3169_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3150_, v_env_3146_);
lean_dec_ref(v_env_3146_);
v___x_3170_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3150_, v___x_3169_, v___f_3165_, v_asyncMode_3152_, v___x_3156_, v___x_3166_);
lean_dec(v_asyncMode_3152_);
v___x_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
return v___x_3171_;
}
}
}
else
{
lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3191_; 
lean_del_object(v___x_3160_);
lean_dec(v_asyncMode_3152_);
lean_dec(v_addEntryFn_3151_);
lean_dec_ref(v_toEnvExtension_3150_);
lean_dec(v_param_3148_);
lean_dec_ref(v_env_3146_);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3191_ == 0)
{
lean_object* v_unused_3192_; 
v_unused_3192_ = lean_ctor_get(v___x_3162_, 0);
lean_dec(v_unused_3192_);
v___x_3174_ = v___x_3162_;
v_isShared_3175_ = v_isSharedCheck_3191_;
goto v_resetjp_3173_;
}
else
{
lean_dec(v___x_3162_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3191_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v_toAttributeImplCore_3176_; lean_object* v_name_3177_; uint8_t v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3189_; 
v_toAttributeImplCore_3176_ = lean_ctor_get(v_attr_3145_, 0);
lean_inc_ref(v_toAttributeImplCore_3176_);
lean_dec_ref(v_attr_3145_);
v_name_3177_ = lean_ctor_get(v_toAttributeImplCore_3176_, 1);
lean_inc(v_name_3177_);
lean_dec_ref(v_toAttributeImplCore_3176_);
v___x_3178_ = 1;
v___x_3179_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3180_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3177_, v___x_3178_);
v___x_3181_ = lean_string_append(v___x_3179_, v___x_3180_);
lean_dec_ref(v___x_3180_);
v___x_3182_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3183_ = lean_string_append(v___x_3181_, v___x_3182_);
v___x_3184_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3147_, v___x_3178_);
v___x_3185_ = lean_string_append(v___x_3183_, v___x_3184_);
lean_dec_ref(v___x_3184_);
v___x_3186_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2));
v___x_3187_ = lean_string_append(v___x_3185_, v___x_3186_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set_tag(v___x_3174_, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3187_);
v___x_3189_ = v___x_3174_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
}
else
{
lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3213_; 
lean_dec(v_param_3148_);
lean_dec_ref(v_env_3146_);
lean_dec_ref(v_ext_3144_);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3213_ == 0)
{
lean_object* v_unused_3214_; 
v_unused_3214_ = lean_ctor_get(v___x_3149_, 0);
lean_dec(v_unused_3214_);
v___x_3196_ = v___x_3149_;
v_isShared_3197_ = v_isSharedCheck_3213_;
goto v_resetjp_3195_;
}
else
{
lean_dec(v___x_3149_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3213_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v_toAttributeImplCore_3198_; lean_object* v_name_3199_; uint8_t v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3211_; 
v_toAttributeImplCore_3198_ = lean_ctor_get(v_attr_3145_, 0);
lean_inc_ref(v_toAttributeImplCore_3198_);
lean_dec_ref(v_attr_3145_);
v_name_3199_ = lean_ctor_get(v_toAttributeImplCore_3198_, 1);
lean_inc(v_name_3199_);
lean_dec_ref(v_toAttributeImplCore_3198_);
v___x_3200_ = 1;
v___x_3201_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3202_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3199_, v___x_3200_);
v___x_3203_ = lean_string_append(v___x_3201_, v___x_3202_);
lean_dec_ref(v___x_3202_);
v___x_3204_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3205_ = lean_string_append(v___x_3203_, v___x_3204_);
v___x_3206_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3147_, v___x_3200_);
v___x_3207_ = lean_string_append(v___x_3205_, v___x_3206_);
lean_dec_ref(v___x_3206_);
v___x_3208_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3));
v___x_3209_ = lean_string_append(v___x_3207_, v___x_3208_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set_tag(v___x_3196_, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3209_);
v___x_3211_ = v___x_3196_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3209_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object* v_00_u03b1_3215_, lean_object* v_ext_3216_, lean_object* v_attr_3217_, lean_object* v_env_3218_, lean_object* v_decl_3219_, lean_object* v_param_3220_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3216_, v_attr_3217_, v_env_3218_, v_decl_3219_, v_param_3220_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3222_, lean_object* v_env_3223_, lean_object* v_decl_3224_, lean_object* v_param_3225_){
_start:
{
lean_object* v_attr_3226_; lean_object* v_ext_3227_; lean_object* v___x_3228_; 
v_attr_3226_ = lean_ctor_get(v_attr_3222_, 0);
lean_inc_ref(v_attr_3226_);
v_ext_3227_ = lean_ctor_get(v_attr_3222_, 1);
lean_inc_ref(v_ext_3227_);
lean_dec_ref(v_attr_3222_);
v___x_3228_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3227_, v_attr_3226_, v_env_3223_, v_decl_3224_, v_param_3225_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3229_, lean_object* v_attr_3230_, lean_object* v_env_3231_, lean_object* v_decl_3232_, lean_object* v_param_3233_){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3230_, v_env_3231_, v_decl_3232_, v_param_3233_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(lean_object* v_x_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3238_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3238_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0___boxed(lean_object* v_x_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(v_x_3240_, v___y_3241_);
lean_dec_ref(v___y_3241_);
lean_dec_ref(v_x_3240_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(lean_object* v_s_3244_, lean_object* v_x_3245_){
_start:
{
lean_inc(v_s_3244_);
return v_s_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1___boxed(lean_object* v_s_3246_, lean_object* v_x_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(v_s_3246_, v_x_3247_);
lean_dec_ref(v_x_3247_);
lean_dec(v_s_3246_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(lean_object* v_x_3249_, lean_object* v_x_3250_){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2___boxed(lean_object* v_x_3252_, lean_object* v_x_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(v_x_3252_, v_x_3253_);
lean_dec(v_x_3253_);
lean_dec_ref(v_x_3252_);
return v_res_3254_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3(void){
_start:
{
lean_object* v___f_3258_; lean_object* v___f_3259_; lean_object* v___f_3260_; lean_object* v___f_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___f_3258_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3259_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2));
v___f_3260_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1));
v___f_3261_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0));
v___x_3262_ = lean_box(0);
v___x_3263_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_3264_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3263_);
lean_ctor_set(v___x_3264_, 1, v___x_3262_);
lean_ctor_set(v___x_3264_, 2, v___f_3261_);
lean_ctor_set(v___x_3264_, 3, v___f_3260_);
lean_ctor_set(v___x_3264_, 4, v___f_3259_);
lean_ctor_set(v___x_3264_, 5, v___f_3258_);
return v___x_3264_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3265_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3);
v___x_3266_ = lean_box(0);
v___x_3267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
lean_ctor_set(v___x_3267_, 1, v___x_3265_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg(){
_start:
{
lean_object* v___x_3269_; 
v___x_3269_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___boxed(lean_object* v___dummy_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v_res_3271_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__0(void){
_start:
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3273_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg(){
_start:
{
lean_object* v___x_3276_; 
v___x_3276_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg___boxed(lean_object* v___dummy_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Lean_instInhabitedEnumAttributes___redArg();
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3279_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3280_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3281_; 
v___x_3281_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3282_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3284_);
lean_dec(v_x_3284_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3286_, lean_object* v_x_3287_, lean_object* v_x_3288_){
_start:
{
if (lean_obj_tag(v_x_3288_) == 0)
{
return v_x_3287_;
}
else
{
lean_object* v_head_3289_; lean_object* v_tail_3290_; lean_object* v___x_3291_; 
v_head_3289_ = lean_ctor_get(v_x_3288_, 0);
lean_inc(v_head_3289_);
v_tail_3290_ = lean_ctor_get(v_x_3288_, 1);
lean_inc(v_tail_3290_);
lean_dec_ref_known(v_x_3288_, 2);
v___x_3291_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3286_, v_head_3289_);
if (lean_obj_tag(v___x_3291_) == 1)
{
lean_object* v_val_3292_; lean_object* v___x_3293_; 
v_val_3292_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_val_3292_);
lean_dec_ref_known(v___x_3291_, 1);
v___x_3293_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3289_, v_val_3292_, v_x_3287_);
v_x_3287_ = v___x_3293_;
v_x_3288_ = v_tail_3290_;
goto _start;
}
else
{
lean_dec(v___x_3291_);
lean_dec(v_head_3289_);
v_x_3288_ = v_tail_3290_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3296_, lean_object* v_x_3297_, lean_object* v_x_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3296_, v_x_3297_, v_x_3298_);
lean_dec(v_newState_3296_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3300_, lean_object* v_newState_3301_, lean_object* v_consts_3302_, lean_object* v_st_3303_){
_start:
{
lean_object* v___x_3304_; 
v___x_3304_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3301_, v_st_3303_, v_consts_3302_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3305_, lean_object* v_newState_3306_, lean_object* v_consts_3307_, lean_object* v_st_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3305_, v_newState_3306_, v_consts_3307_, v_st_3308_);
lean_dec(v_newState_3306_);
lean_dec(v_x_3305_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3319_){
_start:
{
lean_object* v___x_3320_; lean_object* v___y_3322_; 
v___x_3320_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3319_) == 0)
{
lean_object* v_size_3326_; 
v_size_3326_ = lean_ctor_get(v_s_3319_, 0);
lean_inc(v_size_3326_);
lean_dec_ref_known(v_s_3319_, 5);
v___y_3322_ = v_size_3326_;
goto v___jp_3321_;
}
else
{
lean_object* v___x_3327_; 
v___x_3327_ = lean_unsigned_to_nat(0u);
v___y_3322_ = v___x_3327_;
goto v___jp_3321_;
}
v___jp_3321_:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = l_Nat_reprFast(v___y_3322_);
v___x_3324_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
v___x_3325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3320_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
return v___x_3325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3328_, lean_object* v_as_3329_, size_t v_i_3330_, size_t v_stop_3331_, lean_object* v_b_3332_){
_start:
{
lean_object* v___y_3334_; uint8_t v___x_3338_; 
v___x_3338_ = lean_usize_dec_eq(v_i_3330_, v_stop_3331_);
if (v___x_3338_ == 0)
{
lean_object* v___x_3339_; lean_object* v_fst_3340_; uint8_t v___x_3341_; lean_object* v___x_3342_; uint8_t v___x_3343_; 
v___x_3339_ = lean_array_uget_borrowed(v_as_3329_, v_i_3330_);
v_fst_3340_ = lean_ctor_get(v___x_3339_, 0);
v___x_3341_ = 1;
lean_inc_ref(v_env_3328_);
v___x_3342_ = l_Lean_Environment_setExporting(v_env_3328_, v___x_3341_);
lean_inc(v_fst_3340_);
v___x_3343_ = l_Lean_Environment_contains(v___x_3342_, v_fst_3340_, v___x_3338_);
if (v___x_3343_ == 0)
{
v___y_3334_ = v_b_3332_;
goto v___jp_3333_;
}
else
{
lean_object* v___x_3344_; 
lean_inc(v___x_3339_);
v___x_3344_ = lean_array_push(v_b_3332_, v___x_3339_);
v___y_3334_ = v___x_3344_;
goto v___jp_3333_;
}
}
else
{
lean_dec_ref(v_env_3328_);
return v_b_3332_;
}
v___jp_3333_:
{
size_t v___x_3335_; size_t v___x_3336_; 
v___x_3335_ = ((size_t)1ULL);
v___x_3336_ = lean_usize_add(v_i_3330_, v___x_3335_);
v_i_3330_ = v___x_3336_;
v_b_3332_ = v___y_3334_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3345_, lean_object* v_as_3346_, lean_object* v_i_3347_, lean_object* v_stop_3348_, lean_object* v_b_3349_){
_start:
{
size_t v_i_boxed_3350_; size_t v_stop_boxed_3351_; lean_object* v_res_3352_; 
v_i_boxed_3350_ = lean_unbox_usize(v_i_3347_);
lean_dec(v_i_3347_);
v_stop_boxed_3351_ = lean_unbox_usize(v_stop_3348_);
lean_dec(v_stop_3348_);
v_res_3352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3345_, v_as_3346_, v_i_boxed_3350_, v_stop_boxed_3351_, v_b_3349_);
lean_dec_ref(v_as_3346_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3353_, lean_object* v_m_3354_){
_start:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___y_3358_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___y_3369_; lean_object* v___y_3370_; uint8_t v___x_3372_; 
v___x_3355_ = lean_unsigned_to_nat(0u);
v___x_3356_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_3366_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_3356_, v_m_3354_);
v___x_3367_ = lean_array_get_size(v___x_3366_);
v___x_3372_ = lean_nat_dec_eq(v___x_3367_, v___x_3355_);
if (v___x_3372_ == 0)
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___y_3376_; uint8_t v___x_3378_; 
v___x_3373_ = lean_unsigned_to_nat(1u);
v___x_3374_ = lean_nat_sub(v___x_3367_, v___x_3373_);
v___x_3378_ = lean_nat_dec_le(v___x_3355_, v___x_3374_);
if (v___x_3378_ == 0)
{
lean_inc(v___x_3374_);
v___y_3376_ = v___x_3374_;
goto v___jp_3375_;
}
else
{
v___y_3376_ = v___x_3355_;
goto v___jp_3375_;
}
v___jp_3375_:
{
uint8_t v___x_3377_; 
v___x_3377_ = lean_nat_dec_le(v___y_3376_, v___x_3374_);
if (v___x_3377_ == 0)
{
lean_dec(v___x_3374_);
lean_inc(v___y_3376_);
v___y_3369_ = v___y_3376_;
v___y_3370_ = v___y_3376_;
goto v___jp_3368_;
}
else
{
v___y_3369_ = v___y_3376_;
v___y_3370_ = v___x_3374_;
goto v___jp_3368_;
}
}
}
else
{
v___y_3358_ = v___x_3366_;
goto v___jp_3357_;
}
v___jp_3357_:
{
lean_object* v___x_3359_; uint8_t v___x_3360_; 
v___x_3359_ = lean_array_get_size(v___y_3358_);
v___x_3360_ = lean_nat_dec_lt(v___x_3355_, v___x_3359_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3361_; 
lean_dec_ref(v_env_3353_);
v___x_3361_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3356_);
lean_ctor_set(v___x_3361_, 1, v___x_3356_);
lean_ctor_set(v___x_3361_, 2, v___y_3358_);
return v___x_3361_;
}
else
{
size_t v___x_3362_; size_t v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3362_ = ((size_t)0ULL);
v___x_3363_ = lean_usize_of_nat(v___x_3359_);
v___x_3364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3353_, v___y_3358_, v___x_3362_, v___x_3363_, v___x_3356_);
lean_inc_ref(v___x_3364_);
v___x_3365_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3364_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
lean_ctor_set(v___x_3365_, 2, v___y_3358_);
return v___x_3365_;
}
}
v___jp_3368_:
{
lean_object* v___x_3371_; 
v___x_3371_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_3367_, v___x_3366_, v___y_3369_, v___y_3370_);
lean_dec(v___y_3370_);
v___y_3358_ = v___x_3371_;
goto v___jp_3357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3379_, lean_object* v_m_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3379_, v_m_3380_);
lean_dec(v_m_3380_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3382_, lean_object* v_p_3383_){
_start:
{
lean_object* v_fst_3384_; lean_object* v_snd_3385_; lean_object* v___x_3386_; 
v_fst_3384_ = lean_ctor_get(v_p_3383_, 0);
lean_inc(v_fst_3384_);
v_snd_3385_ = lean_ctor_get(v_p_3383_, 1);
lean_inc(v_snd_3385_);
lean_dec_ref(v_p_3383_);
v___x_3386_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3384_, v_snd_3385_, v_s_3382_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3387_, lean_object* v_x_3388_, lean_object* v_x_3389_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3387_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3392_, lean_object* v_x_3393_, lean_object* v_x_3394_, lean_object* v___y_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3392_, v_x_3393_, v_x_3394_);
lean_dec_ref(v_x_3394_);
lean_dec_ref(v_x_3393_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3397_){
_start:
{
if (lean_obj_tag(v_as_3397_) == 0)
{
lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3399_ = lean_box(0);
v___x_3400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3399_);
return v___x_3400_;
}
else
{
lean_object* v_head_3401_; lean_object* v_tail_3402_; lean_object* v___x_3403_; 
v_head_3401_ = lean_ctor_get(v_as_3397_, 0);
lean_inc(v_head_3401_);
v_tail_3402_ = lean_ctor_get(v_as_3397_, 1);
lean_inc(v_tail_3402_);
lean_dec_ref_known(v_as_3397_, 2);
v___x_3403_ = l_Lean_registerBuiltinAttribute(v_head_3401_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_dec_ref_known(v___x_3403_, 1);
v_as_3397_ = v_tail_3402_;
goto _start;
}
else
{
lean_dec(v_tail_3402_);
return v___x_3403_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3405_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_addEntryFn_3408_, lean_object* v___x_3409_, lean_object* v_s_3410_){
_start:
{
lean_object* v_importedEntries_3411_; lean_object* v_state_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3420_; 
v_importedEntries_3411_ = lean_ctor_get(v_s_3410_, 0);
v_state_3412_ = lean_ctor_get(v_s_3410_, 1);
v_isSharedCheck_3420_ = !lean_is_exclusive(v_s_3410_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3414_ = v_s_3410_;
v_isShared_3415_ = v_isSharedCheck_3420_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_state_3412_);
lean_inc(v_importedEntries_3411_);
lean_dec(v_s_3410_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3420_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v_state_3416_; lean_object* v___x_3418_; 
v_state_3416_ = lean_apply_2(v_addEntryFn_3408_, v_state_3412_, v___x_3409_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 1, v_state_3416_);
v___x_3418_ = v___x_3414_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_importedEntries_3411_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v_state_3416_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2(lean_object* v_validate_3421_, lean_object* v_snd_3422_, lean_object* v_a_3423_, lean_object* v_fst_3424_, lean_object* v_decl_3425_, lean_object* v_stx_3426_, uint8_t v_kind_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_){
_start:
{
lean_object* v_nextMacroScope_3432_; lean_object* v_ngen_3433_; lean_object* v_auxDeclNGen_3434_; lean_object* v_traceState_3435_; lean_object* v_recordedDeps_3436_; lean_object* v_messages_3437_; lean_object* v_infoState_3438_; lean_object* v_snapshotTasks_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___x_3477_; 
v___x_3477_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3426_, v___y_3428_, v___y_3429_);
if (lean_obj_tag(v___x_3477_) == 0)
{
uint8_t v___x_3478_; uint8_t v___x_3479_; 
lean_dec_ref_known(v___x_3477_, 1);
v___x_3478_ = 0;
v___x_3479_ = l_Lean_instBEqAttributeKind_beq(v_kind_3427_, v___x_3478_);
if (v___x_3479_ == 0)
{
lean_object* v___x_3480_; 
lean_dec(v_decl_3425_);
lean_dec_ref(v_a_3423_);
lean_dec(v_snd_3422_);
lean_dec_ref(v_validate_3421_);
v___x_3480_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3424_, v_kind_3427_, v___y_3428_, v___y_3429_);
return v___x_3480_;
}
else
{
goto v___jp_3472_;
}
}
else
{
lean_dec(v_decl_3425_);
lean_dec(v_fst_3424_);
lean_dec_ref(v_a_3423_);
lean_dec(v_snd_3422_);
lean_dec_ref(v_validate_3421_);
return v___x_3477_;
}
v___jp_3431_:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3443_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_3444_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3444_, 0, v___y_3442_);
lean_ctor_set(v___x_3444_, 1, v_nextMacroScope_3432_);
lean_ctor_set(v___x_3444_, 2, v_ngen_3433_);
lean_ctor_set(v___x_3444_, 3, v_auxDeclNGen_3434_);
lean_ctor_set(v___x_3444_, 4, v_traceState_3435_);
lean_ctor_set(v___x_3444_, 5, v___x_3443_);
lean_ctor_set(v___x_3444_, 6, v_recordedDeps_3436_);
lean_ctor_set(v___x_3444_, 7, v_messages_3437_);
lean_ctor_set(v___x_3444_, 8, v_infoState_3438_);
lean_ctor_set(v___x_3444_, 9, v_snapshotTasks_3439_);
v___x_3445_ = lean_st_ref_put(v___y_3440_, v___x_3444_);
v___x_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3446_, 0, v___y_3441_);
return v___x_3446_;
}
v___jp_3447_:
{
lean_object* v___x_3450_; 
lean_inc(v___y_3449_);
lean_inc_ref(v___y_3448_);
lean_inc(v_snd_3422_);
lean_inc(v_decl_3425_);
v___x_3450_ = lean_apply_5(v_validate_3421_, v_decl_3425_, v_snd_3422_, v___y_3448_, v___y_3449_, lean_box(0));
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v___x_3451_; lean_object* v_toEnvExtension_3452_; lean_object* v_env_3453_; lean_object* v_nextMacroScope_3454_; lean_object* v_ngen_3455_; lean_object* v_auxDeclNGen_3456_; lean_object* v_traceState_3457_; lean_object* v_recordedDeps_3458_; lean_object* v_messages_3459_; lean_object* v_infoState_3460_; lean_object* v_snapshotTasks_3461_; lean_object* v_addEntryFn_3462_; lean_object* v_asyncMode_3463_; uint8_t v_logWrites_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___f_3467_; uint8_t v___x_3468_; 
lean_dec_ref_known(v___x_3450_, 1);
v___x_3451_ = lean_st_ref_take(v___y_3449_);
v_toEnvExtension_3452_ = lean_ctor_get(v_a_3423_, 0);
lean_inc_ref(v_toEnvExtension_3452_);
v_env_3453_ = lean_ctor_get(v___x_3451_, 0);
lean_inc_ref(v_env_3453_);
v_nextMacroScope_3454_ = lean_ctor_get(v___x_3451_, 1);
lean_inc(v_nextMacroScope_3454_);
v_ngen_3455_ = lean_ctor_get(v___x_3451_, 2);
lean_inc_ref(v_ngen_3455_);
v_auxDeclNGen_3456_ = lean_ctor_get(v___x_3451_, 3);
lean_inc_ref(v_auxDeclNGen_3456_);
v_traceState_3457_ = lean_ctor_get(v___x_3451_, 4);
lean_inc_ref(v_traceState_3457_);
v_recordedDeps_3458_ = lean_ctor_get(v___x_3451_, 6);
lean_inc_ref(v_recordedDeps_3458_);
v_messages_3459_ = lean_ctor_get(v___x_3451_, 7);
lean_inc_ref(v_messages_3459_);
v_infoState_3460_ = lean_ctor_get(v___x_3451_, 8);
lean_inc_ref(v_infoState_3460_);
v_snapshotTasks_3461_ = lean_ctor_get(v___x_3451_, 9);
lean_inc_ref(v_snapshotTasks_3461_);
lean_dec(v___x_3451_);
v_addEntryFn_3462_ = lean_ctor_get(v_a_3423_, 3);
lean_inc(v_addEntryFn_3462_);
lean_dec_ref(v_a_3423_);
v_asyncMode_3463_ = lean_ctor_get(v_toEnvExtension_3452_, 2);
lean_inc(v_asyncMode_3463_);
v_logWrites_3464_ = lean_ctor_get_uint8(v_toEnvExtension_3452_, sizeof(void*)*6);
v___x_3465_ = lean_box(0);
lean_inc(v_decl_3425_);
v___x_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3466_, 0, v_decl_3425_);
lean_ctor_set(v___x_3466_, 1, v_snd_3422_);
v___f_3467_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3467_, 0, v_addEntryFn_3462_);
lean_closure_set(v___f_3467_, 1, v___x_3466_);
v___x_3468_ = 1;
if (v_logWrites_3464_ == 0)
{
lean_object* v___x_3469_; 
v___x_3469_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3452_, v_env_3453_, v___f_3467_, v_asyncMode_3463_, v_decl_3425_, v___x_3468_);
lean_dec(v_asyncMode_3463_);
v_nextMacroScope_3432_ = v_nextMacroScope_3454_;
v_ngen_3433_ = v_ngen_3455_;
v_auxDeclNGen_3434_ = v_auxDeclNGen_3456_;
v_traceState_3435_ = v_traceState_3457_;
v_recordedDeps_3436_ = v_recordedDeps_3458_;
v_messages_3437_ = v_messages_3459_;
v_infoState_3438_ = v_infoState_3460_;
v_snapshotTasks_3439_ = v_snapshotTasks_3461_;
v___y_3440_ = v___y_3449_;
v___y_3441_ = v___x_3465_;
v___y_3442_ = v___x_3469_;
goto v___jp_3431_;
}
else
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
lean_inc_ref(v_toEnvExtension_3452_);
v___x_3470_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3452_, v_env_3453_);
lean_dec_ref(v_env_3453_);
v___x_3471_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3452_, v___x_3470_, v___f_3467_, v_asyncMode_3463_, v_decl_3425_, v___x_3468_);
lean_dec(v_asyncMode_3463_);
v_nextMacroScope_3432_ = v_nextMacroScope_3454_;
v_ngen_3433_ = v_ngen_3455_;
v_auxDeclNGen_3434_ = v_auxDeclNGen_3456_;
v_traceState_3435_ = v_traceState_3457_;
v_recordedDeps_3436_ = v_recordedDeps_3458_;
v_messages_3437_ = v_messages_3459_;
v_infoState_3438_ = v_infoState_3460_;
v_snapshotTasks_3439_ = v_snapshotTasks_3461_;
v___y_3440_ = v___y_3449_;
v___y_3441_ = v___x_3465_;
v___y_3442_ = v___x_3471_;
goto v___jp_3431_;
}
}
else
{
lean_dec(v_decl_3425_);
lean_dec_ref(v_a_3423_);
lean_dec(v_snd_3422_);
return v___x_3450_;
}
}
v___jp_3472_:
{
lean_object* v___x_3473_; lean_object* v_env_3474_; lean_object* v___x_3475_; 
v___x_3473_ = lean_st_ref_get(v___y_3429_);
v_env_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc_ref(v_env_3474_);
lean_dec(v___x_3473_);
v___x_3475_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3474_, v_decl_3425_);
lean_dec_ref(v_env_3474_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_dec(v_fst_3424_);
v___y_3448_ = v___y_3428_;
v___y_3449_ = v___y_3429_;
goto v___jp_3447_;
}
else
{
lean_object* v___x_3476_; 
lean_dec_ref_known(v___x_3475_, 1);
lean_dec_ref(v_a_3423_);
lean_dec(v_snd_3422_);
lean_dec_ref(v_validate_3421_);
v___x_3476_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3424_, v_decl_3425_, v___y_3428_, v___y_3429_);
return v___x_3476_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2___boxed(lean_object* v_validate_3481_, lean_object* v_snd_3482_, lean_object* v_a_3483_, lean_object* v_fst_3484_, lean_object* v_decl_3485_, lean_object* v_stx_3486_, lean_object* v_kind_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
uint8_t v_kind_boxed_3491_; lean_object* v_res_3492_; 
v_kind_boxed_3491_ = lean_unbox(v_kind_3487_);
v_res_3492_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2(v_validate_3481_, v_snd_3482_, v_a_3483_, v_fst_3484_, v_decl_3485_, v_stx_3486_, v_kind_boxed_3491_, v___y_3488_, v___y_3489_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3493_, lean_object* v_decl_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3498_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3499_ = l_Lean_MessageData_ofName(v_fst_3493_);
v___x_3500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3498_);
lean_ctor_set(v___x_3500_, 1, v___x_3499_);
v___x_3501_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3500_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
v___x_3503_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3502_, v___y_3495_, v___y_3496_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3504_, lean_object* v_decl_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3504_, v_decl_3505_, v___y_3506_, v___y_3507_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v_decl_3505_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3510_, lean_object* v_a_3511_, lean_object* v_ref_3512_, uint8_t v_applicationTime_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_){
_start:
{
if (lean_obj_tag(v_a_3514_) == 0)
{
lean_object* v___x_3516_; 
lean_dec(v_ref_3512_);
lean_dec_ref(v_a_3511_);
lean_dec_ref(v_validate_3510_);
v___x_3516_ = l_List_reverse___redArg(v_a_3515_);
return v___x_3516_;
}
else
{
lean_object* v_head_3517_; lean_object* v_snd_3518_; lean_object* v_tail_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3534_; 
v_head_3517_ = lean_ctor_get(v_a_3514_, 0);
lean_inc(v_head_3517_);
v_snd_3518_ = lean_ctor_get(v_head_3517_, 1);
lean_inc(v_snd_3518_);
v_tail_3519_ = lean_ctor_get(v_a_3514_, 1);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_a_3514_);
if (v_isSharedCheck_3534_ == 0)
{
lean_object* v_unused_3535_; 
v_unused_3535_ = lean_ctor_get(v_a_3514_, 0);
lean_dec(v_unused_3535_);
v___x_3521_ = v_a_3514_;
v_isShared_3522_ = v_isSharedCheck_3534_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_tail_3519_);
lean_dec(v_a_3514_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3534_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v_fst_3523_; lean_object* v_fst_3524_; lean_object* v_snd_3525_; lean_object* v___f_3526_; lean_object* v___f_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3531_; 
v_fst_3523_ = lean_ctor_get(v_head_3517_, 0);
lean_inc_n(v_fst_3523_, 3);
lean_dec(v_head_3517_);
v_fst_3524_ = lean_ctor_get(v_snd_3518_, 0);
lean_inc(v_fst_3524_);
v_snd_3525_ = lean_ctor_get(v_snd_3518_, 1);
lean_inc(v_snd_3525_);
lean_dec(v_snd_3518_);
v___f_3526_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3526_, 0, v_fst_3523_);
lean_inc_ref(v_a_3511_);
lean_inc_ref(v_validate_3510_);
v___f_3527_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2___boxed), 10, 4);
lean_closure_set(v___f_3527_, 0, v_validate_3510_);
lean_closure_set(v___f_3527_, 1, v_snd_3525_);
lean_closure_set(v___f_3527_, 2, v_a_3511_);
lean_closure_set(v___f_3527_, 3, v_fst_3523_);
lean_inc(v_ref_3512_);
v___x_3528_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3528_, 0, v_ref_3512_);
lean_ctor_set(v___x_3528_, 1, v_fst_3523_);
lean_ctor_set(v___x_3528_, 2, v_fst_3524_);
lean_ctor_set_uint8(v___x_3528_, sizeof(void*)*3, v_applicationTime_3513_);
v___x_3529_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
lean_ctor_set(v___x_3529_, 1, v___f_3527_);
lean_ctor_set(v___x_3529_, 2, v___f_3526_);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 1, v_a_3515_);
lean_ctor_set(v___x_3521_, 0, v___x_3529_);
v___x_3531_ = v___x_3521_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3529_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v_a_3515_);
v___x_3531_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
v_a_3514_ = v_tail_3519_;
v_a_3515_ = v___x_3531_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3536_, lean_object* v_a_3537_, lean_object* v_ref_3538_, lean_object* v_applicationTime_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
uint8_t v_applicationTime_boxed_3542_; lean_object* v_res_3543_; 
v_applicationTime_boxed_3542_ = lean_unbox(v_applicationTime_3539_);
v_res_3543_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3536_, v_a_3537_, v_ref_3538_, v_applicationTime_boxed_3542_, v_a_3540_, v_a_3541_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3557_, lean_object* v_validate_3558_, uint8_t v_applicationTime_3559_, lean_object* v_ref_3560_){
_start:
{
lean_object* v___f_3562_; lean_object* v___f_3563_; lean_object* v___f_3564_; lean_object* v___f_3565_; lean_object* v___f_3566_; lean_object* v___f_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; uint8_t v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___f_3562_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3563_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3564_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3565_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3566_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3567_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3568_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3569_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
v___x_3570_ = 0;
lean_inc(v_ref_3560_);
v___x_3571_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_3571_, 0, v_ref_3560_);
lean_ctor_set(v___x_3571_, 1, v___f_3566_);
lean_ctor_set(v___x_3571_, 2, v___f_3567_);
lean_ctor_set(v___x_3571_, 3, v___f_3565_);
lean_ctor_set(v___x_3571_, 4, v___f_3564_);
lean_ctor_set(v___x_3571_, 5, v___f_3563_);
lean_ctor_set(v___x_3571_, 6, v___x_3568_);
lean_ctor_set(v___x_3571_, 7, v___x_3569_);
lean_ctor_set_uint8(v___x_3571_, sizeof(void*)*8, v___x_3570_);
lean_ctor_set_uint8(v___x_3571_, sizeof(void*)*8 + 1, v___x_3570_);
v___x_3572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3571_);
lean_ctor_set(v___x_3572_, 1, v___f_3562_);
v___x_3573_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3572_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
lean_inc_n(v_a_3574_, 2);
lean_dec_ref_known(v___x_3573_, 1);
v___x_3575_ = lean_box(0);
v___x_3576_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3558_, v_a_3574_, v_ref_3560_, v_applicationTime_3559_, v_attrDescrs_3557_, v___x_3575_);
lean_inc(v___x_3576_);
v___x_3577_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3576_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3585_; 
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3585_ == 0)
{
lean_object* v_unused_3586_; 
v_unused_3586_ = lean_ctor_get(v___x_3577_, 0);
lean_dec(v_unused_3586_);
v___x_3579_ = v___x_3577_;
v_isShared_3580_ = v_isSharedCheck_3585_;
goto v_resetjp_3578_;
}
else
{
lean_dec(v___x_3577_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3585_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3581_; lean_object* v___x_3583_; 
v___x_3581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3576_);
lean_ctor_set(v___x_3581_, 1, v_a_3574_);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v___x_3581_);
v___x_3583_ = v___x_3579_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3581_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
else
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3594_; 
lean_dec(v___x_3576_);
lean_dec(v_a_3574_);
v_a_3587_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3589_ = v___x_3577_;
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3577_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3592_; 
if (v_isShared_3590_ == 0)
{
v___x_3592_ = v___x_3589_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_a_3587_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_dec(v_ref_3560_);
lean_dec_ref(v_validate_3558_);
lean_dec(v_attrDescrs_3557_);
v_a_3595_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3573_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3573_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3603_, lean_object* v_validate_3604_, lean_object* v_applicationTime_3605_, lean_object* v_ref_3606_, lean_object* v_a_3607_){
_start:
{
uint8_t v_applicationTime_boxed_3608_; lean_object* v_res_3609_; 
v_applicationTime_boxed_3608_ = lean_unbox(v_applicationTime_3605_);
v_res_3609_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3603_, v_validate_3604_, v_applicationTime_boxed_3608_, v_ref_3606_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3610_, lean_object* v_attrDescrs_3611_, lean_object* v_validate_3612_, uint8_t v_applicationTime_3613_, lean_object* v_ref_3614_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3611_, v_validate_3612_, v_applicationTime_3613_, v_ref_3614_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3617_, lean_object* v_attrDescrs_3618_, lean_object* v_validate_3619_, lean_object* v_applicationTime_3620_, lean_object* v_ref_3621_, lean_object* v_a_3622_){
_start:
{
uint8_t v_applicationTime_boxed_3623_; lean_object* v_res_3624_; 
v_applicationTime_boxed_3623_ = lean_unbox(v_applicationTime_3620_);
v_res_3624_ = l_Lean_registerEnumAttributes(v_00_u03b1_3617_, v_attrDescrs_3618_, v_validate_3619_, v_applicationTime_boxed_3623_, v_ref_3621_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3625_, lean_object* v_env_3626_, lean_object* v_as_3627_, size_t v_i_3628_, size_t v_stop_3629_, lean_object* v_b_3630_){
_start:
{
lean_object* v___x_3631_; 
v___x_3631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3626_, v_as_3627_, v_i_3628_, v_stop_3629_, v_b_3630_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3632_, lean_object* v_env_3633_, lean_object* v_as_3634_, lean_object* v_i_3635_, lean_object* v_stop_3636_, lean_object* v_b_3637_){
_start:
{
size_t v_i_boxed_3638_; size_t v_stop_boxed_3639_; lean_object* v_res_3640_; 
v_i_boxed_3638_ = lean_unbox_usize(v_i_3635_);
lean_dec(v_i_3635_);
v_stop_boxed_3639_ = lean_unbox_usize(v_stop_3636_);
lean_dec(v_stop_3636_);
v_res_3640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3632_, v_env_3633_, v_as_3634_, v_i_boxed_3638_, v_stop_boxed_3639_, v_b_3637_);
lean_dec_ref(v_as_3634_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3641_, lean_object* v_newState_3642_, lean_object* v_x_3643_, lean_object* v_x_3644_){
_start:
{
lean_object* v___x_3645_; 
v___x_3645_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3642_, v_x_3643_, v_x_3644_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3646_, lean_object* v_newState_3647_, lean_object* v_x_3648_, lean_object* v_x_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3646_, v_newState_3647_, v_x_3648_, v_x_3649_);
lean_dec(v_newState_3647_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3651_, lean_object* v_validate_3652_, lean_object* v_a_3653_, lean_object* v_ref_3654_, uint8_t v_applicationTime_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_){
_start:
{
lean_object* v___x_3658_; 
v___x_3658_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3652_, v_a_3653_, v_ref_3654_, v_applicationTime_3655_, v_a_3656_, v_a_3657_);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3659_, lean_object* v_validate_3660_, lean_object* v_a_3661_, lean_object* v_ref_3662_, lean_object* v_applicationTime_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_){
_start:
{
uint8_t v_applicationTime_boxed_3666_; lean_object* v_res_3667_; 
v_applicationTime_boxed_3666_ = lean_unbox(v_applicationTime_3663_);
v_res_3667_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3659_, v_validate_3660_, v_a_3661_, v_ref_3662_, v_applicationTime_boxed_3666_, v_a_3664_, v_a_3665_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3668_, lean_object* v_attr_3669_, lean_object* v_env_3670_, lean_object* v_decl_3671_){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3672_ = lean_box(1);
v___x_3673_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3670_, v_decl_3671_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_ext_3674_; lean_object* v_toEnvExtension_3675_; lean_object* v_asyncMode_3676_; uint8_t v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
lean_dec(v_inst_3668_);
v_ext_3674_ = lean_ctor_get(v_attr_3669_, 1);
lean_inc_ref(v_ext_3674_);
lean_dec_ref(v_attr_3669_);
v_toEnvExtension_3675_ = lean_ctor_get(v_ext_3674_, 0);
v_asyncMode_3676_ = lean_ctor_get(v_toEnvExtension_3675_, 2);
lean_inc(v_asyncMode_3676_);
v___x_3677_ = 0;
lean_inc(v_decl_3671_);
v___x_3678_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3672_, v_ext_3674_, v_env_3670_, v_asyncMode_3676_, v_decl_3671_, v___x_3677_);
lean_dec(v_asyncMode_3676_);
lean_dec_ref(v_ext_3674_);
v___x_3679_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3678_, v_decl_3671_);
lean_dec(v_decl_3671_);
lean_dec(v___x_3678_);
return v___x_3679_;
}
else
{
lean_object* v_val_3680_; lean_object* v_ext_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3711_; 
v_val_3680_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_val_3680_);
lean_dec_ref_known(v___x_3673_, 1);
v_ext_3681_ = lean_ctor_get(v_attr_3669_, 1);
v_isSharedCheck_3711_ = !lean_is_exclusive(v_attr_3669_);
if (v_isSharedCheck_3711_ == 0)
{
lean_object* v_unused_3712_; 
v_unused_3712_ = lean_ctor_get(v_attr_3669_, 0);
lean_dec(v_unused_3712_);
v___x_3683_ = v_attr_3669_;
v_isShared_3684_ = v_isSharedCheck_3711_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_ext_3681_);
lean_dec(v_attr_3669_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3711_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
uint8_t v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; uint8_t v___x_3689_; 
v___x_3685_ = 0;
v___x_3686_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3672_, v_ext_3681_, v_env_3670_, v_val_3680_, v___x_3685_);
lean_dec(v_val_3680_);
lean_dec_ref(v_env_3670_);
lean_dec_ref(v_ext_3681_);
v___x_3687_ = lean_unsigned_to_nat(0u);
v___x_3688_ = lean_array_get_size(v___x_3686_);
v___x_3689_ = lean_nat_dec_lt(v___x_3687_, v___x_3688_);
if (v___x_3689_ == 0)
{
lean_object* v___x_3690_; 
lean_dec_ref(v___x_3686_);
lean_del_object(v___x_3683_);
lean_dec(v_decl_3671_);
lean_dec(v_inst_3668_);
v___x_3690_ = lean_box(0);
return v___x_3690_;
}
else
{
lean_object* v___x_3691_; lean_object* v___x_3692_; uint8_t v___x_3693_; 
v___x_3691_ = lean_unsigned_to_nat(1u);
v___x_3692_ = lean_nat_sub(v___x_3688_, v___x_3691_);
v___x_3693_ = lean_nat_dec_le(v___x_3687_, v___x_3692_);
if (v___x_3693_ == 0)
{
lean_object* v___x_3694_; 
lean_dec(v___x_3692_);
lean_dec_ref(v___x_3686_);
lean_del_object(v___x_3683_);
lean_dec(v_decl_3671_);
lean_dec(v_inst_3668_);
v___x_3694_ = lean_box(0);
return v___x_3694_;
}
else
{
lean_object* v___f_3695_; lean_object* v___x_3697_; 
v___f_3695_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 1, v_inst_3668_);
lean_ctor_set(v___x_3683_, 0, v_decl_3671_);
v___x_3697_ = v___x_3683_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_decl_3671_);
lean_ctor_set(v_reuseFailAlloc_3710_, 1, v_inst_3668_);
v___x_3697_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3699_ = l_Array_binSearchAux___redArg(v___f_3695_, v___x_3698_, v___x_3686_, v___x_3697_, v___x_3687_, v___x_3692_);
lean_dec_ref(v___x_3686_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v___x_3700_; 
v___x_3700_ = lean_box(0);
return v___x_3700_;
}
else
{
lean_object* v_val_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3709_; 
v_val_3701_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3703_ = v___x_3699_;
v_isShared_3704_ = v_isSharedCheck_3709_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_val_3701_);
lean_dec(v___x_3699_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3709_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v_snd_3705_; lean_object* v___x_3707_; 
v_snd_3705_ = lean_ctor_get(v_val_3701_, 1);
lean_inc(v_snd_3705_);
lean_dec(v_val_3701_);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 0, v_snd_3705_);
v___x_3707_ = v___x_3703_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_snd_3705_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3713_, lean_object* v_inst_3714_, lean_object* v_attr_3715_, lean_object* v_env_3716_, lean_object* v_decl_3717_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3714_, v_attr_3715_, v_env_3716_, v_decl_3717_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3727_, lean_object* v_env_3728_, lean_object* v_decl_3729_, lean_object* v_val_3730_){
_start:
{
lean_object* v_ext_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3801_; 
v_ext_3731_ = lean_ctor_get(v_attrs_3727_, 1);
v_isSharedCheck_3801_ = !lean_is_exclusive(v_attrs_3727_);
if (v_isSharedCheck_3801_ == 0)
{
lean_object* v_unused_3802_; 
v_unused_3802_ = lean_ctor_get(v_attrs_3727_, 0);
lean_dec(v_unused_3802_);
v___x_3733_ = v_attrs_3727_;
v_isShared_3734_ = v_isSharedCheck_3801_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_ext_3731_);
lean_dec(v_attrs_3727_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3801_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v_toEnvExtension_3735_; lean_object* v_name_3736_; lean_object* v_addEntryFn_3737_; lean_object* v___x_3738_; uint8_t v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v_pfx_3747_; lean_object* v___x_3748_; 
v_toEnvExtension_3735_ = lean_ctor_get(v_ext_3731_, 0);
lean_inc_ref(v_toEnvExtension_3735_);
v_name_3736_ = lean_ctor_get(v_ext_3731_, 1);
v_addEntryFn_3737_ = lean_ctor_get(v_ext_3731_, 3);
lean_inc(v_addEntryFn_3737_);
v___x_3738_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3739_ = 1;
lean_inc(v_name_3736_);
v___x_3740_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3736_, v___x_3739_);
v___x_3741_ = lean_string_append(v___x_3738_, v___x_3740_);
lean_dec_ref(v___x_3740_);
v___x_3742_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3743_ = lean_string_append(v___x_3741_, v___x_3742_);
lean_inc(v_decl_3729_);
v___x_3744_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3729_, v___x_3739_);
v___x_3745_ = lean_string_append(v___x_3743_, v___x_3744_);
lean_dec_ref(v___x_3744_);
v___x_3746_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3747_ = lean_string_append(v___x_3745_, v___x_3746_);
v___x_3748_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3728_, v_decl_3729_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v_asyncMode_3749_; uint8_t v_logWrites_3750_; uint8_t v___x_3751_; 
v_asyncMode_3749_ = lean_ctor_get(v_toEnvExtension_3735_, 2);
lean_inc(v_asyncMode_3749_);
v_logWrites_3750_ = lean_ctor_get_uint8(v_toEnvExtension_3735_, sizeof(void*)*6);
lean_inc(v_decl_3729_);
lean_inc_ref(v_env_3728_);
v___x_3751_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3728_, v_decl_3729_, v_asyncMode_3749_);
if (v___x_3751_ == 0)
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___y_3755_; lean_object* v___x_3759_; 
lean_dec(v_asyncMode_3749_);
lean_dec(v_addEntryFn_3737_);
lean_dec_ref(v_toEnvExtension_3735_);
lean_del_object(v___x_3733_);
lean_dec_ref(v_ext_3731_);
lean_dec(v_val_3730_);
lean_dec(v_decl_3729_);
v___x_3752_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3753_ = lean_string_append(v_pfx_3747_, v___x_3752_);
v___x_3759_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3728_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v___x_3760_; 
v___x_3760_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3755_ = v___x_3760_;
goto v___jp_3754_;
}
else
{
lean_object* v_val_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
v_val_3761_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_val_3761_);
lean_dec_ref_known(v___x_3759_, 1);
v___x_3762_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3763_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3761_, v___x_3739_);
v___x_3764_ = l_addParenHeuristic(v___x_3763_);
v___x_3765_ = lean_string_append(v___x_3762_, v___x_3764_);
lean_dec_ref(v___x_3764_);
v___x_3766_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3767_ = lean_string_append(v___x_3765_, v___x_3766_);
v___y_3755_ = v___x_3767_;
goto v___jp_3754_;
}
v___jp_3754_:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3756_ = lean_string_append(v___x_3753_, v___y_3755_);
lean_dec_ref(v___y_3755_);
v___x_3757_ = lean_string_append(v___x_3756_, v___x_3746_);
v___x_3758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3757_);
return v___x_3758_;
}
}
else
{
lean_object* v___x_3768_; uint8_t v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3768_ = lean_box(1);
v___x_3769_ = 0;
lean_inc(v_decl_3729_);
lean_inc_ref(v_env_3728_);
v___x_3770_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3768_, v_ext_3731_, v_env_3728_, v_asyncMode_3749_, v_decl_3729_, v___x_3769_);
lean_dec_ref(v_ext_3731_);
v___x_3771_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3770_, v_decl_3729_);
lean_dec(v___x_3770_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v___x_3773_; 
lean_dec_ref(v_pfx_3747_);
lean_inc(v_decl_3729_);
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 1, v_val_3730_);
lean_ctor_set(v___x_3733_, 0, v_decl_3729_);
v___x_3773_ = v___x_3733_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_decl_3729_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_val_3730_);
v___x_3773_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
lean_object* v___f_3774_; 
v___f_3774_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3774_, 0, v_addEntryFn_3737_);
lean_closure_set(v___f_3774_, 1, v___x_3773_);
if (v_logWrites_3750_ == 0)
{
lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3775_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3735_, v_env_3728_, v___f_3774_, v_asyncMode_3749_, v_decl_3729_, v___x_3751_);
lean_dec(v_asyncMode_3749_);
v___x_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3775_);
return v___x_3776_;
}
else
{
lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
lean_inc_ref(v_toEnvExtension_3735_);
v___x_3777_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3735_, v_env_3728_);
lean_dec_ref(v_env_3728_);
v___x_3778_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3735_, v___x_3777_, v___f_3774_, v_asyncMode_3749_, v_decl_3729_, v___x_3751_);
lean_dec(v_asyncMode_3749_);
v___x_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3778_);
return v___x_3779_;
}
}
}
else
{
lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3789_; 
lean_dec(v_asyncMode_3749_);
lean_dec(v_addEntryFn_3737_);
lean_dec_ref(v_toEnvExtension_3735_);
lean_del_object(v___x_3733_);
lean_dec(v_val_3730_);
lean_dec(v_decl_3729_);
lean_dec_ref(v_env_3728_);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3789_ == 0)
{
lean_object* v_unused_3790_; 
v_unused_3790_ = lean_ctor_get(v___x_3771_, 0);
lean_dec(v_unused_3790_);
v___x_3782_ = v___x_3771_;
v_isShared_3783_ = v_isSharedCheck_3789_;
goto v_resetjp_3781_;
}
else
{
lean_dec(v___x_3771_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3789_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3787_; 
v___x_3784_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3785_ = lean_string_append(v_pfx_3747_, v___x_3784_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set_tag(v___x_3782_, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3785_);
v___x_3787_ = v___x_3782_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v___x_3785_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
}
}
else
{
lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3799_; 
lean_dec(v_addEntryFn_3737_);
lean_dec_ref(v_toEnvExtension_3735_);
lean_del_object(v___x_3733_);
lean_dec_ref(v_ext_3731_);
lean_dec(v_val_3730_);
lean_dec(v_decl_3729_);
lean_dec_ref(v_env_3728_);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3799_ == 0)
{
lean_object* v_unused_3800_; 
v_unused_3800_ = lean_ctor_get(v___x_3748_, 0);
lean_dec(v_unused_3800_);
v___x_3792_ = v___x_3748_;
v_isShared_3793_ = v_isSharedCheck_3799_;
goto v_resetjp_3791_;
}
else
{
lean_dec(v___x_3748_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3799_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3797_; 
v___x_3794_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3795_ = lean_string_append(v_pfx_3747_, v___x_3794_);
if (v_isShared_3793_ == 0)
{
lean_ctor_set_tag(v___x_3792_, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3795_);
v___x_3797_ = v___x_3792_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3795_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3803_, lean_object* v_attrs_3804_, lean_object* v_env_3805_, lean_object* v_decl_3806_, lean_object* v_val_3807_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3804_, v_env_3805_, v_decl_3806_, v_val_3807_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3810_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3811_ = lean_st_mk_ref(v___x_3810_);
v___x_3812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3811_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3817_, lean_object* v_builder_3818_){
_start:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; uint8_t v___x_3822_; 
v___x_3820_ = l_Lean_attributeImplBuilderTableRef;
v___x_3821_ = lean_st_ref_get(v___x_3820_);
v___x_3822_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3821_, v_builderId_3817_);
lean_dec(v___x_3821_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___x_3823_ = lean_st_ref_take(v___x_3820_);
v___x_3824_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3823_, v_builderId_3817_, v_builder_3818_);
v___x_3825_ = lean_st_ref_put(v___x_3820_, v___x_3824_);
v___x_3826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3825_);
return v___x_3826_;
}
else
{
lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
lean_dec_ref(v_builder_3818_);
v___x_3827_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3828_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3817_, v___x_3822_);
v___x_3829_ = lean_string_append(v___x_3827_, v___x_3828_);
lean_dec_ref(v___x_3828_);
v___x_3830_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3831_ = lean_string_append(v___x_3829_, v___x_3830_);
v___x_3832_ = lean_mk_io_user_error(v___x_3831_);
v___x_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3832_);
return v___x_3833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3834_, lean_object* v_builder_3835_, lean_object* v_a_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_registerAttributeImplBuilder(v_builderId_3834_, v_builder_3835_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3838_){
_start:
{
if (lean_obj_tag(v_e_3838_) == 0)
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3848_; 
v_a_3840_ = lean_ctor_get(v_e_3838_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v_e_3838_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3842_ = v_e_3838_;
v_isShared_3843_ = v_isSharedCheck_3848_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v_e_3838_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3848_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3844_; lean_object* v___x_3846_; 
v___x_3844_ = lean_mk_io_user_error(v_a_3840_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set_tag(v___x_3842_, 1);
lean_ctor_set(v___x_3842_, 0, v___x_3844_);
v___x_3846_ = v___x_3842_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3844_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
v_a_3849_ = lean_ctor_get(v_e_3838_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v_e_3838_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v_e_3838_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v_e_3838_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
lean_ctor_set_tag(v___x_3851_, 0);
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3857_, lean_object* v_a_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3857_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3860_, lean_object* v_e_3861_){
_start:
{
lean_object* v___x_3863_; 
v___x_3863_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3861_);
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3864_, lean_object* v_e_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3864_, v_e_3865_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3868_, lean_object* v_x_3869_){
_start:
{
if (lean_obj_tag(v_x_3869_) == 0)
{
lean_object* v___x_3870_; 
v___x_3870_ = lean_box(0);
return v___x_3870_;
}
else
{
lean_object* v_key_3871_; lean_object* v_value_3872_; lean_object* v_tail_3873_; uint8_t v___x_3874_; 
v_key_3871_ = lean_ctor_get(v_x_3869_, 0);
v_value_3872_ = lean_ctor_get(v_x_3869_, 1);
v_tail_3873_ = lean_ctor_get(v_x_3869_, 2);
v___x_3874_ = lean_name_eq(v_key_3871_, v_a_3868_);
if (v___x_3874_ == 0)
{
v_x_3869_ = v_tail_3873_;
goto _start;
}
else
{
lean_object* v___x_3876_; 
lean_inc(v_value_3872_);
v___x_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3876_, 0, v_value_3872_);
return v___x_3876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3877_, lean_object* v_x_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3877_, v_x_3878_);
lean_dec(v_x_3878_);
lean_dec(v_a_3877_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3880_, lean_object* v_a_3881_){
_start:
{
lean_object* v_buckets_3882_; lean_object* v___x_3883_; uint64_t v___y_3885_; 
v_buckets_3882_ = lean_ctor_get(v_m_3880_, 1);
v___x_3883_ = lean_array_get_size(v_buckets_3882_);
if (lean_obj_tag(v_a_3881_) == 0)
{
uint64_t v___x_3899_; 
v___x_3899_ = 1723ULL;
v___y_3885_ = v___x_3899_;
goto v___jp_3884_;
}
else
{
uint64_t v_hash_3900_; 
v_hash_3900_ = lean_ctor_get_uint64(v_a_3881_, sizeof(void*)*2);
v___y_3885_ = v_hash_3900_;
goto v___jp_3884_;
}
v___jp_3884_:
{
uint64_t v___x_3886_; uint64_t v___x_3887_; uint64_t v_fold_3888_; uint64_t v___x_3889_; uint64_t v___x_3890_; uint64_t v___x_3891_; size_t v___x_3892_; size_t v___x_3893_; size_t v___x_3894_; size_t v___x_3895_; size_t v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3886_ = 32ULL;
v___x_3887_ = lean_uint64_shift_right(v___y_3885_, v___x_3886_);
v_fold_3888_ = lean_uint64_xor(v___y_3885_, v___x_3887_);
v___x_3889_ = 16ULL;
v___x_3890_ = lean_uint64_shift_right(v_fold_3888_, v___x_3889_);
v___x_3891_ = lean_uint64_xor(v_fold_3888_, v___x_3890_);
v___x_3892_ = lean_uint64_to_usize(v___x_3891_);
v___x_3893_ = lean_usize_of_nat(v___x_3883_);
v___x_3894_ = ((size_t)1ULL);
v___x_3895_ = lean_usize_sub(v___x_3893_, v___x_3894_);
v___x_3896_ = lean_usize_land(v___x_3892_, v___x_3895_);
v___x_3897_ = lean_array_uget_borrowed(v_buckets_3882_, v___x_3896_);
v___x_3898_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3881_, v___x_3897_);
return v___x_3898_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3901_, lean_object* v_a_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3901_, v_a_3902_);
lean_dec(v_a_3902_);
lean_dec_ref(v_m_3901_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3905_){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v_builderId_3909_; lean_object* v_ref_3910_; lean_object* v_args_3911_; lean_object* v___x_3912_; 
v___x_3907_ = l_Lean_attributeImplBuilderTableRef;
v___x_3908_ = lean_st_ref_get(v___x_3907_);
v_builderId_3909_ = lean_ctor_get(v_e_3905_, 0);
lean_inc(v_builderId_3909_);
v_ref_3910_ = lean_ctor_get(v_e_3905_, 1);
lean_inc(v_ref_3910_);
v_args_3911_ = lean_ctor_get(v_e_3905_, 2);
lean_inc(v_args_3911_);
lean_dec_ref(v_e_3905_);
v___x_3912_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3908_, v_builderId_3909_);
lean_dec(v___x_3908_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v___x_3913_; uint8_t v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
lean_dec(v_args_3911_);
lean_dec(v_ref_3910_);
v___x_3913_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3914_ = 1;
v___x_3915_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3909_, v___x_3914_);
v___x_3916_ = lean_string_append(v___x_3913_, v___x_3915_);
lean_dec_ref(v___x_3915_);
v___x_3917_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3918_ = lean_string_append(v___x_3916_, v___x_3917_);
v___x_3919_ = lean_mk_io_user_error(v___x_3918_);
v___x_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3919_);
return v___x_3920_;
}
else
{
lean_object* v_val_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
lean_dec(v_builderId_3909_);
v_val_3921_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_val_3921_);
lean_dec_ref_known(v___x_3912_, 1);
v___x_3922_ = lean_apply_2(v_val_3921_, v_ref_3910_, v_args_3911_);
v___x_3923_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3922_);
return v___x_3923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3924_, lean_object* v_a_3925_){
_start:
{
lean_object* v_res_3926_; 
v_res_3926_ = l_Lean_mkAttributeImplOfEntry(v_e_3924_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3927_, lean_object* v_m_3928_, lean_object* v_a_3929_){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3928_, v_a_3929_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3931_, lean_object* v_m_3932_, lean_object* v_a_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3931_, v_m_3932_, v_a_3933_);
lean_dec(v_a_3933_);
lean_dec_ref(v_m_3932_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3935_, lean_object* v_a_3936_, lean_object* v_x_3937_){
_start:
{
lean_object* v___x_3938_; 
v___x_3938_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3936_, v_x_3937_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3939_, lean_object* v_a_3940_, lean_object* v_x_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3939_, v_a_3940_, v_x_3941_);
lean_dec(v_x_3941_);
lean_dec(v_a_3940_);
return v_res_3942_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3943_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3944_ = lean_box(0);
v___x_3945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3944_);
lean_ctor_set(v___x_3945_, 1, v___x_3943_);
return v___x_3945_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3946_; 
v___x_3946_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3946_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3947_; 
v___x_3947_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___x_3949_ = l_Lean_attributeMapRef;
v___x_3950_ = lean_st_ref_get(v___x_3949_);
v___x_3951_ = lean_box(0);
v___x_3952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3951_);
lean_ctor_set(v___x_3952_, 1, v___x_3950_);
v___x_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3952_);
return v___x_3953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3961_, lean_object* v_opts_3962_, lean_object* v_declName_3963_){
_start:
{
uint8_t v___x_3966_; lean_object* v___x_3967_; 
v___x_3966_ = 0;
lean_inc(v_declName_3963_);
lean_inc_ref(v_env_3961_);
v___x_3967_ = l_Lean_Environment_find_x3f(v_env_3961_, v_declName_3963_, v___x_3966_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v___x_3968_; uint8_t v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
lean_dec_ref(v_env_3961_);
v___x_3968_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3969_ = 1;
v___x_3970_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3963_, v___x_3969_);
v___x_3971_ = lean_string_append(v___x_3968_, v___x_3970_);
lean_dec_ref(v___x_3970_);
v___x_3972_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3973_ = lean_string_append(v___x_3971_, v___x_3972_);
v___x_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3973_);
return v___x_3974_;
}
else
{
lean_object* v_val_3975_; lean_object* v___x_3976_; 
v_val_3975_ = lean_ctor_get(v___x_3967_, 0);
lean_inc(v_val_3975_);
lean_dec_ref_known(v___x_3967_, 1);
v___x_3976_ = l_Lean_ConstantInfo_type(v_val_3975_);
lean_dec(v_val_3975_);
if (lean_obj_tag(v___x_3976_) == 4)
{
lean_object* v_declName_3977_; 
v_declName_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_declName_3977_);
lean_dec_ref_known(v___x_3976_, 2);
if (lean_obj_tag(v_declName_3977_) == 1)
{
lean_object* v_pre_3978_; 
v_pre_3978_ = lean_ctor_get(v_declName_3977_, 0);
lean_inc(v_pre_3978_);
if (lean_obj_tag(v_pre_3978_) == 1)
{
lean_object* v_pre_3979_; 
v_pre_3979_ = lean_ctor_get(v_pre_3978_, 0);
if (lean_obj_tag(v_pre_3979_) == 0)
{
lean_object* v_str_3980_; lean_object* v_str_3981_; lean_object* v___x_3982_; uint8_t v___x_3983_; 
v_str_3980_ = lean_ctor_get(v_declName_3977_, 1);
lean_inc_ref(v_str_3980_);
lean_dec_ref_known(v_declName_3977_, 2);
v_str_3981_ = lean_ctor_get(v_pre_3978_, 1);
lean_inc_ref(v_str_3981_);
lean_dec_ref_known(v_pre_3978_, 2);
v___x_3982_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_3983_ = lean_string_dec_eq(v_str_3981_, v___x_3982_);
lean_dec_ref(v_str_3981_);
if (v___x_3983_ == 0)
{
lean_dec_ref(v_str_3980_);
lean_dec(v_declName_3963_);
lean_dec_ref(v_env_3961_);
goto v___jp_3964_;
}
else
{
lean_object* v___x_3984_; uint8_t v___x_3985_; 
v___x_3984_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_3985_ = lean_string_dec_eq(v_str_3980_, v___x_3984_);
lean_dec_ref(v_str_3980_);
if (v___x_3985_ == 0)
{
lean_dec(v_declName_3963_);
lean_dec_ref(v_env_3961_);
goto v___jp_3964_;
}
else
{
lean_object* v___x_3986_; 
v___x_3986_ = l_Lean_Environment_evalConst___redArg(v_env_3961_, v_opts_3962_, v_declName_3963_, v___x_3985_);
lean_dec(v_declName_3963_);
lean_dec_ref(v_env_3961_);
return v___x_3986_;
}
}
}
else
{
lean_dec_ref_known(v_pre_3978_, 2);
lean_dec_ref_known(v_declName_3977_, 2);
lean_dec(v_declName_3963_);
lean_dec_ref(v_env_3961_);
goto v___jp_3964_;
}
}
else
{
lean_dec_ref_known(v_declName_3977_, 2);
lean_dec(v_pre_3978_);
lean_dec(v_declName_3963_);
lean_dec_ref(v_env_3961_);
goto v___jp_3964_;
}
}
else
{
lean_dec(v_declName_3977_);
lean_dec(v_declName_3963_);
lean_dec_ref(v_env_3961_);
goto v___jp_3964_;
}
}
else
{
lean_dec_ref(v___x_3976_);
lean_dec(v_declName_3963_);
lean_dec_ref(v_env_3961_);
goto v___jp_3964_;
}
}
v___jp_3964_:
{
lean_object* v___x_3965_; 
v___x_3965_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_3987_, lean_object* v_opts_3988_, lean_object* v_declName_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_3987_, v_opts_3988_, v_declName_3989_);
lean_dec_ref(v_opts_3988_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_3991_, size_t v_i_3992_, size_t v_stop_3993_, lean_object* v_b_3994_){
_start:
{
uint8_t v___x_3996_; 
v___x_3996_ = lean_usize_dec_eq(v_i_3992_, v_stop_3993_);
if (v___x_3996_ == 0)
{
lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3997_ = lean_array_uget_borrowed(v_as_3991_, v_i_3992_);
lean_inc(v___x_3997_);
v___x_3998_ = l_Lean_mkAttributeImplOfEntry(v___x_3997_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v_toAttributeImplCore_4000_; lean_object* v_name_4001_; lean_object* v___x_4002_; size_t v___x_4003_; size_t v___x_4004_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref_known(v___x_3998_, 1);
v_toAttributeImplCore_4000_ = lean_ctor_get(v_a_3999_, 0);
v_name_4001_ = lean_ctor_get(v_toAttributeImplCore_4000_, 1);
lean_inc(v_name_4001_);
v___x_4002_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_3994_, v_name_4001_, v_a_3999_);
v___x_4003_ = ((size_t)1ULL);
v___x_4004_ = lean_usize_add(v_i_3992_, v___x_4003_);
v_i_3992_ = v___x_4004_;
v_b_3994_ = v___x_4002_;
goto _start;
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
lean_dec_ref(v_b_3994_);
v_a_4006_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_3998_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_3998_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
else
{
lean_object* v___x_4014_; 
v___x_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4014_, 0, v_b_3994_);
return v___x_4014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_4015_, lean_object* v_i_4016_, lean_object* v_stop_4017_, lean_object* v_b_4018_, lean_object* v___y_4019_){
_start:
{
size_t v_i_boxed_4020_; size_t v_stop_boxed_4021_; lean_object* v_res_4022_; 
v_i_boxed_4020_ = lean_unbox_usize(v_i_4016_);
lean_dec(v_i_4016_);
v_stop_boxed_4021_ = lean_unbox_usize(v_stop_4017_);
lean_dec(v_stop_4017_);
v_res_4022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4015_, v_i_boxed_4020_, v_stop_boxed_4021_, v_b_4018_);
lean_dec_ref(v_as_4015_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_4023_, size_t v_i_4024_, size_t v_stop_4025_, lean_object* v_b_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v_a_4030_; uint8_t v___x_4034_; 
v___x_4034_ = lean_usize_dec_eq(v_i_4024_, v_stop_4025_);
if (v___x_4034_ == 0)
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; uint8_t v___x_4038_; 
v___x_4035_ = lean_array_uget_borrowed(v_as_4023_, v_i_4024_);
v___x_4036_ = lean_unsigned_to_nat(0u);
v___x_4037_ = lean_array_get_size(v___x_4035_);
v___x_4038_ = lean_nat_dec_lt(v___x_4036_, v___x_4037_);
if (v___x_4038_ == 0)
{
v_a_4030_ = v_b_4026_;
goto v___jp_4029_;
}
else
{
size_t v___x_4039_; size_t v___x_4040_; lean_object* v___x_4041_; 
v___x_4039_ = ((size_t)0ULL);
v___x_4040_ = lean_usize_of_nat(v___x_4037_);
v___x_4041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4035_, v___x_4039_, v___x_4040_, v_b_4026_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
lean_inc(v_a_4042_);
lean_dec_ref_known(v___x_4041_, 1);
v_a_4030_ = v_a_4042_;
goto v___jp_4029_;
}
else
{
return v___x_4041_;
}
}
}
else
{
lean_object* v___x_4043_; 
v___x_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4043_, 0, v_b_4026_);
return v___x_4043_;
}
v___jp_4029_:
{
size_t v___x_4031_; size_t v___x_4032_; 
v___x_4031_ = ((size_t)1ULL);
v___x_4032_ = lean_usize_add(v_i_4024_, v___x_4031_);
v_i_4024_ = v___x_4032_;
v_b_4026_ = v_a_4030_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4044_, lean_object* v_i_4045_, lean_object* v_stop_4046_, lean_object* v_b_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_){
_start:
{
size_t v_i_boxed_4050_; size_t v_stop_boxed_4051_; lean_object* v_res_4052_; 
v_i_boxed_4050_ = lean_unbox_usize(v_i_4045_);
lean_dec(v_i_4045_);
v_stop_boxed_4051_ = lean_unbox_usize(v_stop_4046_);
lean_dec(v_stop_4046_);
v_res_4052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4044_, v_i_boxed_4050_, v_stop_boxed_4051_, v_b_4047_, v___y_4048_);
lean_dec_ref(v___y_4048_);
lean_dec_ref(v_as_4044_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4053_, lean_object* v_a_4054_){
_start:
{
lean_object* v_a_4057_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; uint8_t v___x_4065_; 
v___x_4061_ = l_Lean_attributeMapRef;
v___x_4062_ = lean_st_ref_get(v___x_4061_);
v___x_4063_ = lean_unsigned_to_nat(0u);
v___x_4064_ = lean_array_get_size(v_es_4053_);
v___x_4065_ = lean_nat_dec_lt(v___x_4063_, v___x_4064_);
if (v___x_4065_ == 0)
{
v_a_4057_ = v___x_4062_;
goto v___jp_4056_;
}
else
{
size_t v___x_4066_; size_t v___x_4067_; lean_object* v___x_4068_; 
v___x_4066_ = ((size_t)0ULL);
v___x_4067_ = lean_usize_of_nat(v___x_4064_);
v___x_4068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4053_, v___x_4066_, v___x_4067_, v___x_4062_, v_a_4054_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_object* v_a_4069_; 
v_a_4069_ = lean_ctor_get(v___x_4068_, 0);
lean_inc(v_a_4069_);
lean_dec_ref_known(v___x_4068_, 1);
v_a_4057_ = v_a_4069_;
goto v___jp_4056_;
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
v_a_4070_ = lean_ctor_get(v___x_4068_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___x_4068_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4068_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
v___jp_4056_:
{
lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4058_ = lean_box(0);
v___x_4059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4058_);
lean_ctor_set(v___x_4059_, 1, v_a_4057_);
v___x_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4059_);
return v___x_4060_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4078_, v_a_4079_);
lean_dec_ref(v_a_4079_);
lean_dec_ref(v_es_4078_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4082_, size_t v_i_4083_, size_t v_stop_4084_, lean_object* v_b_4085_, lean_object* v___y_4086_){
_start:
{
lean_object* v___x_4088_; 
v___x_4088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4082_, v_i_4083_, v_stop_4084_, v_b_4085_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4089_, lean_object* v_i_4090_, lean_object* v_stop_4091_, lean_object* v_b_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
size_t v_i_boxed_4095_; size_t v_stop_boxed_4096_; lean_object* v_res_4097_; 
v_i_boxed_4095_ = lean_unbox_usize(v_i_4090_);
lean_dec(v_i_4090_);
v_stop_boxed_4096_ = lean_unbox_usize(v_stop_4091_);
lean_dec(v_stop_4091_);
v_res_4097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4089_, v_i_boxed_4095_, v_stop_boxed_4096_, v_b_4092_, v___y_4093_);
lean_dec_ref(v___y_4093_);
lean_dec_ref(v_as_4089_);
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4098_, lean_object* v_e_4099_){
_start:
{
lean_object* v_snd_4100_; lean_object* v_toAttributeImplCore_4101_; lean_object* v_fst_4102_; lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4120_; 
v_snd_4100_ = lean_ctor_get(v_e_4099_, 1);
lean_inc(v_snd_4100_);
v_toAttributeImplCore_4101_ = lean_ctor_get(v_snd_4100_, 0);
v_fst_4102_ = lean_ctor_get(v_e_4099_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v_e_4099_);
if (v_isSharedCheck_4120_ == 0)
{
lean_object* v_unused_4121_; 
v_unused_4121_ = lean_ctor_get(v_e_4099_, 1);
lean_dec(v_unused_4121_);
v___x_4104_ = v_e_4099_;
v_isShared_4105_ = v_isSharedCheck_4120_;
goto v_resetjp_4103_;
}
else
{
lean_inc(v_fst_4102_);
lean_dec(v_e_4099_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4120_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v_newEntries_4106_; lean_object* v_map_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4119_; 
v_newEntries_4106_ = lean_ctor_get(v_s_4098_, 0);
v_map_4107_ = lean_ctor_get(v_s_4098_, 1);
v_isSharedCheck_4119_ = !lean_is_exclusive(v_s_4098_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4109_ = v_s_4098_;
v_isShared_4110_ = v_isSharedCheck_4119_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_map_4107_);
lean_inc(v_newEntries_4106_);
lean_dec(v_s_4098_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4119_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v_name_4111_; lean_object* v___x_4113_; 
v_name_4111_ = lean_ctor_get(v_toAttributeImplCore_4101_, 1);
lean_inc(v_name_4111_);
if (v_isShared_4105_ == 0)
{
lean_ctor_set_tag(v___x_4104_, 1);
lean_ctor_set(v___x_4104_, 1, v_newEntries_4106_);
v___x_4113_ = v___x_4104_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_fst_4102_);
lean_ctor_set(v_reuseFailAlloc_4118_, 1, v_newEntries_4106_);
v___x_4113_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
lean_object* v___x_4114_; lean_object* v___x_4116_; 
v___x_4114_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4107_, v_name_4111_, v_snd_4100_);
if (v_isShared_4110_ == 0)
{
lean_ctor_set(v___x_4109_, 1, v___x_4114_);
lean_ctor_set(v___x_4109_, 0, v___x_4113_);
v___x_4116_ = v___x_4109_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v___x_4113_);
lean_ctor_set(v_reuseFailAlloc_4117_, 1, v___x_4114_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4122_, lean_object* v_s_4123_){
_start:
{
lean_object* v_newEntries_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v_newEntries_4124_ = lean_ctor_get(v_s_4123_, 0);
lean_inc(v_newEntries_4124_);
lean_dec_ref(v_s_4123_);
v___x_4125_ = l_List_reverse___redArg(v_newEntries_4124_);
v___x_4126_ = lean_array_mk(v___x_4125_);
lean_inc_ref_n(v___x_4126_, 2);
v___x_4127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4126_);
lean_ctor_set(v___x_4127_, 1, v___x_4126_);
lean_ctor_set(v___x_4127_, 2, v___x_4126_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4128_, lean_object* v_s_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4128_, v_s_4129_);
lean_dec_ref(v_x_4128_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4131_){
_start:
{
lean_object* v_newEntries_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4143_; 
v_newEntries_4132_ = lean_ctor_get(v_s_4131_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v_s_4131_);
if (v_isSharedCheck_4143_ == 0)
{
lean_object* v_unused_4144_; 
v_unused_4144_ = lean_ctor_get(v_s_4131_, 1);
lean_dec(v_unused_4144_);
v___x_4134_ = v_s_4131_;
v_isShared_4135_ = v_isSharedCheck_4143_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_newEntries_4132_);
lean_dec(v_s_4131_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4143_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4141_; 
v___x_4136_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4137_ = l_List_lengthTR___redArg(v_newEntries_4132_);
lean_dec(v_newEntries_4132_);
v___x_4138_ = l_Nat_reprFast(v___x_4137_);
v___x_4139_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4139_, 0, v___x_4138_);
if (v_isShared_4135_ == 0)
{
lean_ctor_set_tag(v___x_4134_, 5);
lean_ctor_set(v___x_4134_, 1, v___x_4139_);
lean_ctor_set(v___x_4134_, 0, v___x_4136_);
v___x_4141_ = v___x_4134_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v___x_4136_);
lean_ctor_set(v_reuseFailAlloc_4142_, 1, v___x_4139_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4145_){
_start:
{
lean_object* v_newEntries_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v_newEntries_4146_ = lean_ctor_get(v_s_4145_, 0);
lean_inc(v_newEntries_4146_);
lean_dec_ref(v_s_4145_);
v___x_4147_ = l_List_reverse___redArg(v_newEntries_4146_);
v___x_4148_ = lean_array_mk(v___x_4147_);
return v___x_4148_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___f_4161_; lean_object* v___f_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4158_ = 0;
v___x_4159_ = lean_box(0);
v___x_4160_ = lean_box(2);
v___f_4161_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4162_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4163_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4164_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4165_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4166_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4167_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
lean_ctor_set(v___x_4167_, 1, v___x_4165_);
lean_ctor_set(v___x_4167_, 2, v___x_4164_);
lean_ctor_set(v___x_4167_, 3, v___x_4163_);
lean_ctor_set(v___x_4167_, 4, v___f_4162_);
lean_ctor_set(v___x_4167_, 5, v___f_4161_);
lean_ctor_set(v___x_4167_, 6, v___x_4160_);
lean_ctor_set(v___x_4167_, 7, v___x_4159_);
lean_ctor_set_uint8(v___x_4167_, sizeof(void*)*8, v___x_4158_);
lean_ctor_set_uint8(v___x_4167_, sizeof(void*)*8 + 1, v___x_4158_);
return v___x_4167_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___f_4168_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4169_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4169_);
lean_ctor_set(v___x_4170_, 1, v___f_4168_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4172_; lean_object* v___x_4173_; 
v___x_4172_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4173_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4172_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4176_){
_start:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; uint8_t v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4178_ = l_Lean_attributeMapRef;
v___x_4179_ = lean_st_ref_get(v___x_4178_);
v___x_4180_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4179_, v_n_4176_);
lean_dec(v___x_4179_);
v___x_4181_ = lean_box(v___x_4180_);
v___x_4182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4181_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4183_, lean_object* v_a_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l_Lean_isBuiltinAttribute(v_n_4183_);
lean_dec(v_n_4183_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4186_, lean_object* v_x_4187_){
_start:
{
if (lean_obj_tag(v_x_4187_) == 0)
{
return v_x_4186_;
}
else
{
lean_object* v_key_4188_; lean_object* v_tail_4189_; lean_object* v___x_4190_; 
v_key_4188_ = lean_ctor_get(v_x_4187_, 0);
v_tail_4189_ = lean_ctor_get(v_x_4187_, 2);
lean_inc(v_key_4188_);
v___x_4190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4190_, 0, v_key_4188_);
lean_ctor_set(v___x_4190_, 1, v_x_4186_);
v_x_4186_ = v___x_4190_;
v_x_4187_ = v_tail_4189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4192_, lean_object* v_x_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4192_, v_x_4193_);
lean_dec(v_x_4193_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4195_, size_t v_i_4196_, size_t v_stop_4197_, lean_object* v_b_4198_){
_start:
{
uint8_t v___x_4199_; 
v___x_4199_ = lean_usize_dec_eq(v_i_4196_, v_stop_4197_);
if (v___x_4199_ == 0)
{
lean_object* v___x_4200_; lean_object* v___x_4201_; size_t v___x_4202_; size_t v___x_4203_; 
v___x_4200_ = lean_array_uget_borrowed(v_as_4195_, v_i_4196_);
v___x_4201_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4198_, v___x_4200_);
v___x_4202_ = ((size_t)1ULL);
v___x_4203_ = lean_usize_add(v_i_4196_, v___x_4202_);
v_i_4196_ = v___x_4203_;
v_b_4198_ = v___x_4201_;
goto _start;
}
else
{
return v_b_4198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4205_, lean_object* v_i_4206_, lean_object* v_stop_4207_, lean_object* v_b_4208_){
_start:
{
size_t v_i_boxed_4209_; size_t v_stop_boxed_4210_; lean_object* v_res_4211_; 
v_i_boxed_4209_ = lean_unbox_usize(v_i_4206_);
lean_dec(v_i_4206_);
v_stop_boxed_4210_ = lean_unbox_usize(v_stop_4207_);
lean_dec(v_stop_4207_);
v_res_4211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4205_, v_i_boxed_4209_, v_stop_boxed_4210_, v_b_4208_);
lean_dec_ref(v_as_4205_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v_buckets_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; uint8_t v___x_4219_; 
v___x_4213_ = l_Lean_attributeMapRef;
v___x_4214_ = lean_st_ref_get(v___x_4213_);
v_buckets_4215_ = lean_ctor_get(v___x_4214_, 1);
lean_inc_ref(v_buckets_4215_);
lean_dec(v___x_4214_);
v___x_4216_ = lean_box(0);
v___x_4217_ = lean_unsigned_to_nat(0u);
v___x_4218_ = lean_array_get_size(v_buckets_4215_);
v___x_4219_ = lean_nat_dec_lt(v___x_4217_, v___x_4218_);
if (v___x_4219_ == 0)
{
lean_object* v___x_4220_; 
lean_dec_ref(v_buckets_4215_);
v___x_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4216_);
return v___x_4220_;
}
else
{
size_t v___x_4221_; size_t v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4221_ = ((size_t)0ULL);
v___x_4222_ = lean_usize_of_nat(v___x_4218_);
v___x_4223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4215_, v___x_4221_, v___x_4222_, v___x_4216_);
lean_dec_ref(v_buckets_4215_);
v___x_4224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4223_);
return v___x_4224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4225_){
_start:
{
lean_object* v_res_4226_; 
v_res_4226_ = l_Lean_getBuiltinAttributeNames();
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4228_){
_start:
{
lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4230_ = l_Lean_attributeMapRef;
v___x_4231_ = lean_st_ref_get(v___x_4230_);
v___x_4232_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4231_, v_attrName_4228_);
lean_dec(v___x_4231_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v___x_4233_; uint8_t v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4233_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4234_ = 1;
v___x_4235_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4228_, v___x_4234_);
v___x_4236_ = lean_string_append(v___x_4233_, v___x_4235_);
lean_dec_ref(v___x_4235_);
v___x_4237_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4238_ = lean_string_append(v___x_4236_, v___x_4237_);
v___x_4239_ = lean_mk_io_user_error(v___x_4238_);
v___x_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4239_);
return v___x_4240_;
}
else
{
lean_object* v_val_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
lean_dec(v_attrName_4228_);
v_val_4241_ = lean_ctor_get(v___x_4232_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4232_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___x_4232_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_val_4241_);
lean_dec(v___x_4232_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
lean_ctor_set_tag(v___x_4243_, 0);
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_val_4241_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4249_, lean_object* v_a_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4249_);
return v_res_4251_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4252_, lean_object* v_attrName_4253_){
_start:
{
lean_object* v___x_4254_; lean_object* v_toEnvExtension_4255_; lean_object* v_asyncMode_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; uint8_t v___x_4259_; lean_object* v___x_4260_; lean_object* v_map_4261_; uint8_t v___x_4262_; 
v___x_4254_ = l_Lean_attributeExtension;
v_toEnvExtension_4255_ = lean_ctor_get(v___x_4254_, 0);
v_asyncMode_4256_ = lean_ctor_get(v_toEnvExtension_4255_, 2);
v___x_4257_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4258_ = lean_box(0);
v___x_4259_ = 0;
v___x_4260_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4257_, v___x_4254_, v_env_4252_, v_asyncMode_4256_, v___x_4258_, v___x_4259_);
v_map_4261_ = lean_ctor_get(v___x_4260_, 1);
lean_inc_ref(v_map_4261_);
lean_dec(v___x_4260_);
v___x_4262_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4261_, v_attrName_4253_);
lean_dec_ref(v_map_4261_);
return v___x_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4263_, lean_object* v_attrName_4264_){
_start:
{
uint8_t v_res_4265_; lean_object* v_r_4266_; 
v_res_4265_ = l_Lean_isAttribute(v_env_4263_, v_attrName_4264_);
lean_dec(v_attrName_4264_);
v_r_4266_ = lean_box(v_res_4265_);
return v_r_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4267_){
_start:
{
lean_object* v___x_4268_; lean_object* v_toEnvExtension_4269_; lean_object* v_asyncMode_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; uint8_t v___x_4273_; lean_object* v___x_4274_; lean_object* v_map_4275_; lean_object* v_buckets_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; uint8_t v___x_4280_; 
v___x_4268_ = l_Lean_attributeExtension;
v_toEnvExtension_4269_ = lean_ctor_get(v___x_4268_, 0);
v_asyncMode_4270_ = lean_ctor_get(v_toEnvExtension_4269_, 2);
v___x_4271_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4272_ = lean_box(0);
v___x_4273_ = 0;
v___x_4274_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4271_, v___x_4268_, v_env_4267_, v_asyncMode_4270_, v___x_4272_, v___x_4273_);
v_map_4275_ = lean_ctor_get(v___x_4274_, 1);
lean_inc_ref(v_map_4275_);
lean_dec(v___x_4274_);
v_buckets_4276_ = lean_ctor_get(v_map_4275_, 1);
lean_inc_ref(v_buckets_4276_);
lean_dec_ref(v_map_4275_);
v___x_4277_ = lean_box(0);
v___x_4278_ = lean_unsigned_to_nat(0u);
v___x_4279_ = lean_array_get_size(v_buckets_4276_);
v___x_4280_ = lean_nat_dec_lt(v___x_4278_, v___x_4279_);
if (v___x_4280_ == 0)
{
lean_dec_ref(v_buckets_4276_);
return v___x_4277_;
}
else
{
size_t v___x_4281_; size_t v___x_4282_; lean_object* v___x_4283_; 
v___x_4281_ = ((size_t)0ULL);
v___x_4282_ = lean_usize_of_nat(v___x_4279_);
v___x_4283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4276_, v___x_4281_, v___x_4282_, v___x_4277_);
lean_dec_ref(v_buckets_4276_);
return v___x_4283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4284_, lean_object* v_attrName_4285_){
_start:
{
lean_object* v___x_4286_; lean_object* v_toEnvExtension_4287_; lean_object* v_asyncMode_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; uint8_t v___x_4291_; lean_object* v___x_4292_; lean_object* v_map_4293_; lean_object* v___x_4294_; 
v___x_4286_ = l_Lean_attributeExtension;
v_toEnvExtension_4287_ = lean_ctor_get(v___x_4286_, 0);
v_asyncMode_4288_ = lean_ctor_get(v_toEnvExtension_4287_, 2);
v___x_4289_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4290_ = lean_box(0);
v___x_4291_ = 0;
v___x_4292_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4289_, v___x_4286_, v_env_4284_, v_asyncMode_4288_, v___x_4290_, v___x_4291_);
v_map_4293_ = lean_ctor_get(v___x_4292_, 1);
lean_inc_ref(v_map_4293_);
lean_dec(v___x_4292_);
v___x_4294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4293_, v_attrName_4285_);
lean_dec_ref(v_map_4293_);
if (lean_obj_tag(v___x_4294_) == 0)
{
lean_object* v___x_4295_; uint8_t v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4295_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4296_ = 1;
v___x_4297_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4285_, v___x_4296_);
v___x_4298_ = lean_string_append(v___x_4295_, v___x_4297_);
lean_dec_ref(v___x_4297_);
v___x_4299_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4300_ = lean_string_append(v___x_4298_, v___x_4299_);
v___x_4301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4300_);
return v___x_4301_;
}
else
{
lean_object* v_val_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
lean_dec(v_attrName_4285_);
v_val_4302_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4304_ = v___x_4294_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_val_4302_);
lean_dec(v___x_4294_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4307_; 
if (v_isShared_4305_ == 0)
{
v___x_4307_ = v___x_4304_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_val_4302_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___lam__0(lean_object* v_addEntryFn_4310_, lean_object* v___x_4311_, lean_object* v_s_4312_){
_start:
{
lean_object* v_importedEntries_4313_; lean_object* v_state_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4322_; 
v_importedEntries_4313_ = lean_ctor_get(v_s_4312_, 0);
v_state_4314_ = lean_ctor_get(v_s_4312_, 1);
v_isSharedCheck_4322_ = !lean_is_exclusive(v_s_4312_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4316_ = v_s_4312_;
v_isShared_4317_ = v_isSharedCheck_4322_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_state_4314_);
lean_inc(v_importedEntries_4313_);
lean_dec(v_s_4312_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4322_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v_state_4318_; lean_object* v___x_4320_; 
v_state_4318_ = lean_apply_2(v_addEntryFn_4310_, v_state_4314_, v___x_4311_);
if (v_isShared_4317_ == 0)
{
lean_ctor_set(v___x_4316_, 1, v_state_4318_);
v___x_4320_ = v___x_4316_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_importedEntries_4313_);
lean_ctor_set(v_reuseFailAlloc_4321_, 1, v_state_4318_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
return v___x_4320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4323_, lean_object* v_builderId_4324_, lean_object* v_ref_4325_, lean_object* v_args_4326_){
_start:
{
lean_object* v_entry_4328_; lean_object* v___x_4329_; 
v_entry_4328_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4328_, 0, v_builderId_4324_);
lean_ctor_set(v_entry_4328_, 1, v_ref_4325_);
lean_ctor_set(v_entry_4328_, 2, v_args_4326_);
lean_inc_ref(v_entry_4328_);
v___x_4329_ = l_Lean_mkAttributeImplOfEntry(v_entry_4328_);
if (lean_obj_tag(v___x_4329_) == 0)
{
lean_object* v_a_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4364_; 
v_a_4330_ = lean_ctor_get(v___x_4329_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4329_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4332_ = v___x_4329_;
v_isShared_4333_ = v_isSharedCheck_4364_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_a_4330_);
lean_dec(v___x_4329_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4364_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v_toAttributeImplCore_4334_; lean_object* v_name_4335_; uint8_t v___x_4336_; 
v_toAttributeImplCore_4334_ = lean_ctor_get(v_a_4330_, 0);
v_name_4335_ = lean_ctor_get(v_toAttributeImplCore_4334_, 1);
lean_inc_ref(v_env_4323_);
v___x_4336_ = l_Lean_isAttribute(v_env_4323_, v_name_4335_);
if (v___x_4336_ == 0)
{
lean_object* v___x_4337_; lean_object* v_toEnvExtension_4338_; lean_object* v_addEntryFn_4339_; lean_object* v_asyncMode_4340_; uint8_t v_logWrites_4341_; lean_object* v___x_4342_; lean_object* v___f_4343_; lean_object* v___x_4344_; uint8_t v___x_4345_; 
v___x_4337_ = l_Lean_attributeExtension;
v_toEnvExtension_4338_ = lean_ctor_get(v___x_4337_, 0);
v_addEntryFn_4339_ = lean_ctor_get(v___x_4337_, 3);
v_asyncMode_4340_ = lean_ctor_get(v_toEnvExtension_4338_, 2);
v_logWrites_4341_ = lean_ctor_get_uint8(v_toEnvExtension_4338_, sizeof(void*)*6);
v___x_4342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4342_, 0, v_entry_4328_);
lean_ctor_set(v___x_4342_, 1, v_a_4330_);
lean_inc(v_addEntryFn_4339_);
v___f_4343_ = lean_alloc_closure((void*)(l_Lean_registerAttributeOfBuilder___lam__0), 3, 2);
lean_closure_set(v___f_4343_, 0, v_addEntryFn_4339_);
lean_closure_set(v___f_4343_, 1, v___x_4342_);
v___x_4344_ = lean_box(0);
v___x_4345_ = 1;
if (v_logWrites_4341_ == 0)
{
lean_object* v___x_4346_; lean_object* v___x_4348_; 
lean_inc_ref(v_toEnvExtension_4338_);
v___x_4346_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4338_, v_env_4323_, v___f_4343_, v_asyncMode_4340_, v___x_4344_, v___x_4345_);
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 0, v___x_4346_);
v___x_4348_ = v___x_4332_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v___x_4346_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
else
{
lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4353_; 
lean_inc_ref_n(v_toEnvExtension_4338_, 2);
v___x_4350_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4338_, v_env_4323_);
lean_dec_ref(v_env_4323_);
v___x_4351_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4338_, v___x_4350_, v___f_4343_, v_asyncMode_4340_, v___x_4344_, v___x_4345_);
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 0, v___x_4351_);
v___x_4353_ = v___x_4332_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v___x_4351_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
else
{
lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4362_; 
lean_inc(v_name_4335_);
lean_dec(v_a_4330_);
lean_dec_ref_known(v_entry_4328_, 3);
lean_dec_ref(v_env_4323_);
v___x_4355_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4356_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4335_, v___x_4336_);
v___x_4357_ = lean_string_append(v___x_4355_, v___x_4356_);
lean_dec_ref(v___x_4356_);
v___x_4358_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4359_ = lean_string_append(v___x_4357_, v___x_4358_);
v___x_4360_ = lean_mk_io_user_error(v___x_4359_);
if (v_isShared_4333_ == 0)
{
lean_ctor_set_tag(v___x_4332_, 1);
lean_ctor_set(v___x_4332_, 0, v___x_4360_);
v___x_4362_ = v___x_4332_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v___x_4360_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
}
else
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4372_; 
lean_dec_ref_known(v_entry_4328_, 3);
lean_dec_ref(v_env_4323_);
v_a_4365_ = lean_ctor_get(v___x_4329_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4329_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4367_ = v___x_4329_;
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_dec(v___x_4329_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4370_; 
if (v_isShared_4368_ == 0)
{
v___x_4370_ = v___x_4367_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_a_4365_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4373_, lean_object* v_builderId_4374_, lean_object* v_ref_4375_, lean_object* v_args_4376_, lean_object* v_a_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l_Lean_registerAttributeOfBuilder(v_env_4373_, v_builderId_4374_, v_ref_4375_, v_args_4376_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
if (lean_obj_tag(v_x_4379_) == 0)
{
lean_object* v_a_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; 
v_a_4383_ = lean_ctor_get(v_x_4379_, 0);
lean_inc(v_a_4383_);
lean_dec_ref_known(v_x_4379_, 1);
v___x_4384_ = l_Lean_stringToMessageData(v_a_4383_);
v___x_4385_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4384_, v___y_4380_, v___y_4381_);
return v___x_4385_;
}
else
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
v_a_4386_ = lean_ctor_get(v_x_4379_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v_x_4379_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4388_ = v_x_4379_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v_x_4379_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
lean_ctor_set_tag(v___x_4388_, 0);
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4386_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
return v___x_4391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v_res_4398_; 
v_res_4398_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4394_, v___y_4395_, v___y_4396_);
lean_dec(v___y_4396_);
lean_dec_ref(v___y_4395_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4399_, lean_object* v_attrName_4400_, lean_object* v_stx_4401_, uint8_t v_kind_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_){
_start:
{
lean_object* v___x_4406_; lean_object* v_env_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4406_ = lean_st_ref_get(v_a_4404_);
v_env_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc_ref(v_env_4407_);
lean_dec(v___x_4406_);
v___x_4408_ = l_Lean_getAttributeImpl(v_env_4407_, v_attrName_4400_);
v___x_4409_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4408_, v_a_4403_, v_a_4404_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v_add_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
v_add_4411_ = lean_ctor_get(v_a_4410_, 1);
lean_inc_ref(v_add_4411_);
lean_dec(v_a_4410_);
v___x_4412_ = lean_box(v_kind_4402_);
lean_inc(v_a_4404_);
lean_inc_ref(v_a_4403_);
v___x_4413_ = lean_apply_6(v_add_4411_, v_declName_4399_, v_stx_4401_, v___x_4412_, v_a_4403_, v_a_4404_, lean_box(0));
return v___x_4413_;
}
else
{
lean_object* v_a_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4421_; 
lean_dec(v_stx_4401_);
lean_dec(v_declName_4399_);
v_a_4414_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4421_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4416_ = v___x_4409_;
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_a_4414_);
lean_dec(v___x_4409_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4419_; 
if (v_isShared_4417_ == 0)
{
v___x_4419_ = v___x_4416_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_a_4414_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
return v___x_4419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4422_, lean_object* v_attrName_4423_, lean_object* v_stx_4424_, lean_object* v_kind_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_){
_start:
{
uint8_t v_kind_boxed_4429_; lean_object* v_res_4430_; 
v_kind_boxed_4429_ = lean_unbox(v_kind_4425_);
v_res_4430_ = l_Lean_Attribute_add(v_declName_4422_, v_attrName_4423_, v_stx_4424_, v_kind_boxed_4429_, v_a_4426_, v_a_4427_);
lean_dec(v_a_4427_);
lean_dec_ref(v_a_4426_);
return v_res_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4431_, lean_object* v_x_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_){
_start:
{
lean_object* v___x_4436_; 
v___x_4436_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4432_, v___y_4433_, v___y_4434_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4437_, lean_object* v_x_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_){
_start:
{
lean_object* v_res_4442_; 
v_res_4442_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4437_, v_x_4438_, v___y_4439_, v___y_4440_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4443_, lean_object* v_attrName_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_){
_start:
{
lean_object* v___x_4448_; lean_object* v_env_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4448_ = lean_st_ref_get(v_a_4446_);
v_env_4449_ = lean_ctor_get(v___x_4448_, 0);
lean_inc_ref(v_env_4449_);
lean_dec(v___x_4448_);
v___x_4450_ = l_Lean_getAttributeImpl(v_env_4449_, v_attrName_4444_);
v___x_4451_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4450_, v_a_4445_, v_a_4446_);
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_object* v_a_4452_; lean_object* v_erase_4453_; lean_object* v___x_4454_; 
v_a_4452_ = lean_ctor_get(v___x_4451_, 0);
lean_inc(v_a_4452_);
lean_dec_ref_known(v___x_4451_, 1);
v_erase_4453_ = lean_ctor_get(v_a_4452_, 2);
lean_inc_ref(v_erase_4453_);
lean_dec(v_a_4452_);
lean_inc(v_a_4446_);
lean_inc_ref(v_a_4445_);
v___x_4454_ = lean_apply_4(v_erase_4453_, v_declName_4443_, v_a_4445_, v_a_4446_, lean_box(0));
return v___x_4454_;
}
else
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4462_; 
lean_dec(v_declName_4443_);
v_a_4455_ = lean_ctor_get(v___x_4451_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v___x_4451_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4457_ = v___x_4451_;
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v___x_4451_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4460_; 
if (v_isShared_4458_ == 0)
{
v___x_4460_ = v___x_4457_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_a_4455_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4463_, lean_object* v_attrName_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_){
_start:
{
lean_object* v_res_4468_; 
v_res_4468_ = l_Lean_Attribute_erase(v_declName_4463_, v_attrName_4464_, v_a_4465_, v_a_4466_);
lean_dec(v_a_4466_);
lean_dec_ref(v_a_4465_);
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___lam__0(lean_object* v___y_4469_, lean_object* v_ps_4470_){
_start:
{
lean_object* v_importedEntries_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4478_; 
v_importedEntries_4471_ = lean_ctor_get(v_ps_4470_, 0);
v_isSharedCheck_4478_ = !lean_is_exclusive(v_ps_4470_);
if (v_isSharedCheck_4478_ == 0)
{
lean_object* v_unused_4479_; 
v_unused_4479_ = lean_ctor_get(v_ps_4470_, 1);
lean_dec(v_unused_4479_);
v___x_4473_ = v_ps_4470_;
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_importedEntries_4471_);
lean_dec(v_ps_4470_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4476_; 
if (v_isShared_4474_ == 0)
{
lean_ctor_set(v___x_4473_, 1, v___y_4469_);
v___x_4476_ = v___x_4473_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_importedEntries_4471_);
lean_ctor_set(v_reuseFailAlloc_4477_, 1, v___y_4469_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
return v___x_4476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4480_, lean_object* v_x_4481_){
_start:
{
if (lean_obj_tag(v_x_4481_) == 0)
{
return v_x_4480_;
}
else
{
lean_object* v_key_4482_; lean_object* v_value_4483_; lean_object* v_tail_4484_; lean_object* v_newEntries_4485_; lean_object* v_map_4486_; uint8_t v___x_4487_; 
v_key_4482_ = lean_ctor_get(v_x_4481_, 0);
lean_inc(v_key_4482_);
v_value_4483_ = lean_ctor_get(v_x_4481_, 1);
lean_inc(v_value_4483_);
v_tail_4484_ = lean_ctor_get(v_x_4481_, 2);
lean_inc(v_tail_4484_);
lean_dec_ref_known(v_x_4481_, 3);
v_newEntries_4485_ = lean_ctor_get(v_x_4480_, 0);
v_map_4486_ = lean_ctor_get(v_x_4480_, 1);
v___x_4487_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4486_, v_key_4482_);
if (v___x_4487_ == 0)
{
lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4496_; 
lean_inc_ref(v_map_4486_);
lean_inc(v_newEntries_4485_);
v_isSharedCheck_4496_ = !lean_is_exclusive(v_x_4480_);
if (v_isSharedCheck_4496_ == 0)
{
lean_object* v_unused_4497_; lean_object* v_unused_4498_; 
v_unused_4497_ = lean_ctor_get(v_x_4480_, 1);
lean_dec(v_unused_4497_);
v_unused_4498_ = lean_ctor_get(v_x_4480_, 0);
lean_dec(v_unused_4498_);
v___x_4489_ = v_x_4480_;
v_isShared_4490_ = v_isSharedCheck_4496_;
goto v_resetjp_4488_;
}
else
{
lean_dec(v_x_4480_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4496_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4491_; lean_object* v___x_4493_; 
v___x_4491_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4486_, v_key_4482_, v_value_4483_);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 1, v___x_4491_);
v___x_4493_ = v___x_4489_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_newEntries_4485_);
lean_ctor_set(v_reuseFailAlloc_4495_, 1, v___x_4491_);
v___x_4493_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
v_x_4480_ = v___x_4493_;
v_x_4481_ = v_tail_4484_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4483_);
lean_dec(v_key_4482_);
v_x_4481_ = v_tail_4484_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4500_, size_t v_i_4501_, size_t v_stop_4502_, lean_object* v_b_4503_){
_start:
{
uint8_t v___x_4504_; 
v___x_4504_ = lean_usize_dec_eq(v_i_4501_, v_stop_4502_);
if (v___x_4504_ == 0)
{
lean_object* v___x_4505_; lean_object* v___x_4506_; size_t v___x_4507_; size_t v___x_4508_; 
v___x_4505_ = lean_array_uget_borrowed(v_as_4500_, v_i_4501_);
lean_inc(v___x_4505_);
v___x_4506_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4503_, v___x_4505_);
v___x_4507_ = ((size_t)1ULL);
v___x_4508_ = lean_usize_add(v_i_4501_, v___x_4507_);
v_i_4501_ = v___x_4508_;
v_b_4503_ = v___x_4506_;
goto _start;
}
else
{
return v_b_4503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4510_, lean_object* v_i_4511_, lean_object* v_stop_4512_, lean_object* v_b_4513_){
_start:
{
size_t v_i_boxed_4514_; size_t v_stop_boxed_4515_; lean_object* v_res_4516_; 
v_i_boxed_4514_ = lean_unbox_usize(v_i_4511_);
lean_dec(v_i_4511_);
v_stop_boxed_4515_ = lean_unbox_usize(v_stop_4512_);
lean_dec(v_stop_4512_);
v_res_4516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4510_, v_i_boxed_4514_, v_stop_boxed_4515_, v_b_4513_);
lean_dec_ref(v_as_4510_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4517_){
_start:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v_toEnvExtension_4523_; lean_object* v_asyncMode_4524_; uint8_t v_logWrites_4525_; lean_object* v___y_4527_; lean_object* v_buckets_4536_; lean_object* v___x_4537_; uint8_t v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; uint8_t v___x_4542_; 
v___x_4519_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4520_ = l_Lean_attributeMapRef;
v___x_4521_ = lean_st_ref_get(v___x_4520_);
v___x_4522_ = l_Lean_attributeExtension;
v_toEnvExtension_4523_ = lean_ctor_get(v___x_4522_, 0);
v_asyncMode_4524_ = lean_ctor_get(v_toEnvExtension_4523_, 2);
v_logWrites_4525_ = lean_ctor_get_uint8(v_toEnvExtension_4523_, sizeof(void*)*6);
v_buckets_4536_ = lean_ctor_get(v___x_4521_, 1);
lean_inc_ref(v_buckets_4536_);
lean_dec(v___x_4521_);
v___x_4537_ = lean_box(0);
v___x_4538_ = 0;
lean_inc_ref(v_env_4517_);
v___x_4539_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4519_, v___x_4522_, v_env_4517_, v_asyncMode_4524_, v___x_4537_, v___x_4538_);
v___x_4540_ = lean_unsigned_to_nat(0u);
v___x_4541_ = lean_array_get_size(v_buckets_4536_);
v___x_4542_ = lean_nat_dec_lt(v___x_4540_, v___x_4541_);
if (v___x_4542_ == 0)
{
lean_dec_ref(v_buckets_4536_);
v___y_4527_ = v___x_4539_;
goto v___jp_4526_;
}
else
{
size_t v___x_4543_; size_t v___x_4544_; lean_object* v___x_4545_; 
v___x_4543_ = ((size_t)0ULL);
v___x_4544_ = lean_usize_of_nat(v___x_4541_);
v___x_4545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4536_, v___x_4543_, v___x_4544_, v___x_4539_);
lean_dec_ref(v_buckets_4536_);
v___y_4527_ = v___x_4545_;
goto v___jp_4526_;
}
v___jp_4526_:
{
lean_object* v___f_4528_; lean_object* v___x_4529_; uint8_t v___x_4530_; 
v___f_4528_ = lean_alloc_closure((void*)(l_Lean_updateEnvAttributesImpl___lam__0), 2, 1);
lean_closure_set(v___f_4528_, 0, v___y_4527_);
v___x_4529_ = lean_box(0);
v___x_4530_ = 1;
if (v_logWrites_4525_ == 0)
{
lean_object* v___x_4531_; lean_object* v___x_4532_; 
lean_inc_ref(v_toEnvExtension_4523_);
v___x_4531_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4523_, v_env_4517_, v___f_4528_, v_asyncMode_4524_, v___x_4529_, v___x_4530_);
v___x_4532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4532_, 0, v___x_4531_);
return v___x_4532_;
}
else
{
lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; 
lean_inc_ref_n(v_toEnvExtension_4523_, 2);
v___x_4533_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4523_, v_env_4517_);
lean_dec_ref(v_env_4517_);
v___x_4534_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4523_, v___x_4533_, v___f_4528_, v_asyncMode_4524_, v___x_4529_, v___x_4530_);
v___x_4535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4535_, 0, v___x_4534_);
return v___x_4535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4546_, lean_object* v_a_4547_){
_start:
{
lean_object* v_res_4548_; 
v_res_4548_ = lean_update_env_attributes(v_env_4546_);
return v_res_4548_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v_size_4552_; lean_object* v___x_4553_; 
v___x_4550_ = l_Lean_attributeMapRef;
v___x_4551_ = lean_st_ref_get(v___x_4550_);
v_size_4552_ = lean_ctor_get(v___x_4551_, 0);
lean_inc(v_size_4552_);
lean_dec(v___x_4551_);
v___x_4553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4553_, 0, v_size_4552_);
return v___x_4553_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4554_){
_start:
{
lean_object* v_res_4555_; 
v_res_4555_ = lean_get_num_attributes();
return v_res_4555_;
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
