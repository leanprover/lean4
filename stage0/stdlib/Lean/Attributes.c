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
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_1429509408____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_1429509408____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_automationAttrsRef;
LEAN_EXPORT lean_object* l_Lean_registerAutomationAttr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerAutomationAttr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAutomationAttr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAutomationAttr___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_1429509408____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = l_Lean_NameSet_empty;
v___x_660_ = lean_st_mk_ref(v___x_659_);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_1429509408____hygCtx___hyg_2____boxed(lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_1429509408____hygCtx___hyg_2_();
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAutomationAttr(lean_object* v_attrName_664_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_666_ = l_Lean_automationAttrsRef;
v___x_667_ = lean_st_ref_take(v___x_666_);
v___x_668_ = l_Lean_NameSet_insert(v___x_667_, v_attrName_664_);
v___x_669_ = lean_st_ref_put(v___x_666_, v___x_668_);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAutomationAttr___boxed(lean_object* v_attrName_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_registerAutomationAttr(v_attrName_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAutomationAttr(lean_object* v_attrName_674_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_676_ = l_Lean_automationAttrsRef;
v___x_677_ = lean_st_ref_get(v___x_676_);
v___x_678_ = l_Lean_NameSet_contains(v___x_677_, v_attrName_674_);
lean_dec(v___x_677_);
v___x_679_ = lean_box(v___x_678_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAutomationAttr___boxed(lean_object* v_attrName_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_isAutomationAttr(v_attrName_681_);
lean_dec(v_attrName_681_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object* v_ref_684_, lean_object* v_msg_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_toCold_689_; lean_object* v_currRecDepth_690_; lean_object* v_ref_691_; uint16_t v_optionFlags_692_; uint8_t v_suppressElabErrors_693_; uint8_t v_checkDeprecated_694_; uint8_t v_isRecordingDeps_695_; lean_object* v_ref_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v_toCold_689_ = lean_ctor_get(v___y_686_, 0);
v_currRecDepth_690_ = lean_ctor_get(v___y_686_, 1);
v_ref_691_ = lean_ctor_get(v___y_686_, 2);
v_optionFlags_692_ = lean_ctor_get_uint16(v___y_686_, sizeof(void*)*3);
v_suppressElabErrors_693_ = lean_ctor_get_uint8(v___y_686_, sizeof(void*)*3 + 2);
v_checkDeprecated_694_ = lean_ctor_get_uint8(v___y_686_, sizeof(void*)*3 + 3);
v_isRecordingDeps_695_ = lean_ctor_get_uint8(v___y_686_, sizeof(void*)*3 + 4);
v_ref_696_ = l_Lean_replaceRef(v_ref_684_, v_ref_691_);
lean_inc(v_currRecDepth_690_);
lean_inc_ref(v_toCold_689_);
v___x_697_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_697_, 0, v_toCold_689_);
lean_ctor_set(v___x_697_, 1, v_currRecDepth_690_);
lean_ctor_set(v___x_697_, 2, v_ref_696_);
lean_ctor_set_uint16(v___x_697_, sizeof(void*)*3, v_optionFlags_692_);
lean_ctor_set_uint8(v___x_697_, sizeof(void*)*3 + 2, v_suppressElabErrors_693_);
lean_ctor_set_uint8(v___x_697_, sizeof(void*)*3 + 3, v_checkDeprecated_694_);
lean_ctor_set_uint8(v___x_697_, sizeof(void*)*3 + 4, v_isRecordingDeps_695_);
v___x_698_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_685_, v___x_697_, v___y_687_);
lean_dec_ref_known(v___x_697_, 3);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object* v_ref_699_, lean_object* v_msg_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_699_, v_msg_700_, v___y_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v_ref_699_);
return v_res_704_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__3));
v___x_714_ = l_Lean_stringToMessageData(v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object* v_stx_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_735_; uint8_t v___x_736_; 
lean_inc(v_stx_721_);
v___x_725_ = l_Lean_Syntax_getKind(v_stx_721_);
v___x_735_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_736_ = lean_name_eq(v___x_725_, v___x_735_);
if (v___x_736_ == 0)
{
goto v___jp_726_;
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = l_Lean_Syntax_getArg(v_stx_721_, v___x_737_);
v___x_739_ = l_Lean_Syntax_isNone(v___x_738_);
lean_dec(v___x_738_);
if (v___x_739_ == 0)
{
goto v___jp_726_;
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_740_ = lean_unsigned_to_nat(2u);
v___x_741_ = l_Lean_Syntax_getArg(v_stx_721_, v___x_740_);
v___x_742_ = l_Lean_Syntax_isNone(v___x_741_);
lean_dec(v___x_741_);
if (v___x_742_ == 0)
{
goto v___jp_726_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; 
lean_dec(v___x_725_);
lean_dec(v_stx_721_);
v___x_743_ = lean_box(0);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
}
v___jp_726_:
{
lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_727_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__2));
v___x_728_ = lean_name_eq(v___x_725_, v___x_727_);
lean_dec(v___x_725_);
if (v___x_728_ == 0)
{
if (lean_obj_tag(v_stx_721_) == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_box(0);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_obj_once(&l_Lean_Attribute_Builtin_ensureNoArgs___closed__4, &l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once, _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4);
v___x_732_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_721_, v___x_731_, v_a_722_, v_a_723_);
lean_dec(v_stx_721_);
return v___x_732_;
}
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; 
lean_dec(v_stx_721_);
v___x_733_ = lean_box(0);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object* v_stx_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_745_, v_a_746_, v_a_747_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object* v_00_u03b1_750_, lean_object* v_ref_751_, lean_object* v_msg_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_751_, v_msg_752_, v___y_753_, v___y_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object* v_00_u03b1_757_, lean_object* v_ref_758_, lean_object* v_msg_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(v_00_u03b1_757_, v_ref_758_, v_msg_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v_ref_758_);
return v_res_763_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__4));
v___x_778_ = l_Lean_stringToMessageData(v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object* v_stx_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
lean_inc(v_stx_779_);
v___x_791_ = l_Lean_Syntax_getKind(v_stx_779_);
v___x_792_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_793_ = lean_name_eq(v___x_791_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_795_ = lean_name_eq(v___x_791_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_797_ = lean_name_eq(v___x_791_, v___x_796_);
lean_dec(v___x_791_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_799_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_779_, v___x_798_, v_a_780_, v_a_781_);
lean_dec(v_stx_779_);
return v___x_799_;
}
else
{
goto v___jp_783_;
}
}
else
{
lean_dec(v___x_791_);
goto v___jp_783_;
}
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
lean_dec(v___x_791_);
v___x_800_ = lean_unsigned_to_nat(1u);
v___x_801_ = l_Lean_Syntax_getArg(v_stx_779_, v___x_800_);
lean_dec(v_stx_779_);
v___x_802_ = l_Lean_Syntax_isNone(v___x_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = l_Lean_Syntax_getArg(v___x_801_, v___x_803_);
lean_dec(v___x_801_);
v___x_805_ = l_Lean_Syntax_isIdent(v___x_804_);
if (v___x_805_ == 0)
{
lean_dec(v___x_804_);
goto v___jp_788_;
}
else
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
v___x_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
return v___x_807_;
}
}
else
{
lean_dec(v___x_801_);
goto v___jp_788_;
}
}
v___jp_783_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_784_ = lean_unsigned_to_nat(1u);
v___x_785_ = l_Lean_Syntax_getArg(v_stx_779_, v___x_784_);
lean_dec(v_stx_779_);
v___x_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
v___x_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
return v___x_787_;
}
v___jp_788_:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_box(0);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
return v___x_790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object* v_stx_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_808_, v_a_809_, v_a_810_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
return v_res_812_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent___closed__1(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent___closed__0));
v___x_815_ = l_Lean_stringToMessageData(v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v___x_820_; 
lean_inc(v_stx_816_);
v___x_820_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_816_, v_a_817_, v_a_818_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_834_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_834_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_834_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_834_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
if (lean_obj_tag(v_a_821_) == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
lean_del_object(v___x_823_);
v___x_825_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent___closed__1, &l_Lean_Attribute_Builtin_getIdent___closed__1_once, _init_l_Lean_Attribute_Builtin_getIdent___closed__1);
lean_inc(v_stx_816_);
v___x_826_ = l_Lean_MessageData_ofSyntax(v_stx_816_);
v___x_827_ = l_Lean_indentD(v___x_826_);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_825_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_816_, v___x_828_, v_a_817_, v_a_818_);
lean_dec(v_stx_816_);
return v___x_829_;
}
else
{
lean_object* v_val_830_; lean_object* v___x_832_; 
lean_dec(v_stx_816_);
v_val_830_ = lean_ctor_get(v_a_821_, 0);
lean_inc(v_val_830_);
lean_dec_ref_known(v_a_821_, 1);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v_val_830_);
v___x_832_ = v___x_823_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_val_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec(v_stx_816_);
v_a_835_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_820_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_820_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
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
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_Attribute_Builtin_getIdent(v_stx_843_, v_a_844_, v_a_845_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_848_, v_a_849_, v_a_850_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_873_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_873_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_873_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_873_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
if (lean_obj_tag(v_a_853_) == 0)
{
lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_857_ = lean_box(0);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_857_);
v___x_859_ = v___x_855_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
else
{
lean_object* v_val_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_872_; 
v_val_861_ = lean_ctor_get(v_a_853_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v_a_853_);
if (v_isSharedCheck_872_ == 0)
{
v___x_863_ = v_a_853_;
v_isShared_864_ = v_isSharedCheck_872_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_val_861_);
lean_dec(v_a_853_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_872_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_865_ = l_Lean_Syntax_getId(v_val_861_);
lean_dec(v_val_861_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_865_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_871_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_869_; 
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_867_);
v___x_869_ = v___x_855_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
v_a_874_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_852_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_852_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_882_, v_a_883_, v_a_884_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_Attribute_Builtin_getIdent(v_stx_887_, v_a_888_, v_a_889_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_900_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_900_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_900_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_900_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = l_Lean_Syntax_getId(v_a_892_);
lean_dec(v_a_892_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_896_);
v___x_898_ = v___x_894_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
v_a_901_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_891_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_891_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Attribute_Builtin_getId(v_stx_909_, v_a_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
return v_res_913_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_916_ = l_Lean_stringToMessageData(v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
uint8_t v___x_921_; 
v___x_921_ = l_Lean_Syntax_isNone(v_optPrioStx_917_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = lean_unsigned_to_nat(0u);
v___x_923_ = l_Lean_Syntax_getArg(v_optPrioStx_917_, v___x_922_);
v___x_924_ = l_Lean_Syntax_isNatLit_x3f(v___x_923_);
lean_dec(v___x_923_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_925_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_917_);
v___x_926_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_917_);
v___x_927_ = l_Lean_indentD(v___x_926_);
v___x_928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_925_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_917_, v___x_928_, v_a_918_, v_a_919_);
lean_dec(v_optPrioStx_917_);
return v___x_929_;
}
else
{
lean_object* v_val_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec(v_optPrioStx_917_);
v_val_930_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_924_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_val_930_);
lean_dec(v___x_924_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set_tag(v___x_932_, 0);
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_val_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec(v_optPrioStx_917_);
v___x_938_ = lean_unsigned_to_nat(1000u);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
return v___x_939_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object* v_optPrioStx_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_940_, v_a_941_, v_a_942_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
return v_res_944_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getPrio___closed__1(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = ((lean_object*)(l_Lean_Attribute_Builtin_getPrio___closed__0));
v___x_947_ = l_Lean_stringToMessageData(v___x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; 
lean_inc(v_stx_948_);
v___x_952_ = l_Lean_Syntax_getKind(v_stx_948_);
v___x_953_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_954_ = lean_name_eq(v___x_952_, v___x_953_);
lean_dec(v___x_952_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_955_ = lean_obj_once(&l_Lean_Attribute_Builtin_getPrio___closed__1, &l_Lean_Attribute_Builtin_getPrio___closed__1_once, _init_l_Lean_Attribute_Builtin_getPrio___closed__1);
lean_inc(v_stx_948_);
v___x_956_ = l_Lean_MessageData_ofSyntax(v_stx_948_);
v___x_957_ = l_Lean_indentD(v___x_956_);
v___x_958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_955_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_948_, v___x_958_, v_a_949_, v_a_950_);
lean_dec(v_stx_948_);
return v___x_959_;
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_960_ = lean_unsigned_to_nat(1u);
v___x_961_ = l_Lean_Syntax_getArg(v_stx_948_, v___x_960_);
lean_dec(v_stx_948_);
v___x_962_ = l_Lean_getAttrParamOptPrio(v___x_961_, v_a_949_, v_a_950_);
return v___x_962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_Attribute_Builtin_getPrio(v_stx_963_, v_a_964_, v_a_965_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
return v_res_967_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_970_ = l_Lean_stringToMessageData(v___x_969_);
return v___x_970_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_973_ = l_Lean_stringToMessageData(v___x_972_);
return v___x_973_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_976_ = l_Lean_stringToMessageData(v___x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_977_, lean_object* v_inst_978_, lean_object* v_name_979_, uint8_t v_kind_980_){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___y_987_; 
v___x_981_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_982_ = l_Lean_MessageData_ofName(v_name_979_);
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
switch(v_kind_980_)
{
case 0:
{
lean_object* v___x_994_; 
v___x_994_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_987_ = v___x_994_;
goto v___jp_986_;
}
case 1:
{
lean_object* v___x_995_; 
v___x_995_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_987_ = v___x_995_;
goto v___jp_986_;
}
default: 
{
lean_object* v___x_996_; 
v___x_996_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_987_ = v___x_996_;
goto v___jp_986_;
}
}
v___jp_986_:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
lean_inc_ref(v___y_987_);
v___x_988_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_988_, 0, v___y_987_);
v___x_989_ = l_Lean_MessageData_ofFormat(v___x_988_);
v___x_990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_985_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = l_Lean_throwError___redArg(v_inst_977_, v_inst_978_, v___x_992_);
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_name_999_, lean_object* v_kind_1000_){
_start:
{
uint8_t v_kind_boxed_1001_; lean_object* v_res_1002_; 
v_kind_boxed_1001_ = lean_unbox(v_kind_1000_);
v_res_1002_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_997_, v_inst_998_, v_name_999_, v_kind_boxed_1001_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_1003_, lean_object* v_inst_1004_, lean_object* v_inst_1005_, lean_object* v_00_u03b1_1006_, lean_object* v_name_1007_, uint8_t v_kind_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_1004_, v_inst_1005_, v_name_1007_, v_kind_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_1010_, lean_object* v_inst_1011_, lean_object* v_inst_1012_, lean_object* v_00_u03b1_1013_, lean_object* v_name_1014_, lean_object* v_kind_1015_){
_start:
{
uint8_t v_kind_boxed_1016_; lean_object* v_res_1017_; 
v_kind_boxed_1016_ = lean_unbox(v_kind_1015_);
v_res_1017_ = l_Lean_throwAttrMustBeGlobal(v_m_1010_, v_inst_1011_, v_inst_1012_, v_00_u03b1_1013_, v_name_1014_, v_kind_boxed_1016_);
return v_res_1017_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_1020_ = l_Lean_stringToMessageData(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_1023_ = l_Lean_stringToMessageData(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_1026_ = l_Lean_stringToMessageData(v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_1027_, lean_object* v_inst_1028_, lean_object* v_attrName_1029_, lean_object* v_declName_1030_){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1031_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1032_ = l_Lean_MessageData_ofName(v_attrName_1029_);
v___x_1033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = 0;
v___x_1037_ = l_Lean_MessageData_ofConstName(v_declName_1030_, v___x_1036_);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1035_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = l_Lean_throwError___redArg(v_inst_1027_, v_inst_1028_, v___x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1042_, lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v_00_u03b1_1045_, lean_object* v_attrName_1046_, lean_object* v_declName_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1043_, v_inst_1044_, v_attrName_1046_, v_declName_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1051_ = l_Lean_stringToMessageData(v___x_1050_);
return v___x_1051_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1054_ = l_Lean_stringToMessageData(v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1055_, lean_object* v_inst_1056_, lean_object* v_attrName_1057_, lean_object* v_declName_1058_, lean_object* v_asyncPrefix_x3f_1059_){
_start:
{
lean_object* v___y_1061_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1059_) == 0)
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_MessageData_nil;
v___y_1061_ = v___x_1074_;
goto v___jp_1060_;
}
else
{
lean_object* v_val_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v_val_1075_ = lean_ctor_get(v_asyncPrefix_x3f_1059_, 0);
lean_inc(v_val_1075_);
lean_dec_ref_known(v_asyncPrefix_x3f_1059_, 1);
v___x_1076_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1077_ = l_Lean_MessageData_ofName(v_val_1075_);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___y_1061_ = v___x_1080_;
goto v___jp_1060_;
}
v___jp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1062_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1063_ = l_Lean_MessageData_ofName(v_attrName_1057_);
v___x_1064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1062_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = 0;
v___x_1068_ = l_Lean_MessageData_ofConstName(v_declName_1058_, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1066_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v___y_1061_);
v___x_1073_ = l_Lean_throwError___redArg(v_inst_1055_, v_inst_1056_, v___x_1072_);
return v___x_1073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1081_, lean_object* v_inst_1082_, lean_object* v_inst_1083_, lean_object* v_00_u03b1_1084_, lean_object* v_attrName_1085_, lean_object* v_declName_1086_, lean_object* v_asyncPrefix_x3f_1087_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1082_, v_inst_1083_, v_attrName_1085_, v_declName_1086_, v_asyncPrefix_x3f_1087_);
return v___x_1088_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1091_ = l_Lean_stringToMessageData(v___x_1090_);
return v___x_1091_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1094_ = l_Lean_stringToMessageData(v___x_1093_);
return v___x_1094_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1097_ = l_Lean_stringToMessageData(v___x_1096_);
return v___x_1097_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1100_ = l_Lean_stringToMessageData(v___x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1101_, lean_object* v_inst_1102_, lean_object* v_attrName_1103_, lean_object* v_declName_1104_, lean_object* v_givenType_1105_, lean_object* v_expectedType_1106_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1107_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1108_ = l_Lean_MessageData_ofName(v_attrName_1103_);
lean_inc_ref(v___x_1108_);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1109_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = 0;
v___x_1113_ = l_Lean_MessageData_ofConstName(v_declName_1104_, v___x_1112_);
v___x_1114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1111_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1114_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = l_Lean_indentExpr(v_givenType_1105_);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
lean_ctor_set(v___x_1121_, 1, v___x_1108_);
v___x_1122_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = l_Lean_indentExpr(v_expectedType_1106_);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = l_Lean_throwError___redArg(v_inst_1101_, v_inst_1102_, v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1127_, lean_object* v_inst_1128_, lean_object* v_inst_1129_, lean_object* v_00_u03b1_1130_, lean_object* v_attrName_1131_, lean_object* v_declName_1132_, lean_object* v_givenType_1133_, lean_object* v_expectedType_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1128_, v_inst_1129_, v_attrName_1131_, v_declName_1132_, v_givenType_1133_, v_expectedType_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1136_, uint8_t v_skipRealize_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; lean_object* v_env_1141_; uint8_t v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1140_ = lean_st_ref_get(v___y_1138_);
v_env_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc_ref(v_env_1141_);
lean_dec(v___x_1140_);
v___x_1142_ = l_Lean_Environment_contains(v_env_1141_, v_constName_1136_, v_skipRealize_1137_);
v___x_1143_ = lean_box(v___x_1142_);
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object* v_constName_1145_, lean_object* v_skipRealize_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
uint8_t v_skipRealize_boxed_1149_; lean_object* v_res_1150_; 
v_skipRealize_boxed_1149_ = lean_unbox(v_skipRealize_1146_);
v_res_1150_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1145_, v_skipRealize_boxed_1149_, v___y_1147_);
lean_dec(v___y_1147_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1151_, uint8_t v_skipRealize_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1151_, v_skipRealize_1152_, v___y_1154_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1157_, lean_object* v_skipRealize_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
uint8_t v_skipRealize_boxed_1162_; lean_object* v_res_1163_; 
v_skipRealize_boxed_1162_ = lean_unbox(v_skipRealize_1158_);
v_res_1163_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1157_, v_skipRealize_boxed_1162_, v___y_1159_, v___y_1160_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1164_, uint8_t v_isExporting_1165_, lean_object* v___x_1166_, lean_object* v_a_x3f_1167_){
_start:
{
lean_object* v___x_1169_; lean_object* v_env_1170_; lean_object* v_nextMacroScope_1171_; lean_object* v_ngen_1172_; lean_object* v_auxDeclNGen_1173_; lean_object* v_traceState_1174_; lean_object* v_recordedDeps_1175_; lean_object* v_messages_1176_; lean_object* v_infoState_1177_; lean_object* v_snapshotTasks_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1189_; 
v___x_1169_ = lean_st_ref_take(v___y_1164_);
v_env_1170_ = lean_ctor_get(v___x_1169_, 0);
v_nextMacroScope_1171_ = lean_ctor_get(v___x_1169_, 1);
v_ngen_1172_ = lean_ctor_get(v___x_1169_, 2);
v_auxDeclNGen_1173_ = lean_ctor_get(v___x_1169_, 3);
v_traceState_1174_ = lean_ctor_get(v___x_1169_, 4);
v_recordedDeps_1175_ = lean_ctor_get(v___x_1169_, 6);
v_messages_1176_ = lean_ctor_get(v___x_1169_, 7);
v_infoState_1177_ = lean_ctor_get(v___x_1169_, 8);
v_snapshotTasks_1178_ = lean_ctor_get(v___x_1169_, 9);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1189_ == 0)
{
lean_object* v_unused_1190_; 
v_unused_1190_ = lean_ctor_get(v___x_1169_, 5);
lean_dec(v_unused_1190_);
v___x_1180_ = v___x_1169_;
v_isShared_1181_ = v_isSharedCheck_1189_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_snapshotTasks_1178_);
lean_inc(v_infoState_1177_);
lean_inc(v_messages_1176_);
lean_inc(v_recordedDeps_1175_);
lean_inc(v_traceState_1174_);
lean_inc(v_auxDeclNGen_1173_);
lean_inc(v_ngen_1172_);
lean_inc(v_nextMacroScope_1171_);
lean_inc(v_env_1170_);
lean_dec(v___x_1169_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1189_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1182_ = lean_box(0);
v___x_1183_ = l_Lean_Environment_setExporting(v_env_1170_, v_isExporting_1165_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 5, v___x_1166_);
lean_ctor_set(v___x_1180_, 0, v___x_1183_);
v___x_1185_ = v___x_1180_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_nextMacroScope_1171_);
lean_ctor_set(v_reuseFailAlloc_1188_, 2, v_ngen_1172_);
lean_ctor_set(v_reuseFailAlloc_1188_, 3, v_auxDeclNGen_1173_);
lean_ctor_set(v_reuseFailAlloc_1188_, 4, v_traceState_1174_);
lean_ctor_set(v_reuseFailAlloc_1188_, 5, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1188_, 6, v_recordedDeps_1175_);
lean_ctor_set(v_reuseFailAlloc_1188_, 7, v_messages_1176_);
lean_ctor_set(v_reuseFailAlloc_1188_, 8, v_infoState_1177_);
lean_ctor_set(v_reuseFailAlloc_1188_, 9, v_snapshotTasks_1178_);
v___x_1185_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_st_ref_put(v___y_1164_, v___x_1185_);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1182_);
return v___x_1187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1191_, lean_object* v_isExporting_1192_, lean_object* v___x_1193_, lean_object* v_a_x3f_1194_, lean_object* v___y_1195_){
_start:
{
uint8_t v_isExporting_boxed_1196_; lean_object* v_res_1197_; 
v_isExporting_boxed_1196_ = lean_unbox(v_isExporting_1192_);
v_res_1197_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1191_, v_isExporting_boxed_1196_, v___x_1193_, v_a_x3f_1194_);
lean_dec(v_a_x3f_1194_);
lean_dec(v___y_1191_);
return v_res_1197_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0);
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
return v___x_1199_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1202_, uint8_t v_isExporting_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; lean_object* v_env_1208_; lean_object* v___x_1209_; uint8_t v_isModule_1210_; 
v___x_1207_ = lean_st_ref_get(v___y_1205_);
v_env_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc_ref(v_env_1208_);
lean_dec(v___x_1207_);
v___x_1209_ = l_Lean_Environment_header(v_env_1208_);
v_isModule_1210_ = lean_ctor_get_uint8(v___x_1209_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1209_);
if (v_isModule_1210_ == 0)
{
lean_object* v___x_1211_; 
lean_dec_ref(v_env_1208_);
lean_inc(v___y_1205_);
lean_inc_ref(v___y_1204_);
v___x_1211_ = lean_apply_3(v_x_1202_, v___y_1204_, v___y_1205_, lean_box(0));
return v___x_1211_;
}
else
{
uint8_t v_isExporting_1212_; 
v_isExporting_1212_ = lean_ctor_get_uint8(v_env_1208_, sizeof(void*)*13);
lean_dec_ref(v_env_1208_);
if (v_isExporting_1203_ == 0)
{
if (v_isExporting_1212_ == 0)
{
lean_object* v___x_1264_; 
lean_inc(v___y_1205_);
lean_inc_ref(v___y_1204_);
v___x_1264_ = lean_apply_3(v_x_1202_, v___y_1204_, v___y_1205_, lean_box(0));
return v___x_1264_;
}
else
{
goto v___jp_1213_;
}
}
else
{
if (v_isExporting_1212_ == 0)
{
goto v___jp_1213_;
}
else
{
lean_object* v___x_1265_; 
lean_inc(v___y_1205_);
lean_inc_ref(v___y_1204_);
v___x_1265_ = lean_apply_3(v_x_1202_, v___y_1204_, v___y_1205_, lean_box(0));
return v___x_1265_;
}
}
v___jp_1213_:
{
lean_object* v___x_1214_; lean_object* v_env_1215_; lean_object* v_nextMacroScope_1216_; lean_object* v_ngen_1217_; lean_object* v_auxDeclNGen_1218_; lean_object* v_traceState_1219_; lean_object* v_recordedDeps_1220_; lean_object* v_messages_1221_; lean_object* v_infoState_1222_; lean_object* v_snapshotTasks_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1262_; 
v___x_1214_ = lean_st_ref_take(v___y_1205_);
v_env_1215_ = lean_ctor_get(v___x_1214_, 0);
v_nextMacroScope_1216_ = lean_ctor_get(v___x_1214_, 1);
v_ngen_1217_ = lean_ctor_get(v___x_1214_, 2);
v_auxDeclNGen_1218_ = lean_ctor_get(v___x_1214_, 3);
v_traceState_1219_ = lean_ctor_get(v___x_1214_, 4);
v_recordedDeps_1220_ = lean_ctor_get(v___x_1214_, 6);
v_messages_1221_ = lean_ctor_get(v___x_1214_, 7);
v_infoState_1222_ = lean_ctor_get(v___x_1214_, 8);
v_snapshotTasks_1223_ = lean_ctor_get(v___x_1214_, 9);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; 
v_unused_1263_ = lean_ctor_get(v___x_1214_, 5);
lean_dec(v_unused_1263_);
v___x_1225_ = v___x_1214_;
v_isShared_1226_ = v_isSharedCheck_1262_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_snapshotTasks_1223_);
lean_inc(v_infoState_1222_);
lean_inc(v_messages_1221_);
lean_inc(v_recordedDeps_1220_);
lean_inc(v_traceState_1219_);
lean_inc(v_auxDeclNGen_1218_);
lean_inc(v_ngen_1217_);
lean_inc(v_nextMacroScope_1216_);
lean_inc(v_env_1215_);
lean_dec(v___x_1214_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1262_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1227_ = l_Lean_Environment_setExporting(v_env_1215_, v_isExporting_1203_);
v___x_1228_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 5, v___x_1228_);
lean_ctor_set(v___x_1225_, 0, v___x_1227_);
v___x_1230_ = v___x_1225_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_nextMacroScope_1216_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_ngen_1217_);
lean_ctor_set(v_reuseFailAlloc_1261_, 3, v_auxDeclNGen_1218_);
lean_ctor_set(v_reuseFailAlloc_1261_, 4, v_traceState_1219_);
lean_ctor_set(v_reuseFailAlloc_1261_, 5, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1261_, 6, v_recordedDeps_1220_);
lean_ctor_set(v_reuseFailAlloc_1261_, 7, v_messages_1221_);
lean_ctor_set(v_reuseFailAlloc_1261_, 8, v_infoState_1222_);
lean_ctor_set(v_reuseFailAlloc_1261_, 9, v_snapshotTasks_1223_);
v___x_1230_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1231_; lean_object* v_r_1232_; 
v___x_1231_ = lean_st_ref_put(v___y_1205_, v___x_1230_);
lean_inc(v___y_1205_);
lean_inc_ref(v___y_1204_);
v_r_1232_ = lean_apply_3(v_x_1202_, v___y_1204_, v___y_1205_, lean_box(0));
if (lean_obj_tag(v_r_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1249_; 
v_a_1233_ = lean_ctor_get(v_r_1232_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_r_1232_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1235_ = v_r_1232_;
v_isShared_1236_ = v_isSharedCheck_1249_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v_r_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1249_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
lean_inc(v_a_1233_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set_tag(v___x_1235_, 1);
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
v___x_1239_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1205_, v_isExporting_1212_, v___x_1228_, v___x_1238_);
lean_dec_ref(v___x_1238_);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v___x_1239_, 0);
lean_dec(v_unused_1247_);
v___x_1241_ = v___x_1239_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_dec(v___x_1239_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v_a_1233_);
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1233_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
v_a_1250_ = lean_ctor_get(v_r_1232_, 0);
lean_inc(v_a_1250_);
lean_dec_ref_known(v_r_1232_, 1);
v___x_1251_ = lean_box(0);
v___x_1252_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1205_, v_isExporting_1212_, v___x_1228_, v___x_1251_);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; 
v_unused_1260_ = lean_ctor_get(v___x_1252_, 0);
lean_dec(v_unused_1260_);
v___x_1254_ = v___x_1252_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_dec(v___x_1252_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set_tag(v___x_1254_, 1);
lean_ctor_set(v___x_1254_, 0, v_a_1250_);
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1250_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1266_, lean_object* v_isExporting_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
uint8_t v_isExporting_boxed_1271_; lean_object* v_res_1272_; 
v_isExporting_boxed_1271_ = lean_unbox(v_isExporting_1267_);
v_res_1272_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1266_, v_isExporting_boxed_1271_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1273_, lean_object* v_x_1274_, uint8_t v_isExporting_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1274_, v_isExporting_1275_, v___y_1276_, v___y_1277_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1280_, lean_object* v_x_1281_, lean_object* v_isExporting_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
uint8_t v_isExporting_boxed_1286_; lean_object* v_res_1287_; 
v_isExporting_boxed_1286_ = lean_unbox(v_isExporting_1282_);
v_res_1287_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1280_, v_x_1281_, v_isExporting_boxed_1286_, v___y_1283_, v___y_1284_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
return v_res_1287_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1288_, lean_object* v_opt_1289_){
_start:
{
lean_object* v_name_1290_; lean_object* v_defValue_1291_; lean_object* v_map_1292_; lean_object* v___x_1293_; 
v_name_1290_ = lean_ctor_get(v_opt_1289_, 0);
v_defValue_1291_ = lean_ctor_get(v_opt_1289_, 1);
v_map_1292_ = lean_ctor_get(v_opts_1288_, 0);
v___x_1293_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1292_, v_name_1290_);
if (lean_obj_tag(v___x_1293_) == 0)
{
uint8_t v___x_1294_; 
v___x_1294_ = lean_unbox(v_defValue_1291_);
return v___x_1294_;
}
else
{
lean_object* v_val_1295_; 
v_val_1295_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_val_1295_);
lean_dec_ref_known(v___x_1293_, 1);
if (lean_obj_tag(v_val_1295_) == 1)
{
uint8_t v_v_1296_; 
v_v_1296_ = lean_ctor_get_uint8(v_val_1295_, 0);
lean_dec_ref_known(v_val_1295_, 0);
return v_v_1296_;
}
else
{
uint8_t v___x_1297_; 
lean_dec(v_val_1295_);
v___x_1297_ = lean_unbox(v_defValue_1291_);
return v___x_1297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1298_, lean_object* v_opt_1299_){
_start:
{
uint8_t v_res_1300_; lean_object* v_r_1301_; 
v_res_1300_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1298_, v_opt_1299_);
lean_dec_ref(v_opt_1299_);
lean_dec_ref(v_opts_1298_);
v_r_1301_ = lean_box(v_res_1300_);
return v_r_1301_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_1309_, lean_object* v_x_1310_){
_start:
{
if (lean_obj_tag(v_x_1310_) == 1)
{
lean_object* v_pre_1311_; 
v_pre_1311_ = lean_ctor_get(v_x_1310_, 0);
switch(lean_obj_tag(v_pre_1311_))
{
case 1:
{
lean_object* v_pre_1312_; 
v_pre_1312_ = lean_ctor_get(v_pre_1311_, 0);
switch(lean_obj_tag(v_pre_1312_))
{
case 0:
{
lean_object* v_str_1313_; lean_object* v_str_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v_str_1313_ = lean_ctor_get(v_x_1310_, 1);
v_str_1314_ = lean_ctor_get(v_pre_1311_, 1);
v___x_1315_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1316_ = lean_string_dec_eq(v_str_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1318_ = lean_string_dec_eq(v_str_1314_, v___x_1317_);
if (v___x_1318_ == 0)
{
return v___x_1318_;
}
else
{
lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1320_ = lean_string_dec_eq(v_str_1313_, v___x_1319_);
if (v___x_1320_ == 0)
{
return v___x_1320_;
}
else
{
return v_suppressElabErrors_1309_;
}
}
}
else
{
lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1321_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1322_ = lean_string_dec_eq(v_str_1313_, v___x_1321_);
if (v___x_1322_ == 0)
{
return v___x_1322_;
}
else
{
return v_suppressElabErrors_1309_;
}
}
}
case 1:
{
lean_object* v_pre_1323_; 
v_pre_1323_ = lean_ctor_get(v_pre_1312_, 0);
if (lean_obj_tag(v_pre_1323_) == 0)
{
lean_object* v_str_1324_; lean_object* v_str_1325_; lean_object* v_str_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v_str_1324_ = lean_ctor_get(v_x_1310_, 1);
v_str_1325_ = lean_ctor_get(v_pre_1311_, 1);
v_str_1326_ = lean_ctor_get(v_pre_1312_, 1);
v___x_1327_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1328_ = lean_string_dec_eq(v_str_1326_, v___x_1327_);
if (v___x_1328_ == 0)
{
return v___x_1328_;
}
else
{
lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1330_ = lean_string_dec_eq(v_str_1325_, v___x_1329_);
if (v___x_1330_ == 0)
{
return v___x_1330_;
}
else
{
lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1331_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1332_ = lean_string_dec_eq(v_str_1324_, v___x_1331_);
if (v___x_1332_ == 0)
{
return v___x_1332_;
}
else
{
return v_suppressElabErrors_1309_;
}
}
}
}
else
{
uint8_t v___x_1333_; 
v___x_1333_ = 0;
return v___x_1333_;
}
}
default: 
{
uint8_t v___x_1334_; 
v___x_1334_ = 0;
return v___x_1334_;
}
}
}
case 0:
{
lean_object* v_str_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v_str_1335_ = lean_ctor_get(v_x_1310_, 1);
v___x_1336_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1337_ = lean_string_dec_eq(v_str_1335_, v___x_1336_);
if (v___x_1337_ == 0)
{
return v___x_1337_;
}
else
{
return v_suppressElabErrors_1309_;
}
}
default: 
{
uint8_t v___x_1338_; 
v___x_1338_ = 0;
return v___x_1338_;
}
}
}
else
{
uint8_t v___x_1339_; 
v___x_1339_ = 0;
return v___x_1339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_1340_, lean_object* v_x_1341_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1342_; uint8_t v_res_1343_; lean_object* v_r_1344_; 
v_suppressElabErrors_boxed_1342_ = lean_unbox(v_suppressElabErrors_1340_);
v_res_1343_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_1342_, v_x_1341_);
lean_dec(v_x_1341_);
v_r_1344_ = lean_box(v_res_1343_);
return v_r_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1345_, lean_object* v_msgData_1346_, uint8_t v_severity_1347_, uint8_t v_isSilent_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___y_1353_; uint8_t v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; uint8_t v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v_toCold_1360_; lean_object* v___y_1361_; lean_object* v___y_1390_; lean_object* v___y_1391_; uint8_t v___y_1392_; lean_object* v___y_1393_; uint8_t v___y_1394_; uint8_t v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1417_; lean_object* v___y_1418_; uint8_t v___y_1419_; uint8_t v___y_1420_; uint8_t v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; uint8_t v___y_1427_; uint8_t v___y_1428_; uint8_t v___x_1438_; uint8_t v___y_1440_; uint8_t v___x_1446_; 
v___x_1438_ = 2;
v___x_1446_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1347_, v___x_1438_);
if (v___x_1446_ == 0)
{
v___y_1440_ = v___x_1446_;
goto v___jp_1439_;
}
else
{
uint8_t v___x_1447_; 
lean_inc_ref(v_msgData_1346_);
v___x_1447_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1346_);
if (v___x_1447_ == 0)
{
v___y_1440_ = v___x_1447_;
goto v___jp_1439_;
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_dec_ref(v_msgData_1346_);
v___x_1448_ = lean_box(0);
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
return v___x_1449_;
}
}
v___jp_1352_:
{
lean_object* v_currNamespace_1362_; lean_object* v_openDecls_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v_env_1368_; lean_object* v_nextMacroScope_1369_; lean_object* v_ngen_1370_; lean_object* v_auxDeclNGen_1371_; lean_object* v_traceState_1372_; lean_object* v_cache_1373_; lean_object* v_recordedDeps_1374_; lean_object* v_messages_1375_; lean_object* v_infoState_1376_; lean_object* v_snapshotTasks_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1388_; 
v_currNamespace_1362_ = lean_ctor_get(v_toCold_1360_, 4);
v_openDecls_1363_ = lean_ctor_get(v_toCold_1360_, 5);
lean_inc(v_openDecls_1363_);
lean_inc(v_currNamespace_1362_);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v_currNamespace_1362_);
lean_ctor_set(v___x_1364_, 1, v_openDecls_1363_);
v___x_1365_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
lean_ctor_set(v___x_1365_, 1, v___y_1356_);
lean_inc_ref(v___y_1353_);
lean_inc_ref(v___y_1355_);
v___x_1366_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1366_, 0, v___y_1355_);
lean_ctor_set(v___x_1366_, 1, v___y_1359_);
lean_ctor_set(v___x_1366_, 2, v___y_1358_);
lean_ctor_set(v___x_1366_, 3, v___y_1353_);
lean_ctor_set(v___x_1366_, 4, v___x_1365_);
lean_ctor_set_uint8(v___x_1366_, sizeof(void*)*5, v___y_1354_);
lean_ctor_set_uint8(v___x_1366_, sizeof(void*)*5 + 1, v___y_1357_);
lean_ctor_set_uint8(v___x_1366_, sizeof(void*)*5 + 2, v_isSilent_1348_);
v___x_1367_ = lean_st_ref_take(v___y_1361_);
v_env_1368_ = lean_ctor_get(v___x_1367_, 0);
v_nextMacroScope_1369_ = lean_ctor_get(v___x_1367_, 1);
v_ngen_1370_ = lean_ctor_get(v___x_1367_, 2);
v_auxDeclNGen_1371_ = lean_ctor_get(v___x_1367_, 3);
v_traceState_1372_ = lean_ctor_get(v___x_1367_, 4);
v_cache_1373_ = lean_ctor_get(v___x_1367_, 5);
v_recordedDeps_1374_ = lean_ctor_get(v___x_1367_, 6);
v_messages_1375_ = lean_ctor_get(v___x_1367_, 7);
v_infoState_1376_ = lean_ctor_get(v___x_1367_, 8);
v_snapshotTasks_1377_ = lean_ctor_get(v___x_1367_, 9);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1379_ = v___x_1367_;
v_isShared_1380_ = v_isSharedCheck_1388_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_snapshotTasks_1377_);
lean_inc(v_infoState_1376_);
lean_inc(v_messages_1375_);
lean_inc(v_recordedDeps_1374_);
lean_inc(v_cache_1373_);
lean_inc(v_traceState_1372_);
lean_inc(v_auxDeclNGen_1371_);
lean_inc(v_ngen_1370_);
lean_inc(v_nextMacroScope_1369_);
lean_inc(v_env_1368_);
lean_dec(v___x_1367_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1388_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1381_ = lean_box(0);
v___x_1382_ = l_Lean_MessageLog_add(v___x_1366_, v_messages_1375_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 7, v___x_1382_);
v___x_1384_ = v___x_1379_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_env_1368_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_nextMacroScope_1369_);
lean_ctor_set(v_reuseFailAlloc_1387_, 2, v_ngen_1370_);
lean_ctor_set(v_reuseFailAlloc_1387_, 3, v_auxDeclNGen_1371_);
lean_ctor_set(v_reuseFailAlloc_1387_, 4, v_traceState_1372_);
lean_ctor_set(v_reuseFailAlloc_1387_, 5, v_cache_1373_);
lean_ctor_set(v_reuseFailAlloc_1387_, 6, v_recordedDeps_1374_);
lean_ctor_set(v_reuseFailAlloc_1387_, 7, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1387_, 8, v_infoState_1376_);
lean_ctor_set(v_reuseFailAlloc_1387_, 9, v_snapshotTasks_1377_);
v___x_1384_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_st_ref_put(v___y_1361_, v___x_1384_);
v___x_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1381_);
return v___x_1386_;
}
}
}
v___jp_1389_:
{
lean_object* v_fileName_1398_; lean_object* v_fileMap_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1415_; 
v_fileName_1398_ = lean_ctor_get(v___y_1396_, 0);
v_fileMap_1399_ = lean_ctor_get(v___y_1396_, 1);
v___x_1400_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1346_);
v___x_1401_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v___x_1400_, v___y_1349_, v___y_1350_);
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1415_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1415_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
lean_inc_ref_n(v_fileMap_1399_, 2);
v___x_1406_ = l_Lean_FileMap_toPosition(v_fileMap_1399_, v___y_1393_);
lean_dec(v___y_1393_);
v___x_1407_ = l_Lean_FileMap_toPosition(v_fileMap_1399_, v___y_1397_);
lean_dec(v___y_1397_);
v___x_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
v___x_1409_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1395_ == 0)
{
lean_del_object(v___x_1404_);
lean_dec_ref(v___y_1390_);
v___y_1353_ = v___x_1409_;
v___y_1354_ = v___y_1392_;
v___y_1355_ = v_fileName_1398_;
v___y_1356_ = v_a_1402_;
v___y_1357_ = v___y_1394_;
v___y_1358_ = v___x_1408_;
v___y_1359_ = v___x_1406_;
v_toCold_1360_ = v___y_1391_;
v___y_1361_ = v___y_1350_;
goto v___jp_1352_;
}
else
{
uint8_t v___x_1410_; 
lean_inc(v_a_1402_);
v___x_1410_ = l_Lean_MessageData_hasTag(v___y_1390_, v_a_1402_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
lean_dec_ref_known(v___x_1408_, 1);
lean_dec_ref(v___x_1406_);
lean_dec(v_a_1402_);
v___x_1411_ = lean_box(0);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1411_);
v___x_1413_ = v___x_1404_;
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
else
{
lean_del_object(v___x_1404_);
v___y_1353_ = v___x_1409_;
v___y_1354_ = v___y_1392_;
v___y_1355_ = v_fileName_1398_;
v___y_1356_ = v_a_1402_;
v___y_1357_ = v___y_1394_;
v___y_1358_ = v___x_1408_;
v___y_1359_ = v___x_1406_;
v_toCold_1360_ = v___y_1391_;
v___y_1361_ = v___y_1350_;
goto v___jp_1352_;
}
}
}
}
v___jp_1416_:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_Syntax_getTailPos_x3f(v___y_1422_, v___y_1420_);
lean_dec(v___y_1422_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_inc(v___y_1423_);
v___y_1390_ = v___y_1417_;
v___y_1391_ = v___y_1418_;
v___y_1392_ = v___y_1420_;
v___y_1393_ = v___y_1423_;
v___y_1394_ = v___y_1421_;
v___y_1395_ = v___y_1419_;
v___y_1396_ = v___y_1418_;
v___y_1397_ = v___y_1423_;
goto v___jp_1389_;
}
else
{
lean_object* v_val_1425_; 
v_val_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_val_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v___y_1390_ = v___y_1417_;
v___y_1391_ = v___y_1418_;
v___y_1392_ = v___y_1420_;
v___y_1393_ = v___y_1423_;
v___y_1394_ = v___y_1421_;
v___y_1395_ = v___y_1419_;
v___y_1396_ = v___y_1418_;
v___y_1397_ = v_val_1425_;
goto v___jp_1389_;
}
}
v___jp_1426_:
{
lean_object* v_toCold_1429_; lean_object* v_ref_1430_; uint8_t v_suppressElabErrors_1431_; lean_object* v___x_1432_; lean_object* v___f_1433_; lean_object* v_ref_1434_; lean_object* v___x_1435_; 
v_toCold_1429_ = lean_ctor_get(v___y_1349_, 0);
v_ref_1430_ = lean_ctor_get(v___y_1349_, 2);
v_suppressElabErrors_1431_ = lean_ctor_get_uint8(v___y_1349_, sizeof(void*)*3 + 2);
v___x_1432_ = lean_box(v_suppressElabErrors_1431_);
v___f_1433_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1433_, 0, v___x_1432_);
v_ref_1434_ = l_Lean_replaceRef(v_ref_1345_, v_ref_1430_);
v___x_1435_ = l_Lean_Syntax_getPos_x3f(v_ref_1434_, v___y_1427_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_unsigned_to_nat(0u);
v___y_1417_ = v___f_1433_;
v___y_1418_ = v_toCold_1429_;
v___y_1419_ = v_suppressElabErrors_1431_;
v___y_1420_ = v___y_1427_;
v___y_1421_ = v___y_1428_;
v___y_1422_ = v_ref_1434_;
v___y_1423_ = v___x_1436_;
goto v___jp_1416_;
}
else
{
lean_object* v_val_1437_; 
v_val_1437_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_val_1437_);
lean_dec_ref_known(v___x_1435_, 1);
v___y_1417_ = v___f_1433_;
v___y_1418_ = v_toCold_1429_;
v___y_1419_ = v_suppressElabErrors_1431_;
v___y_1420_ = v___y_1427_;
v___y_1421_ = v___y_1428_;
v___y_1422_ = v_ref_1434_;
v___y_1423_ = v_val_1437_;
goto v___jp_1416_;
}
}
v___jp_1439_:
{
uint8_t v___x_1441_; uint8_t v___x_1442_; 
v___x_1441_ = 1;
v___x_1442_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1347_, v___x_1441_);
if (v___x_1442_ == 0)
{
v___y_1427_ = v___y_1440_;
v___y_1428_ = v_severity_1347_;
goto v___jp_1426_;
}
else
{
lean_object* v___x_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1443_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1349_);
v___x_1444_ = l_Lean_warningAsError;
v___x_1445_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v___x_1443_, v___x_1444_);
lean_dec_ref(v___x_1443_);
if (v___x_1445_ == 0)
{
v___y_1427_ = v___y_1440_;
v___y_1428_ = v_severity_1347_;
goto v___jp_1426_;
}
else
{
v___y_1427_ = v___y_1440_;
v___y_1428_ = v___x_1438_;
goto v___jp_1426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1450_, lean_object* v_msgData_1451_, lean_object* v_severity_1452_, lean_object* v_isSilent_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
uint8_t v_severity_boxed_1457_; uint8_t v_isSilent_boxed_1458_; lean_object* v_res_1459_; 
v_severity_boxed_1457_ = lean_unbox(v_severity_1452_);
v_isSilent_boxed_1458_ = lean_unbox(v_isSilent_1453_);
v_res_1459_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1450_, v_msgData_1451_, v_severity_boxed_1457_, v_isSilent_boxed_1458_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v_ref_1450_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1460_, uint8_t v_severity_1461_, uint8_t v_isSilent_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_ref_1466_; lean_object* v___x_1467_; 
v_ref_1466_ = lean_ctor_get(v___y_1463_, 2);
v___x_1467_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1466_, v_msgData_1460_, v_severity_1461_, v_isSilent_1462_, v___y_1463_, v___y_1464_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1468_, lean_object* v_severity_1469_, lean_object* v_isSilent_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
uint8_t v_severity_boxed_1474_; uint8_t v_isSilent_boxed_1475_; lean_object* v_res_1476_; 
v_severity_boxed_1474_ = lean_unbox(v_severity_1469_);
v_isSilent_boxed_1475_ = lean_unbox(v_isSilent_1470_);
v_res_1476_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1468_, v_severity_boxed_1474_, v_isSilent_boxed_1475_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
uint8_t v___x_1481_; uint8_t v___x_1482_; lean_object* v___x_1483_; 
v___x_1481_ = 1;
v___x_1482_ = 0;
v___x_1483_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1477_, v___x_1481_, v___x_1482_, v___y_1478_, v___y_1479_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1484_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v___x_1492_; uint8_t v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1492_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1490_);
v___x_1493_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v___x_1492_, v_opt_1489_);
lean_dec_ref(v___x_1492_);
v___x_1494_ = lean_box(v___x_1493_);
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1496_, v___y_1497_);
lean_dec_ref(v___y_1497_);
lean_dec_ref(v_opt_1496_);
return v_res_1499_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1502_ = l_Lean_stringToMessageData(v___x_1501_);
return v___x_1502_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1505_ = l_Lean_stringToMessageData(v___x_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; lean_object* v_env_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1533_; 
v___x_1510_ = lean_st_ref_get(v___y_1508_);
v_env_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc_ref(v_env_1511_);
lean_dec(v___x_1510_);
v___x_1512_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1513_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1512_, v___y_1507_);
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1533_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1533_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
uint8_t v_isExporting_1523_; 
v_isExporting_1523_ = lean_ctor_get_uint8(v_env_1511_, sizeof(void*)*13);
lean_dec_ref(v_env_1511_);
if (v_isExporting_1523_ == 0)
{
lean_dec(v_a_1514_);
lean_dec(v_id_1506_);
goto v___jp_1518_;
}
else
{
uint8_t v___x_1524_; 
v___x_1524_ = l_Lean_isPrivateName(v_id_1506_);
if (v___x_1524_ == 0)
{
lean_dec(v_a_1514_);
lean_dec(v_id_1506_);
goto v___jp_1518_;
}
else
{
uint8_t v___x_1525_; 
v___x_1525_ = lean_unbox(v_a_1514_);
lean_dec(v_a_1514_);
if (v___x_1525_ == 0)
{
lean_dec(v_id_1506_);
goto v___jp_1518_;
}
else
{
lean_object* v___x_1526_; uint8_t v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_del_object(v___x_1516_);
v___x_1526_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1527_ = 0;
v___x_1528_ = l_Lean_MessageData_ofConstName(v_id_1506_, v___x_1527_);
v___x_1529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1526_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1531_, v___y_1507_, v___y_1508_);
return v___x_1532_;
}
}
}
v___jp_1518_:
{
lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1519_ = lean_box(0);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1519_);
v___x_1521_ = v___x_1516_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
return v_res_1538_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1541_ = l_Lean_stringToMessageData(v___x_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1542_, uint8_t v_isModule_1543_, lean_object* v_attrName_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v___x_1548_; 
lean_inc(v_declName_1542_);
v___x_1548_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1542_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v___x_1549_; lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1570_; 
lean_dec_ref_known(v___x_1548_, 1);
lean_inc(v_declName_1542_);
v___x_1549_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1542_, v_isModule_1543_, v___y_1546_);
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1570_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1570_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
uint8_t v___x_1554_; 
v___x_1554_ = lean_unbox(v_a_1550_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
lean_del_object(v___x_1552_);
v___x_1555_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1556_ = l_Lean_MessageData_ofName(v_attrName_1544_);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = lean_unbox(v_a_1550_);
lean_dec(v_a_1550_);
v___x_1561_ = l_Lean_MessageData_ofConstName(v_declName_1542_, v___x_1560_);
v___x_1562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1559_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1564_, v___y_1545_, v___y_1546_);
return v___x_1565_;
}
else
{
lean_object* v___x_1566_; lean_object* v___x_1568_; 
lean_dec(v_a_1550_);
lean_dec(v_attrName_1544_);
lean_dec(v_declName_1542_);
v___x_1566_ = lean_box(0);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1566_);
v___x_1568_ = v___x_1552_;
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
lean_dec(v_attrName_1544_);
lean_dec(v_declName_1542_);
return v___x_1548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1571_, lean_object* v_isModule_1572_, lean_object* v_attrName_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
uint8_t v_isModule_boxed_1577_; lean_object* v_res_1578_; 
v_isModule_boxed_1577_ = lean_unbox(v_isModule_1572_);
v_res_1578_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1571_, v_isModule_boxed_1577_, v_attrName_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1579_, lean_object* v_declName_1580_, uint8_t v_attrKind_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v___x_1585_; lean_object* v_env_1589_; lean_object* v___x_1590_; uint8_t v_isModule_1591_; 
v___x_1585_ = lean_st_ref_get(v_a_1583_);
v_env_1589_ = lean_ctor_get(v___x_1585_, 0);
lean_inc_ref(v_env_1589_);
lean_dec(v___x_1585_);
v___x_1590_ = l_Lean_Environment_header(v_env_1589_);
lean_dec_ref(v_env_1589_);
v_isModule_1591_ = lean_ctor_get_uint8(v___x_1590_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1590_);
if (v_isModule_1591_ == 0)
{
lean_dec(v_declName_1580_);
lean_dec(v_attrName_1579_);
goto v___jp_1586_;
}
else
{
uint8_t v___x_1592_; uint8_t v___x_1593_; 
v___x_1592_ = 1;
v___x_1593_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1581_, v___x_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; lean_object* v___f_1595_; lean_object* v___x_1596_; 
v___x_1594_ = lean_box(v_isModule_1591_);
v___f_1595_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1595_, 0, v_declName_1580_);
lean_closure_set(v___f_1595_, 1, v___x_1594_);
lean_closure_set(v___f_1595_, 2, v_attrName_1579_);
v___x_1596_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1595_, v_isModule_1591_, v_a_1582_, v_a_1583_);
return v___x_1596_;
}
else
{
lean_dec(v_declName_1580_);
lean_dec(v_attrName_1579_);
goto v___jp_1586_;
}
}
v___jp_1586_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = lean_box(0);
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
return v___x_1588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1597_, lean_object* v_declName_1598_, lean_object* v_attrKind_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
uint8_t v_attrKind_boxed_1603_; lean_object* v_res_1604_; 
v_attrKind_boxed_1603_ = lean_unbox(v_attrKind_1599_);
v_res_1604_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1597_, v_declName_1598_, v_attrKind_boxed_1603_, v_a_1600_, v_a_1601_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1605_, v___y_1606_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1610_, v___y_1611_, v___y_1612_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec_ref(v_opt_1610_);
return v_res_1614_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1617_ = l_Lean_stringToMessageData(v___x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1618_, lean_object* v_declName_1619_, uint8_t v_attrKind_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v___x_1624_; lean_object* v_env_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; uint8_t v_isModule_1628_; 
v___x_1624_ = lean_st_ref_get(v_a_1622_);
v_env_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc_ref(v_env_1625_);
lean_dec(v___x_1624_);
v___x_1626_ = lean_st_ref_get(v_a_1622_);
v___x_1627_ = l_Lean_Environment_header(v_env_1625_);
lean_dec_ref(v_env_1625_);
v_isModule_1628_ = lean_ctor_get_uint8(v___x_1627_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1627_);
if (v_isModule_1628_ == 0)
{
lean_object* v___x_1629_; 
lean_dec(v___x_1626_);
v___x_1629_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1618_, v_declName_1619_, v_attrKind_1620_, v_a_1621_, v_a_1622_);
return v___x_1629_;
}
else
{
lean_object* v_env_1630_; uint8_t v___x_1631_; 
v_env_1630_ = lean_ctor_get(v___x_1626_, 0);
lean_inc_ref(v_env_1630_);
lean_dec(v___x_1626_);
lean_inc(v_declName_1619_);
v___x_1631_ = l_Lean_isMarkedMeta(v_env_1630_, v_declName_1619_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1632_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1633_ = l_Lean_MessageData_ofName(v_attrName_1618_);
v___x_1634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1632_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = l_Lean_MessageData_ofConstName(v_declName_1619_, v___x_1631_);
v___x_1638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1636_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1640_, v_a_1621_, v_a_1622_);
return v___x_1641_;
}
else
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1618_, v_declName_1619_, v_attrKind_1620_, v_a_1621_, v_a_1622_);
return v___x_1642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1643_, lean_object* v_declName_1644_, lean_object* v_attrKind_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
uint8_t v_attrKind_boxed_1649_; lean_object* v_res_1650_; 
v_attrKind_boxed_1649_ = lean_unbox(v_attrKind_1645_);
v_res_1650_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1643_, v_declName_1644_, v_attrKind_boxed_1649_, v_a_1646_, v_a_1647_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1659_, v___y_1660_);
lean_dec_ref(v___y_1660_);
lean_dec_ref(v_x_1659_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1663_, lean_object* v_x_1664_){
_start:
{
lean_inc(v_s_1663_);
return v_s_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1665_, lean_object* v_x_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1665_, v_x_1666_);
lean_dec(v_x_1666_);
lean_dec(v_s_1665_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1672_, lean_object* v_x_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1675_, lean_object* v_x_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1675_, v_x_1676_);
lean_dec(v_x_1676_);
lean_dec_ref(v_x_1675_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1678_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_box(0);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1680_);
lean_dec(v_x_1680_);
return v_res_1681_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_1686_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1687_; lean_object* v___f_1688_; lean_object* v___f_1689_; lean_object* v___f_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___f_1687_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1688_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1689_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1690_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1691_ = lean_box(0);
v___x_1692_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1693_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
lean_ctor_set(v___x_1693_, 1, v___x_1691_);
lean_ctor_set(v___x_1693_, 2, v___f_1690_);
lean_ctor_set(v___x_1693_, 3, v___f_1689_);
lean_ctor_set(v___x_1693_, 4, v___f_1688_);
lean_ctor_set(v___x_1693_, 5, v___f_1687_);
return v___x_1693_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1694_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1695_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
lean_ctor_set(v___x_1696_, 1, v___x_1694_);
return v___x_1696_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1697_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1698_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_registerTagAttribute___lam__0(v_x_1702_);
lean_dec(v_x_1702_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1704_, lean_object* v_x_1705_, lean_object* v_x_1706_){
_start:
{
if (lean_obj_tag(v_x_1706_) == 0)
{
return v_x_1705_;
}
else
{
lean_object* v_head_1707_; lean_object* v_tail_1708_; uint8_t v___x_1709_; 
v_head_1707_ = lean_ctor_get(v_x_1706_, 0);
lean_inc(v_head_1707_);
v_tail_1708_ = lean_ctor_get(v_x_1706_, 1);
lean_inc(v_tail_1708_);
lean_dec_ref_known(v_x_1706_, 2);
v___x_1709_ = l_Lean_NameSet_contains(v_newState_1704_, v_head_1707_);
if (v___x_1709_ == 0)
{
lean_dec(v_head_1707_);
v_x_1706_ = v_tail_1708_;
goto _start;
}
else
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_NameSet_insert(v_x_1705_, v_head_1707_);
v_x_1705_ = v___x_1711_;
v_x_1706_ = v_tail_1708_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1713_, lean_object* v_x_1714_, lean_object* v_x_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1713_, v_x_1714_, v_x_1715_);
lean_dec(v_newState_1713_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1717_, lean_object* v_newState_1718_, lean_object* v_newConsts_1719_, lean_object* v_s_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1718_, v_s_1720_, v_newConsts_1719_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1722_, lean_object* v_newState_1723_, lean_object* v_newConsts_1724_, lean_object* v_s_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_registerTagAttribute___lam__1(v_x_1722_, v_newState_1723_, v_newConsts_1724_, v_s_1725_);
lean_dec(v_newState_1723_);
lean_dec(v_x_1722_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1739_){
_start:
{
lean_object* v___x_1740_; lean_object* v___y_1742_; 
v___x_1740_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1739_) == 0)
{
lean_object* v_size_1746_; 
v_size_1746_ = lean_ctor_get(v_s_1739_, 0);
lean_inc(v_size_1746_);
lean_dec_ref_known(v_s_1739_, 5);
v___y_1742_ = v_size_1746_;
goto v___jp_1741_;
}
else
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_unsigned_to_nat(0u);
v___y_1742_ = v___x_1747_;
goto v___jp_1741_;
}
v___jp_1741_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1743_ = l_Nat_reprFast(v___y_1742_);
v___x_1744_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
v___x_1745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1740_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
return v___x_1745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1748_, lean_object* v_pivot_1749_, lean_object* v_as_1750_, lean_object* v_i_1751_, lean_object* v_k_1752_){
_start:
{
uint8_t v___x_1753_; 
v___x_1753_ = lean_nat_dec_lt(v_k_1752_, v_hi_1748_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_dec(v_k_1752_);
v___x_1754_ = lean_array_fswap(v_as_1750_, v_i_1751_, v_hi_1748_);
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v_i_1751_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
return v___x_1755_;
}
else
{
lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = lean_array_fget_borrowed(v_as_1750_, v_k_1752_);
v___x_1757_ = l_Lean_Name_quickLt(v___x_1756_, v_pivot_1749_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = lean_unsigned_to_nat(1u);
v___x_1759_ = lean_nat_add(v_k_1752_, v___x_1758_);
lean_dec(v_k_1752_);
v_k_1752_ = v___x_1759_;
goto _start;
}
else
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1761_ = lean_array_fswap(v_as_1750_, v_i_1751_, v_k_1752_);
v___x_1762_ = lean_unsigned_to_nat(1u);
v___x_1763_ = lean_nat_add(v_i_1751_, v___x_1762_);
lean_dec(v_i_1751_);
v___x_1764_ = lean_nat_add(v_k_1752_, v___x_1762_);
lean_dec(v_k_1752_);
v_as_1750_ = v___x_1761_;
v_i_1751_ = v___x_1763_;
v_k_1752_ = v___x_1764_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1766_, lean_object* v_pivot_1767_, lean_object* v_as_1768_, lean_object* v_i_1769_, lean_object* v_k_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1766_, v_pivot_1767_, v_as_1768_, v_i_1769_, v_k_1770_);
lean_dec(v_pivot_1767_);
lean_dec(v_hi_1766_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1772_, lean_object* v_as_1773_, lean_object* v_lo_1774_, lean_object* v_hi_1775_){
_start:
{
lean_object* v___y_1777_; uint8_t v___x_1787_; 
v___x_1787_ = lean_nat_dec_lt(v_lo_1774_, v_hi_1775_);
if (v___x_1787_ == 0)
{
lean_dec(v_lo_1774_);
return v_as_1773_;
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v_mid_1790_; lean_object* v___y_1792_; lean_object* v___y_1798_; lean_object* v___x_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1788_ = lean_nat_add(v_lo_1774_, v_hi_1775_);
v___x_1789_ = lean_unsigned_to_nat(1u);
v_mid_1790_ = lean_nat_shiftr(v___x_1788_, v___x_1789_);
lean_dec(v___x_1788_);
v___x_1803_ = lean_array_fget_borrowed(v_as_1773_, v_mid_1790_);
v___x_1804_ = lean_array_fget_borrowed(v_as_1773_, v_lo_1774_);
v___x_1805_ = l_Lean_Name_quickLt(v___x_1803_, v___x_1804_);
if (v___x_1805_ == 0)
{
v___y_1798_ = v_as_1773_;
goto v___jp_1797_;
}
else
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_array_fswap(v_as_1773_, v_lo_1774_, v_mid_1790_);
v___y_1798_ = v___x_1806_;
goto v___jp_1797_;
}
v___jp_1791_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v___x_1793_ = lean_array_fget_borrowed(v___y_1792_, v_mid_1790_);
v___x_1794_ = lean_array_fget_borrowed(v___y_1792_, v_hi_1775_);
v___x_1795_ = l_Lean_Name_quickLt(v___x_1793_, v___x_1794_);
if (v___x_1795_ == 0)
{
lean_dec(v_mid_1790_);
v___y_1777_ = v___y_1792_;
goto v___jp_1776_;
}
else
{
lean_object* v___x_1796_; 
v___x_1796_ = lean_array_fswap(v___y_1792_, v_mid_1790_, v_hi_1775_);
lean_dec(v_mid_1790_);
v___y_1777_ = v___x_1796_;
goto v___jp_1776_;
}
}
v___jp_1797_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1799_ = lean_array_fget_borrowed(v___y_1798_, v_hi_1775_);
v___x_1800_ = lean_array_fget_borrowed(v___y_1798_, v_lo_1774_);
v___x_1801_ = l_Lean_Name_quickLt(v___x_1799_, v___x_1800_);
if (v___x_1801_ == 0)
{
v___y_1792_ = v___y_1798_;
goto v___jp_1791_;
}
else
{
lean_object* v___x_1802_; 
v___x_1802_ = lean_array_fswap(v___y_1798_, v_lo_1774_, v_hi_1775_);
v___y_1792_ = v___x_1802_;
goto v___jp_1791_;
}
}
}
v___jp_1776_:
{
lean_object* v_pivot_1778_; lean_object* v___x_1779_; lean_object* v_fst_1780_; lean_object* v_snd_1781_; uint8_t v___x_1782_; 
v_pivot_1778_ = lean_array_fget(v___y_1777_, v_hi_1775_);
lean_inc_n(v_lo_1774_, 2);
v___x_1779_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1775_, v_pivot_1778_, v___y_1777_, v_lo_1774_, v_lo_1774_);
lean_dec(v_pivot_1778_);
v_fst_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_fst_1780_);
v_snd_1781_ = lean_ctor_get(v___x_1779_, 1);
lean_inc(v_snd_1781_);
lean_dec_ref(v___x_1779_);
v___x_1782_ = lean_nat_dec_le(v_hi_1775_, v_fst_1780_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1772_, v_snd_1781_, v_lo_1774_, v_fst_1780_);
v___x_1784_ = lean_unsigned_to_nat(1u);
v___x_1785_ = lean_nat_add(v_fst_1780_, v___x_1784_);
lean_dec(v_fst_1780_);
v_as_1773_ = v___x_1783_;
v_lo_1774_ = v___x_1785_;
goto _start;
}
else
{
lean_dec(v_fst_1780_);
lean_dec(v_lo_1774_);
return v_snd_1781_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1807_, lean_object* v_as_1808_, lean_object* v_lo_1809_, lean_object* v_hi_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1807_, v_as_1808_, v_lo_1809_, v_hi_1810_);
lean_dec(v_hi_1810_);
lean_dec(v_n_1807_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1812_, lean_object* v_as_1813_, size_t v_i_1814_, size_t v_stop_1815_, lean_object* v_b_1816_){
_start:
{
lean_object* v___y_1818_; uint8_t v___x_1822_; 
v___x_1822_ = lean_usize_dec_eq(v_i_1814_, v_stop_1815_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; uint8_t v___x_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1823_ = lean_array_uget_borrowed(v_as_1813_, v_i_1814_);
v___x_1824_ = 1;
lean_inc_ref(v_env_1812_);
v___x_1825_ = l_Lean_Environment_setExporting(v_env_1812_, v___x_1824_);
lean_inc(v___x_1823_);
v___x_1826_ = l_Lean_Environment_contains(v___x_1825_, v___x_1823_, v___x_1822_);
if (v___x_1826_ == 0)
{
v___y_1818_ = v_b_1816_;
goto v___jp_1817_;
}
else
{
lean_object* v___x_1827_; 
lean_inc(v___x_1823_);
v___x_1827_ = lean_array_push(v_b_1816_, v___x_1823_);
v___y_1818_ = v___x_1827_;
goto v___jp_1817_;
}
}
else
{
lean_dec_ref(v_env_1812_);
return v_b_1816_;
}
v___jp_1817_:
{
size_t v___x_1819_; size_t v___x_1820_; 
v___x_1819_ = ((size_t)1ULL);
v___x_1820_ = lean_usize_add(v_i_1814_, v___x_1819_);
v_i_1814_ = v___x_1820_;
v_b_1816_ = v___y_1818_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1828_, lean_object* v_as_1829_, lean_object* v_i_1830_, lean_object* v_stop_1831_, lean_object* v_b_1832_){
_start:
{
size_t v_i_boxed_1833_; size_t v_stop_boxed_1834_; lean_object* v_res_1835_; 
v_i_boxed_1833_ = lean_unbox_usize(v_i_1830_);
lean_dec(v_i_1830_);
v_stop_boxed_1834_ = lean_unbox_usize(v_stop_1831_);
lean_dec(v_stop_1831_);
v_res_1835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1828_, v_as_1829_, v_i_boxed_1833_, v_stop_boxed_1834_, v_b_1832_);
lean_dec_ref(v_as_1829_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1836_, lean_object* v_x_1837_){
_start:
{
if (lean_obj_tag(v_x_1837_) == 0)
{
lean_object* v_k_1838_; lean_object* v_l_1839_; lean_object* v_r_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v_k_1838_ = lean_ctor_get(v_x_1837_, 1);
lean_inc(v_k_1838_);
v_l_1839_ = lean_ctor_get(v_x_1837_, 3);
lean_inc(v_l_1839_);
v_r_1840_ = lean_ctor_get(v_x_1837_, 4);
lean_inc(v_r_1840_);
lean_dec_ref_known(v_x_1837_, 5);
v___x_1841_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1836_, v_l_1839_);
v___x_1842_ = lean_array_push(v___x_1841_, v_k_1838_);
v_init_1836_ = v___x_1842_;
v_x_1837_ = v_r_1840_;
goto _start;
}
else
{
return v_init_1836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1844_, lean_object* v_es_1845_){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___y_1849_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___y_1860_; lean_object* v___y_1861_; uint8_t v___x_1863_; 
v___x_1846_ = lean_unsigned_to_nat(0u);
v___x_1847_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1857_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1847_, v_es_1845_);
v___x_1858_ = lean_array_get_size(v___x_1857_);
v___x_1863_ = lean_nat_dec_eq(v___x_1858_, v___x_1846_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___y_1867_; uint8_t v___x_1869_; 
v___x_1864_ = lean_unsigned_to_nat(1u);
v___x_1865_ = lean_nat_sub(v___x_1858_, v___x_1864_);
v___x_1869_ = lean_nat_dec_le(v___x_1846_, v___x_1865_);
if (v___x_1869_ == 0)
{
lean_inc(v___x_1865_);
v___y_1867_ = v___x_1865_;
goto v___jp_1866_;
}
else
{
v___y_1867_ = v___x_1846_;
goto v___jp_1866_;
}
v___jp_1866_:
{
uint8_t v___x_1868_; 
v___x_1868_ = lean_nat_dec_le(v___y_1867_, v___x_1865_);
if (v___x_1868_ == 0)
{
lean_dec(v___x_1865_);
lean_inc(v___y_1867_);
v___y_1860_ = v___y_1867_;
v___y_1861_ = v___y_1867_;
goto v___jp_1859_;
}
else
{
v___y_1860_ = v___y_1867_;
v___y_1861_ = v___x_1865_;
goto v___jp_1859_;
}
}
}
else
{
v___y_1849_ = v___x_1857_;
goto v___jp_1848_;
}
v___jp_1848_:
{
lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1850_ = lean_array_get_size(v___y_1849_);
v___x_1851_ = lean_nat_dec_lt(v___x_1846_, v___x_1850_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; 
lean_dec_ref(v_env_1844_);
v___x_1852_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1847_);
lean_ctor_set(v___x_1852_, 1, v___x_1847_);
lean_ctor_set(v___x_1852_, 2, v___y_1849_);
return v___x_1852_;
}
else
{
size_t v___x_1853_; size_t v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1853_ = ((size_t)0ULL);
v___x_1854_ = lean_usize_of_nat(v___x_1850_);
v___x_1855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1844_, v___y_1849_, v___x_1853_, v___x_1854_, v___x_1847_);
lean_inc_ref(v___x_1855_);
v___x_1856_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
lean_ctor_set(v___x_1856_, 2, v___y_1849_);
return v___x_1856_;
}
}
v___jp_1859_:
{
lean_object* v___x_1862_; 
v___x_1862_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1858_, v___x_1857_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
v___y_1849_ = v___x_1862_;
goto v___jp_1848_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v_name_1870_, lean_object* v_decl_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1875_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1876_ = l_Lean_MessageData_ofName(v_name_1870_);
v___x_1877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1875_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1877_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1879_, v___y_1872_, v___y_1873_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v_name_1881_, lean_object* v_decl_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_registerTagAttribute___lam__4(v_name_1881_, v_decl_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v_decl_1882_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1887_, lean_object* v_x_1888_, lean_object* v_x_1889_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1887_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_registerTagAttribute___lam__5(v___x_1892_, v_x_1893_, v_x_1894_);
lean_dec_ref(v_x_1894_);
lean_dec_ref(v_x_1893_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v___x_1897_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1897_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v___x_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_registerTagAttribute___lam__6(v___x_1900_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_a_1903_, lean_object* v_decl_1904_, lean_object* v_s_1905_){
_start:
{
lean_object* v_addEntryFn_1906_; lean_object* v_importedEntries_1907_; lean_object* v_state_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1916_; 
v_addEntryFn_1906_ = lean_ctor_get(v_a_1903_, 3);
lean_inc(v_addEntryFn_1906_);
lean_dec_ref(v_a_1903_);
v_importedEntries_1907_ = lean_ctor_get(v_s_1905_, 0);
v_state_1908_ = lean_ctor_get(v_s_1905_, 1);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_s_1905_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1910_ = v_s_1905_;
v_isShared_1911_ = v_isSharedCheck_1916_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_state_1908_);
lean_inc(v_importedEntries_1907_);
lean_dec(v_s_1905_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1916_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v_state_1912_; lean_object* v___x_1914_; 
v_state_1912_ = lean_apply_2(v_addEntryFn_1906_, v_state_1908_, v_decl_1904_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 1, v_state_1912_);
v___x_1914_ = v___x_1910_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_importedEntries_1907_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_state_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1917_, lean_object* v_declName_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1922_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1923_ = l_Lean_MessageData_ofName(v_attrName_1917_);
v___x_1924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = 0;
v___x_1928_ = l_Lean_MessageData_ofConstName(v_declName_1918_, v___x_1927_);
v___x_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1926_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1931_, v___y_1919_, v___y_1920_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1933_, lean_object* v_declName_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1933_, v_declName_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1939_, lean_object* v_declName_1940_, lean_object* v_asyncPrefix_x3f_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v___y_1946_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1941_) == 0)
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Lean_MessageData_nil;
v___y_1946_ = v___x_1959_;
goto v___jp_1945_;
}
else
{
lean_object* v_val_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v_val_1960_ = lean_ctor_get(v_asyncPrefix_x3f_1941_, 0);
lean_inc(v_val_1960_);
lean_dec_ref_known(v_asyncPrefix_x3f_1941_, 1);
v___x_1961_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1962_ = l_Lean_MessageData_ofName(v_val_1960_);
v___x_1963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1961_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1963_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___y_1946_ = v___x_1965_;
goto v___jp_1945_;
}
v___jp_1945_:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1947_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1948_ = l_Lean_MessageData_ofName(v_attrName_1939_);
v___x_1949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = 0;
v___x_1953_ = l_Lean_MessageData_ofConstName(v_declName_1940_, v___x_1952_);
v___x_1954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1951_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
v___x_1955_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1954_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
lean_ctor_set(v___x_1957_, 1, v___y_1946_);
v___x_1958_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1957_, v___y_1942_, v___y_1943_);
return v___x_1958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1966_, lean_object* v_declName_1967_, lean_object* v_asyncPrefix_x3f_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1966_, v_declName_1967_, v_asyncPrefix_x3f_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1973_, uint8_t v_kind_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___y_1984_; 
v___x_1978_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1979_ = l_Lean_MessageData_ofName(v_name_1973_);
v___x_1980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1978_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1980_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
switch(v_kind_1974_)
{
case 0:
{
lean_object* v___x_1991_; 
v___x_1991_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1984_ = v___x_1991_;
goto v___jp_1983_;
}
case 1:
{
lean_object* v___x_1992_; 
v___x_1992_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1984_ = v___x_1992_;
goto v___jp_1983_;
}
default: 
{
lean_object* v___x_1993_; 
v___x_1993_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1984_ = v___x_1993_;
goto v___jp_1983_;
}
}
v___jp_1983_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
lean_inc_ref(v___y_1984_);
v___x_1985_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1985_, 0, v___y_1984_);
v___x_1986_ = l_Lean_MessageData_ofFormat(v___x_1985_);
v___x_1987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1982_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
v___x_1988_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1987_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1989_, v___y_1975_, v___y_1976_);
return v___x_1990_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_1994_, lean_object* v_kind_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
uint8_t v_kind_boxed_1999_; lean_object* v_res_2000_; 
v_kind_boxed_1999_ = lean_unbox(v_kind_1995_);
v_res_2000_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1994_, v_kind_boxed_1999_, v___y_1996_, v___y_1997_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__8(lean_object* v_a_2001_, lean_object* v_validate_2002_, lean_object* v_name_2003_, lean_object* v_decl_2004_, lean_object* v_stx_2005_, uint8_t v_kind_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v_nextMacroScope_2013_; lean_object* v_ngen_2014_; lean_object* v_auxDeclNGen_2015_; lean_object* v_traceState_2016_; lean_object* v_recordedDeps_2017_; lean_object* v_messages_2018_; lean_object* v_infoState_2019_; lean_object* v_snapshotTasks_2020_; lean_object* v___y_2021_; lean_object* v___f_2026_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___x_2063_; 
lean_inc(v_decl_2004_);
lean_inc_ref(v_a_2001_);
v___f_2026_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7), 3, 2);
lean_closure_set(v___f_2026_, 0, v_a_2001_);
lean_closure_set(v___f_2026_, 1, v_decl_2004_);
v___x_2063_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2005_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2063_) == 0)
{
uint8_t v___x_2064_; uint8_t v___x_2065_; 
lean_dec_ref_known(v___x_2063_, 1);
v___x_2064_ = 0;
v___x_2065_ = l_Lean_instBEqAttributeKind_beq(v_kind_2006_, v___x_2064_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2066_; 
lean_dec_ref(v___f_2026_);
lean_dec(v_decl_2004_);
lean_dec_ref(v_validate_2002_);
lean_dec_ref(v_a_2001_);
v___x_2066_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2003_, v_kind_2006_, v___y_2007_, v___y_2008_);
return v___x_2066_;
}
else
{
goto v___jp_2058_;
}
}
else
{
lean_dec_ref(v___f_2026_);
lean_dec(v_decl_2004_);
lean_dec(v_name_2003_);
lean_dec_ref(v_validate_2002_);
lean_dec_ref(v_a_2001_);
return v___x_2063_;
}
v___jp_2010_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2022_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_2023_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2023_, 0, v___y_2021_);
lean_ctor_set(v___x_2023_, 1, v_nextMacroScope_2013_);
lean_ctor_set(v___x_2023_, 2, v_ngen_2014_);
lean_ctor_set(v___x_2023_, 3, v_auxDeclNGen_2015_);
lean_ctor_set(v___x_2023_, 4, v_traceState_2016_);
lean_ctor_set(v___x_2023_, 5, v___x_2022_);
lean_ctor_set(v___x_2023_, 6, v_recordedDeps_2017_);
lean_ctor_set(v___x_2023_, 7, v_messages_2018_);
lean_ctor_set(v___x_2023_, 8, v_infoState_2019_);
lean_ctor_set(v___x_2023_, 9, v_snapshotTasks_2020_);
v___x_2024_ = lean_st_ref_put(v___y_2012_, v___x_2023_);
v___x_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___y_2011_);
return v___x_2025_;
}
v___jp_2027_:
{
lean_object* v___x_2030_; 
lean_inc(v___y_2029_);
lean_inc_ref(v___y_2028_);
lean_inc(v_decl_2004_);
v___x_2030_ = lean_apply_4(v_validate_2002_, v_decl_2004_, v___y_2028_, v___y_2029_, lean_box(0));
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v___x_2031_; lean_object* v_toEnvExtension_2032_; lean_object* v_env_2033_; lean_object* v_nextMacroScope_2034_; lean_object* v_ngen_2035_; lean_object* v_auxDeclNGen_2036_; lean_object* v_traceState_2037_; lean_object* v_recordedDeps_2038_; lean_object* v_messages_2039_; lean_object* v_infoState_2040_; lean_object* v_snapshotTasks_2041_; lean_object* v_asyncMode_2042_; uint8_t v_logWrites_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; 
lean_dec_ref_known(v___x_2030_, 1);
v___x_2031_ = lean_st_ref_take(v___y_2029_);
v_toEnvExtension_2032_ = lean_ctor_get(v_a_2001_, 0);
lean_inc_ref(v_toEnvExtension_2032_);
lean_dec_ref(v_a_2001_);
v_env_2033_ = lean_ctor_get(v___x_2031_, 0);
lean_inc_ref(v_env_2033_);
v_nextMacroScope_2034_ = lean_ctor_get(v___x_2031_, 1);
lean_inc(v_nextMacroScope_2034_);
v_ngen_2035_ = lean_ctor_get(v___x_2031_, 2);
lean_inc_ref(v_ngen_2035_);
v_auxDeclNGen_2036_ = lean_ctor_get(v___x_2031_, 3);
lean_inc_ref(v_auxDeclNGen_2036_);
v_traceState_2037_ = lean_ctor_get(v___x_2031_, 4);
lean_inc_ref(v_traceState_2037_);
v_recordedDeps_2038_ = lean_ctor_get(v___x_2031_, 6);
lean_inc_ref(v_recordedDeps_2038_);
v_messages_2039_ = lean_ctor_get(v___x_2031_, 7);
lean_inc_ref(v_messages_2039_);
v_infoState_2040_ = lean_ctor_get(v___x_2031_, 8);
lean_inc_ref(v_infoState_2040_);
v_snapshotTasks_2041_ = lean_ctor_get(v___x_2031_, 9);
lean_inc_ref(v_snapshotTasks_2041_);
lean_dec(v___x_2031_);
v_asyncMode_2042_ = lean_ctor_get(v_toEnvExtension_2032_, 2);
lean_inc(v_asyncMode_2042_);
v_logWrites_2043_ = lean_ctor_get_uint8(v_toEnvExtension_2032_, sizeof(void*)*6);
v___x_2044_ = lean_box(0);
v___x_2045_ = 1;
if (v_logWrites_2043_ == 0)
{
lean_object* v___x_2046_; 
v___x_2046_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2032_, v_env_2033_, v___f_2026_, v_asyncMode_2042_, v_decl_2004_, v___x_2045_);
lean_dec(v_asyncMode_2042_);
v___y_2011_ = v___x_2044_;
v___y_2012_ = v___y_2029_;
v_nextMacroScope_2013_ = v_nextMacroScope_2034_;
v_ngen_2014_ = v_ngen_2035_;
v_auxDeclNGen_2015_ = v_auxDeclNGen_2036_;
v_traceState_2016_ = v_traceState_2037_;
v_recordedDeps_2017_ = v_recordedDeps_2038_;
v_messages_2018_ = v_messages_2039_;
v_infoState_2019_ = v_infoState_2040_;
v_snapshotTasks_2020_ = v_snapshotTasks_2041_;
v___y_2021_ = v___x_2046_;
goto v___jp_2010_;
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
lean_inc(v_decl_2004_);
v___x_2047_ = l_Lean_Environment_logDeclChange(v_env_2033_, v_decl_2004_);
v___x_2048_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2032_, v___x_2047_, v___f_2026_, v_asyncMode_2042_, v_decl_2004_, v___x_2045_);
lean_dec(v_asyncMode_2042_);
v___y_2011_ = v___x_2044_;
v___y_2012_ = v___y_2029_;
v_nextMacroScope_2013_ = v_nextMacroScope_2034_;
v_ngen_2014_ = v_ngen_2035_;
v_auxDeclNGen_2015_ = v_auxDeclNGen_2036_;
v_traceState_2016_ = v_traceState_2037_;
v_recordedDeps_2017_ = v_recordedDeps_2038_;
v_messages_2018_ = v_messages_2039_;
v_infoState_2019_ = v_infoState_2040_;
v_snapshotTasks_2020_ = v_snapshotTasks_2041_;
v___y_2021_ = v___x_2048_;
goto v___jp_2010_;
}
}
else
{
lean_dec_ref(v___f_2026_);
lean_dec(v_decl_2004_);
lean_dec_ref(v_a_2001_);
return v___x_2030_;
}
}
v___jp_2049_:
{
lean_object* v_toEnvExtension_2053_; lean_object* v_asyncMode_2054_; uint8_t v___x_2055_; 
v_toEnvExtension_2053_ = lean_ctor_get(v_a_2001_, 0);
v_asyncMode_2054_ = lean_ctor_get(v_toEnvExtension_2053_, 2);
lean_inc(v_decl_2004_);
lean_inc_ref(v___y_2050_);
v___x_2055_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2050_, v_decl_2004_, v_asyncMode_2054_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
lean_dec_ref(v___f_2026_);
lean_dec_ref(v_validate_2002_);
lean_dec_ref(v_a_2001_);
v___x_2056_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2050_);
v___x_2057_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_2003_, v_decl_2004_, v___x_2056_, v___y_2051_, v___y_2052_);
return v___x_2057_;
}
else
{
lean_dec_ref(v___y_2050_);
lean_dec(v_name_2003_);
v___y_2028_ = v___y_2051_;
v___y_2029_ = v___y_2052_;
goto v___jp_2027_;
}
}
v___jp_2058_:
{
lean_object* v___x_2059_; lean_object* v_env_2060_; lean_object* v___x_2061_; 
v___x_2059_ = lean_st_ref_get(v___y_2008_);
v_env_2060_ = lean_ctor_get(v___x_2059_, 0);
lean_inc_ref(v_env_2060_);
lean_dec(v___x_2059_);
v___x_2061_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2060_, v_decl_2004_);
if (lean_obj_tag(v___x_2061_) == 0)
{
v___y_2050_ = v_env_2060_;
v___y_2051_ = v___y_2007_;
v___y_2052_ = v___y_2008_;
goto v___jp_2049_;
}
else
{
lean_object* v___x_2062_; 
lean_dec_ref_known(v___x_2061_, 1);
lean_dec_ref(v_env_2060_);
lean_dec_ref(v___f_2026_);
lean_dec_ref(v_validate_2002_);
lean_dec_ref(v_a_2001_);
v___x_2062_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2003_, v_decl_2004_, v___y_2007_, v___y_2008_);
return v___x_2062_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__8___boxed(lean_object* v_a_2067_, lean_object* v_validate_2068_, lean_object* v_name_2069_, lean_object* v_decl_2070_, lean_object* v_stx_2071_, lean_object* v_kind_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
uint8_t v_kind_boxed_2076_; lean_object* v_res_2077_; 
v_kind_boxed_2076_ = lean_unbox(v_kind_2072_);
v_res_2077_ = l_Lean_registerTagAttribute___lam__8(v_a_2067_, v_validate_2068_, v_name_2069_, v_decl_2070_, v_stx_2071_, v_kind_boxed_2076_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
return v_res_2077_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2083_; lean_object* v___f_2084_; 
v___x_2083_ = l_Lean_NameSet_empty;
v___f_2084_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 4, 1);
lean_closure_set(v___f_2084_, 0, v___x_2083_);
return v___f_2084_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___f_2086_; 
v___x_2085_ = l_Lean_NameSet_empty;
v___f_2086_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 2, 1);
lean_closure_set(v___f_2086_, 0, v___x_2085_);
return v___f_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2089_, lean_object* v_descr_2090_, lean_object* v_validate_2091_, lean_object* v_ref_2092_, uint8_t v_applicationTime_2093_, lean_object* v_asyncMode_2094_, uint8_t v_logWrites_2095_){
_start:
{
lean_object* v___f_2097_; lean_object* v___f_2098_; lean_object* v___f_2099_; lean_object* v___f_2100_; lean_object* v___f_2101_; lean_object* v___f_2102_; lean_object* v___f_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___f_2097_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2098_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2099_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2100_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
lean_inc(v_name_2089_);
v___f_2101_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 5, 1);
lean_closure_set(v___f_2101_, 0, v_name_2089_);
v___f_2102_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2103_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2104_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
v___x_2105_ = 0;
lean_inc(v_ref_2092_);
v___x_2106_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2106_, 0, v_ref_2092_);
lean_ctor_set(v___x_2106_, 1, v___f_2103_);
lean_ctor_set(v___x_2106_, 2, v___f_2102_);
lean_ctor_set(v___x_2106_, 3, v___f_2100_);
lean_ctor_set(v___x_2106_, 4, v___f_2099_);
lean_ctor_set(v___x_2106_, 5, v___f_2098_);
lean_ctor_set(v___x_2106_, 6, v_asyncMode_2094_);
lean_ctor_set(v___x_2106_, 7, v___x_2104_);
lean_ctor_set_uint8(v___x_2106_, sizeof(void*)*8, v___x_2105_);
lean_ctor_set_uint8(v___x_2106_, sizeof(void*)*8 + 1, v_logWrites_2095_);
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v___f_2097_);
v___x_2108_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2107_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v___f_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc_n(v_a_2109_, 2);
lean_dec_ref_known(v___x_2108_, 1);
lean_inc(v_name_2089_);
v___f_2110_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__8___boxed), 9, 3);
lean_closure_set(v___f_2110_, 0, v_a_2109_);
lean_closure_set(v___f_2110_, 1, v_validate_2091_);
lean_closure_set(v___f_2110_, 2, v_name_2089_);
v___x_2111_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2111_, 0, v_ref_2092_);
lean_ctor_set(v___x_2111_, 1, v_name_2089_);
lean_ctor_set(v___x_2111_, 2, v_descr_2090_);
lean_ctor_set_uint8(v___x_2111_, sizeof(void*)*3, v_applicationTime_2093_);
v___x_2112_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
lean_ctor_set(v___x_2112_, 1, v___f_2110_);
lean_ctor_set(v___x_2112_, 2, v___f_2101_);
lean_inc_ref(v___x_2112_);
v___x_2113_ = l_Lean_registerBuiltinAttribute(v___x_2112_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2121_; 
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2121_ == 0)
{
lean_object* v_unused_2122_; 
v_unused_2122_ = lean_ctor_get(v___x_2113_, 0);
lean_dec(v_unused_2122_);
v___x_2115_ = v___x_2113_;
v_isShared_2116_ = v_isSharedCheck_2121_;
goto v_resetjp_2114_;
}
else
{
lean_dec(v___x_2113_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2121_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2112_);
lean_ctor_set(v___x_2117_, 1, v_a_2109_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2117_);
v___x_2119_ = v___x_2115_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec_ref_known(v___x_2112_, 3);
lean_dec(v_a_2109_);
v_a_2123_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2113_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2113_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec_ref(v___f_2101_);
lean_dec(v_ref_2092_);
lean_dec_ref(v_validate_2091_);
lean_dec_ref(v_descr_2090_);
lean_dec(v_name_2089_);
v_a_2131_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2108_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2108_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2139_, lean_object* v_descr_2140_, lean_object* v_validate_2141_, lean_object* v_ref_2142_, lean_object* v_applicationTime_2143_, lean_object* v_asyncMode_2144_, lean_object* v_logWrites_2145_, lean_object* v_a_2146_){
_start:
{
uint8_t v_applicationTime_boxed_2147_; uint8_t v_logWrites_boxed_2148_; lean_object* v_res_2149_; 
v_applicationTime_boxed_2147_ = lean_unbox(v_applicationTime_2143_);
v_logWrites_boxed_2148_ = lean_unbox(v_logWrites_2145_);
v_res_2149_ = l_Lean_registerTagAttribute(v_name_2139_, v_descr_2140_, v_validate_2141_, v_ref_2142_, v_applicationTime_boxed_2147_, v_asyncMode_2144_, v_logWrites_boxed_2148_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2150_, lean_object* v_t_2151_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2150_, v_t_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2153_, lean_object* v_as_2154_, lean_object* v_lo_2155_, lean_object* v_hi_2156_, lean_object* v_w_2157_, lean_object* v_hlo_2158_, lean_object* v_hhi_2159_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2153_, v_as_2154_, v_lo_2155_, v_hi_2156_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2161_, lean_object* v_as_2162_, lean_object* v_lo_2163_, lean_object* v_hi_2164_, lean_object* v_w_2165_, lean_object* v_hlo_2166_, lean_object* v_hhi_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2161_, v_as_2162_, v_lo_2163_, v_hi_2164_, v_w_2165_, v_hlo_2166_, v_hhi_2167_);
lean_dec(v_hi_2164_);
lean_dec(v_n_2161_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2169_, lean_object* v_attrName_2170_, lean_object* v_declName_2171_, lean_object* v_asyncPrefix_x3f_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2170_, v_declName_2171_, v_asyncPrefix_x3f_2172_, v___y_2173_, v___y_2174_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2177_, lean_object* v_attrName_2178_, lean_object* v_declName_2179_, lean_object* v_asyncPrefix_x3f_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2177_, v_attrName_2178_, v_declName_2179_, v_asyncPrefix_x3f_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2185_, lean_object* v_attrName_2186_, lean_object* v_declName_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2186_, v_declName_2187_, v___y_2188_, v___y_2189_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2192_, lean_object* v_attrName_2193_, lean_object* v_declName_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2192_, v_attrName_2193_, v_declName_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2199_, lean_object* v_name_2200_, uint8_t v_kind_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2200_, v_kind_2201_, v___y_2202_, v___y_2203_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2206_, lean_object* v_name_2207_, lean_object* v_kind_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
uint8_t v_kind_boxed_2212_; lean_object* v_res_2213_; 
v_kind_boxed_2212_ = lean_unbox(v_kind_2208_);
v_res_2213_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2206_, v_name_2207_, v_kind_boxed_2212_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2214_, lean_object* v_lo_2215_, lean_object* v_hi_2216_, lean_object* v_hhi_2217_, lean_object* v_pivot_2218_, lean_object* v_as_2219_, lean_object* v_i_2220_, lean_object* v_k_2221_, lean_object* v_ilo_2222_, lean_object* v_ik_2223_, lean_object* v_w_2224_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2216_, v_pivot_2218_, v_as_2219_, v_i_2220_, v_k_2221_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2226_, lean_object* v_lo_2227_, lean_object* v_hi_2228_, lean_object* v_hhi_2229_, lean_object* v_pivot_2230_, lean_object* v_as_2231_, lean_object* v_i_2232_, lean_object* v_k_2233_, lean_object* v_ilo_2234_, lean_object* v_ik_2235_, lean_object* v_w_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2226_, v_lo_2227_, v_hi_2228_, v_hhi_2229_, v_pivot_2230_, v_as_2231_, v_i_2232_, v_k_2233_, v_ilo_2234_, v_ik_2235_, v_w_2236_);
lean_dec(v_pivot_2230_);
lean_dec(v_hi_2228_);
lean_dec(v_lo_2227_);
lean_dec(v_n_2226_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_addEntryFn_2238_, lean_object* v_decl_2239_, lean_object* v_s_2240_){
_start:
{
lean_object* v_importedEntries_2241_; lean_object* v_state_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2250_; 
v_importedEntries_2241_ = lean_ctor_get(v_s_2240_, 0);
v_state_2242_ = lean_ctor_get(v_s_2240_, 1);
v_isSharedCheck_2250_ = !lean_is_exclusive(v_s_2240_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2244_ = v_s_2240_;
v_isShared_2245_ = v_isSharedCheck_2250_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_state_2242_);
lean_inc(v_importedEntries_2241_);
lean_dec(v_s_2240_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2250_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v_state_2246_; lean_object* v___x_2248_; 
v_state_2246_ = lean_apply_2(v_addEntryFn_2238_, v_state_2242_, v_decl_2239_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 1, v_state_2246_);
v___x_2248_ = v___x_2244_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_importedEntries_2241_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_state_2246_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_attr_2251_, lean_object* v_decl_2252_, lean_object* v_env_2253_){
_start:
{
lean_object* v_ext_2254_; lean_object* v_toEnvExtension_2255_; lean_object* v_addEntryFn_2256_; lean_object* v_asyncMode_2257_; uint8_t v_logWrites_2258_; lean_object* v___f_2259_; uint8_t v___x_2260_; 
v_ext_2254_ = lean_ctor_get(v_attr_2251_, 1);
lean_inc_ref(v_ext_2254_);
lean_dec_ref(v_attr_2251_);
v_toEnvExtension_2255_ = lean_ctor_get(v_ext_2254_, 0);
lean_inc_ref(v_toEnvExtension_2255_);
v_addEntryFn_2256_ = lean_ctor_get(v_ext_2254_, 3);
lean_inc(v_addEntryFn_2256_);
lean_dec_ref(v_ext_2254_);
v_asyncMode_2257_ = lean_ctor_get(v_toEnvExtension_2255_, 2);
lean_inc(v_asyncMode_2257_);
v_logWrites_2258_ = lean_ctor_get_uint8(v_toEnvExtension_2255_, sizeof(void*)*6);
lean_inc(v_decl_2252_);
v___f_2259_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2259_, 0, v_addEntryFn_2256_);
lean_closure_set(v___f_2259_, 1, v_decl_2252_);
v___x_2260_ = 1;
if (v_logWrites_2258_ == 0)
{
lean_object* v___x_2261_; 
v___x_2261_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2255_, v_env_2253_, v___f_2259_, v_asyncMode_2257_, v_decl_2252_, v___x_2260_);
lean_dec(v_asyncMode_2257_);
return v___x_2261_;
}
else
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
lean_inc_ref(v_toEnvExtension_2255_);
v___x_2262_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2255_, v_env_2253_);
lean_dec_ref(v_env_2253_);
v___x_2263_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2255_, v___x_2262_, v___f_2259_, v_asyncMode_2257_, v_decl_2252_, v___x_2260_);
lean_dec(v_asyncMode_2257_);
return v___x_2263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_modifyEnv_2264_, lean_object* v___f_2265_, lean_object* v_____r_2266_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = lean_apply_1(v_modifyEnv_2264_, v___f_2265_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v_attr_2268_, lean_object* v_env_2269_, lean_object* v_decl_2270_, lean_object* v_inst_2271_, lean_object* v_inst_2272_, lean_object* v_toBind_2273_, lean_object* v___f_2274_, lean_object* v_modifyEnv_2275_, lean_object* v___f_2276_, lean_object* v_____r_2277_){
_start:
{
lean_object* v_ext_2278_; lean_object* v_toEnvExtension_2279_; lean_object* v_attr_2280_; lean_object* v_asyncMode_2281_; uint8_t v___x_2282_; 
v_ext_2278_ = lean_ctor_get(v_attr_2268_, 1);
v_toEnvExtension_2279_ = lean_ctor_get(v_ext_2278_, 0);
lean_inc_ref(v_toEnvExtension_2279_);
v_attr_2280_ = lean_ctor_get(v_attr_2268_, 0);
lean_inc_ref(v_attr_2280_);
lean_dec_ref(v_attr_2268_);
v_asyncMode_2281_ = lean_ctor_get(v_toEnvExtension_2279_, 2);
lean_inc(v_asyncMode_2281_);
lean_dec_ref(v_toEnvExtension_2279_);
lean_inc(v_decl_2270_);
lean_inc_ref(v_env_2269_);
v___x_2282_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2269_, v_decl_2270_, v_asyncMode_2281_);
lean_dec(v_asyncMode_2281_);
if (v___x_2282_ == 0)
{
lean_object* v_toAttributeImplCore_2283_; lean_object* v_name_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_dec_ref(v___f_2276_);
lean_dec(v_modifyEnv_2275_);
v_toAttributeImplCore_2283_ = lean_ctor_get(v_attr_2280_, 0);
lean_inc_ref(v_toAttributeImplCore_2283_);
lean_dec_ref(v_attr_2280_);
v_name_2284_ = lean_ctor_get(v_toAttributeImplCore_2283_, 1);
lean_inc(v_name_2284_);
lean_dec_ref(v_toAttributeImplCore_2283_);
v___x_2285_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2269_);
v___x_2286_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2271_, v_inst_2272_, v_name_2284_, v_decl_2270_, v___x_2285_);
v___x_2287_ = lean_apply_4(v_toBind_2273_, lean_box(0), lean_box(0), v___x_2286_, v___f_2274_);
return v___x_2287_;
}
else
{
lean_object* v___x_2288_; 
lean_dec_ref(v_attr_2280_);
lean_dec(v___f_2274_);
lean_dec(v_toBind_2273_);
lean_dec_ref(v_inst_2272_);
lean_dec_ref(v_inst_2271_);
lean_dec(v_decl_2270_);
lean_dec_ref(v_env_2269_);
v___x_2288_ = lean_apply_1(v_modifyEnv_2275_, v___f_2276_);
return v___x_2288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v___f_2289_, lean_object* v_____r_2290_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_apply_1(v___f_2289_, v_____r_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__5(lean_object* v_attr_2292_, lean_object* v_decl_2293_, lean_object* v_inst_2294_, lean_object* v_inst_2295_, lean_object* v_toBind_2296_, lean_object* v___f_2297_, lean_object* v_modifyEnv_2298_, lean_object* v___f_2299_, lean_object* v_env_2300_){
_start:
{
lean_object* v___f_2301_; lean_object* v___x_2302_; 
lean_inc_ref(v___f_2299_);
lean_inc(v_modifyEnv_2298_);
lean_inc(v___f_2297_);
lean_inc(v_toBind_2296_);
lean_inc_ref(v_inst_2295_);
lean_inc_ref(v_inst_2294_);
lean_inc(v_decl_2293_);
lean_inc_ref(v_env_2300_);
lean_inc_ref(v_attr_2292_);
v___f_2301_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 10, 9);
lean_closure_set(v___f_2301_, 0, v_attr_2292_);
lean_closure_set(v___f_2301_, 1, v_env_2300_);
lean_closure_set(v___f_2301_, 2, v_decl_2293_);
lean_closure_set(v___f_2301_, 3, v_inst_2294_);
lean_closure_set(v___f_2301_, 4, v_inst_2295_);
lean_closure_set(v___f_2301_, 5, v_toBind_2296_);
lean_closure_set(v___f_2301_, 6, v___f_2297_);
lean_closure_set(v___f_2301_, 7, v_modifyEnv_2298_);
lean_closure_set(v___f_2301_, 8, v___f_2299_);
v___x_2302_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2300_, v_decl_2293_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
lean_dec_ref(v___f_2301_);
v___x_2303_ = lean_box(0);
v___x_2304_ = l_Lean_TagAttribute_setTag___redArg___lam__3(v_attr_2292_, v_env_2300_, v_decl_2293_, v_inst_2294_, v_inst_2295_, v_toBind_2296_, v___f_2297_, v_modifyEnv_2298_, v___f_2299_, v___x_2303_);
return v___x_2304_;
}
else
{
lean_object* v_attr_2305_; lean_object* v_toAttributeImplCore_2306_; lean_object* v_name_2307_; lean_object* v___f_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
lean_dec_ref_known(v___x_2302_, 1);
lean_dec_ref(v_env_2300_);
lean_dec_ref(v___f_2299_);
lean_dec(v_modifyEnv_2298_);
lean_dec(v___f_2297_);
v_attr_2305_ = lean_ctor_get(v_attr_2292_, 0);
lean_inc_ref(v_attr_2305_);
lean_dec_ref(v_attr_2292_);
v_toAttributeImplCore_2306_ = lean_ctor_get(v_attr_2305_, 0);
lean_inc_ref(v_toAttributeImplCore_2306_);
lean_dec_ref(v_attr_2305_);
v_name_2307_ = lean_ctor_get(v_toAttributeImplCore_2306_, 1);
lean_inc(v_name_2307_);
lean_dec_ref(v_toAttributeImplCore_2306_);
v___f_2308_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2308_, 0, v___f_2301_);
v___x_2309_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2294_, v_inst_2295_, v_name_2307_, v_decl_2293_);
v___x_2310_ = lean_apply_4(v_toBind_2296_, lean_box(0), lean_box(0), v___x_2309_, v___f_2308_);
return v___x_2310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2311_, lean_object* v_inst_2312_, lean_object* v_inst_2313_, lean_object* v_attr_2314_, lean_object* v_decl_2315_){
_start:
{
lean_object* v_toBind_2316_; lean_object* v_getEnv_2317_; lean_object* v_modifyEnv_2318_; lean_object* v___f_2319_; lean_object* v___f_2320_; lean_object* v___f_2321_; lean_object* v___x_2322_; 
v_toBind_2316_ = lean_ctor_get(v_inst_2311_, 1);
lean_inc_n(v_toBind_2316_, 2);
v_getEnv_2317_ = lean_ctor_get(v_inst_2313_, 0);
lean_inc(v_getEnv_2317_);
v_modifyEnv_2318_ = lean_ctor_get(v_inst_2313_, 1);
lean_inc_n(v_modifyEnv_2318_, 2);
lean_dec_ref(v_inst_2313_);
lean_inc(v_decl_2315_);
lean_inc_ref(v_attr_2314_);
v___f_2319_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2319_, 0, v_attr_2314_);
lean_closure_set(v___f_2319_, 1, v_decl_2315_);
lean_inc_ref(v___f_2319_);
v___f_2320_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2320_, 0, v_modifyEnv_2318_);
lean_closure_set(v___f_2320_, 1, v___f_2319_);
v___f_2321_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__5), 9, 8);
lean_closure_set(v___f_2321_, 0, v_attr_2314_);
lean_closure_set(v___f_2321_, 1, v_decl_2315_);
lean_closure_set(v___f_2321_, 2, v_inst_2311_);
lean_closure_set(v___f_2321_, 3, v_inst_2312_);
lean_closure_set(v___f_2321_, 4, v_toBind_2316_);
lean_closure_set(v___f_2321_, 5, v___f_2320_);
lean_closure_set(v___f_2321_, 6, v_modifyEnv_2318_);
lean_closure_set(v___f_2321_, 7, v___f_2319_);
v___x_2322_ = lean_apply_4(v_toBind_2316_, lean_box(0), lean_box(0), v_getEnv_2317_, v___f_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2323_, lean_object* v_inst_2324_, lean_object* v_inst_2325_, lean_object* v_inst_2326_, lean_object* v_attr_2327_, lean_object* v_decl_2328_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2324_, v_inst_2325_, v_inst_2326_, v_attr_2327_, v_decl_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2330_, lean_object* v_env_2331_, lean_object* v_decl_2332_){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = lean_box(1);
v___x_2334_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2331_, v_decl_2332_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_ext_2335_; lean_object* v_toEnvExtension_2336_; lean_object* v_asyncMode_2337_; uint8_t v___x_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v_ext_2335_ = lean_ctor_get(v_attr_2330_, 1);
v_toEnvExtension_2336_ = lean_ctor_get(v_ext_2335_, 0);
v_asyncMode_2337_ = lean_ctor_get(v_toEnvExtension_2336_, 2);
v___x_2338_ = 0;
lean_inc(v_decl_2332_);
v___x_2339_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2333_, v_ext_2335_, v_env_2331_, v_asyncMode_2337_, v_decl_2332_, v___x_2338_);
v___x_2340_ = l_Lean_NameSet_contains(v___x_2339_, v_decl_2332_);
lean_dec(v_decl_2332_);
lean_dec(v___x_2339_);
return v___x_2340_;
}
else
{
lean_object* v_val_2341_; lean_object* v_ext_2342_; uint8_t v___x_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; 
v_val_2341_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_val_2341_);
lean_dec_ref_known(v___x_2334_, 1);
v_ext_2342_ = lean_ctor_get(v_attr_2330_, 1);
v___x_2343_ = 0;
v___x_2344_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2333_, v_ext_2342_, v_env_2331_, v_val_2341_, v___x_2343_);
lean_dec(v_val_2341_);
lean_dec_ref(v_env_2331_);
v___x_2345_ = l_Lean_containsSortedName(v___x_2344_, v_decl_2332_);
lean_dec(v_decl_2332_);
lean_dec_ref(v___x_2344_);
return v___x_2345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2346_, lean_object* v_env_2347_, lean_object* v_decl_2348_){
_start:
{
uint8_t v_res_2349_; lean_object* v_r_2350_; 
v_res_2349_ = l_Lean_TagAttribute_hasTag(v_attr_2346_, v_env_2347_, v_decl_2348_);
lean_dec_ref(v_attr_2346_);
v_r_2350_ = lean_box(v_res_2349_);
return v_r_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(lean_object* v_x_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0___boxed(lean_object* v_x_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(v_x_2356_, v___y_2357_);
lean_dec_ref(v___y_2357_);
lean_dec_ref(v_x_2356_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(lean_object* v_s_2360_, lean_object* v_x_2361_){
_start:
{
lean_inc_ref(v_s_2360_);
return v_s_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1___boxed(lean_object* v_s_2362_, lean_object* v_x_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(v_s_2362_, v_x_2363_);
lean_dec_ref(v_x_2363_);
lean_dec_ref(v_s_2362_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(lean_object* v_x_2369_, lean_object* v_x_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___boxed(lean_object* v_x_2372_, lean_object* v_x_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(v_x_2372_, v_x_2373_);
lean_dec_ref(v_x_2373_);
lean_dec_ref(v_x_2372_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(lean_object* v_x_2375_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = lean_box(0);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3___boxed(lean_object* v_x_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(v_x_2377_);
lean_dec_ref(v_x_2377_);
return v_res_2378_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4(void){
_start:
{
lean_object* v___f_2383_; lean_object* v___f_2384_; lean_object* v___f_2385_; lean_object* v___f_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___f_2383_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3));
v___f_2384_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2));
v___f_2385_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1));
v___f_2386_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0));
v___x_2387_ = lean_box(0);
v___x_2388_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_2389_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
lean_ctor_set(v___x_2389_, 1, v___x_2387_);
lean_ctor_set(v___x_2389_, 2, v___f_2386_);
lean_ctor_set(v___x_2389_, 3, v___f_2385_);
lean_ctor_set(v___x_2389_, 4, v___f_2384_);
lean_ctor_set(v___x_2389_, 5, v___f_2383_);
return v___x_2389_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5(void){
_start:
{
uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2390_ = 0;
v___x_2391_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4);
v___x_2392_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2393_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
lean_ctor_set(v___x_2393_, 1, v___x_2391_);
lean_ctor_set_uint8(v___x_2393_, sizeof(void*)*2, v___x_2390_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg(){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___boxed(lean_object* v___dummy_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v_res_2397_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__0(void){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2399_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg(){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg___boxed(lean_object* v___dummy_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_instInhabitedParametricAttribute___redArg();
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2405_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object* v_x_2407_, lean_object* v_p_2408_){
_start:
{
lean_object* v_fst_2409_; lean_object* v_snd_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2427_; 
v_fst_2409_ = lean_ctor_get(v_x_2407_, 0);
v_snd_2410_ = lean_ctor_get(v_x_2407_, 1);
v_isSharedCheck_2427_ = !lean_is_exclusive(v_x_2407_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2412_ = v_x_2407_;
v_isShared_2413_ = v_isSharedCheck_2427_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_snd_2410_);
lean_inc(v_fst_2409_);
lean_dec(v_x_2407_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2427_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v_fst_2414_; lean_object* v_snd_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2426_; 
v_fst_2414_ = lean_ctor_get(v_p_2408_, 0);
v_snd_2415_ = lean_ctor_get(v_p_2408_, 1);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_p_2408_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2417_ = v_p_2408_;
v_isShared_2418_ = v_isSharedCheck_2426_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_snd_2415_);
lean_inc(v_fst_2414_);
lean_dec(v_p_2408_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2426_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
lean_inc(v_fst_2414_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set_tag(v___x_2412_, 1);
lean_ctor_set(v___x_2412_, 1, v_fst_2409_);
lean_ctor_set(v___x_2412_, 0, v_fst_2414_);
v___x_2420_ = v___x_2412_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_fst_2414_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v_fst_2409_);
v___x_2420_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
lean_object* v___x_2421_; lean_object* v___x_2423_; 
v___x_2421_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2414_, v_snd_2415_, v_snd_2410_);
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 1, v___x_2421_);
lean_ctor_set(v___x_2417_, 0, v___x_2420_);
v___x_2423_ = v___x_2417_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2420_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object* v_init_2428_, lean_object* v_x_2429_){
_start:
{
if (lean_obj_tag(v_x_2429_) == 0)
{
lean_object* v_k_2430_; lean_object* v_v_2431_; lean_object* v_l_2432_; lean_object* v_r_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v_k_2430_ = lean_ctor_get(v_x_2429_, 1);
v_v_2431_ = lean_ctor_get(v_x_2429_, 2);
v_l_2432_ = lean_ctor_get(v_x_2429_, 3);
v_r_2433_ = lean_ctor_get(v_x_2429_, 4);
v___x_2434_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2428_, v_l_2432_);
lean_inc(v_v_2431_);
lean_inc(v_k_2430_);
v___x_2435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2435_, 0, v_k_2430_);
lean_ctor_set(v___x_2435_, 1, v_v_2431_);
v___x_2436_ = lean_array_push(v___x_2434_, v___x_2435_);
v_init_2428_ = v___x_2436_;
v_x_2429_ = v_r_2433_;
goto _start;
}
else
{
return v_init_2428_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object* v_init_2438_, lean_object* v_x_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2438_, v_x_2439_);
lean_dec(v_x_2439_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object* v_snd_2441_, lean_object* v_as_2442_, size_t v_i_2443_, size_t v_stop_2444_, lean_object* v_b_2445_){
_start:
{
lean_object* v___y_2447_; uint8_t v___x_2451_; 
v___x_2451_ = lean_usize_dec_eq(v_i_2443_, v_stop_2444_);
if (v___x_2451_ == 0)
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_array_uget_borrowed(v_as_2442_, v_i_2443_);
v___x_2453_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2441_, v___x_2452_);
if (lean_obj_tag(v___x_2453_) == 0)
{
v___y_2447_ = v_b_2445_;
goto v___jp_2446_;
}
else
{
lean_object* v_val_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v_val_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_val_2454_);
lean_dec_ref_known(v___x_2453_, 1);
lean_inc(v___x_2452_);
v___x_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2452_);
lean_ctor_set(v___x_2455_, 1, v_val_2454_);
v___x_2456_ = lean_array_push(v_b_2445_, v___x_2455_);
v___y_2447_ = v___x_2456_;
goto v___jp_2446_;
}
}
else
{
return v_b_2445_;
}
v___jp_2446_:
{
size_t v___x_2448_; size_t v___x_2449_; 
v___x_2448_ = ((size_t)1ULL);
v___x_2449_ = lean_usize_add(v_i_2443_, v___x_2448_);
v_i_2443_ = v___x_2449_;
v_b_2445_ = v___y_2447_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2457_, lean_object* v_as_2458_, lean_object* v_i_2459_, lean_object* v_stop_2460_, lean_object* v_b_2461_){
_start:
{
size_t v_i_boxed_2462_; size_t v_stop_boxed_2463_; lean_object* v_res_2464_; 
v_i_boxed_2462_ = lean_unbox_usize(v_i_2459_);
lean_dec(v_i_2459_);
v_stop_boxed_2463_ = lean_unbox_usize(v_stop_2460_);
lean_dec(v_stop_2460_);
v_res_2464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2457_, v_as_2458_, v_i_boxed_2462_, v_stop_boxed_2463_, v_b_2461_);
lean_dec_ref(v_as_2458_);
lean_dec(v_snd_2457_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object* v_snd_2465_, lean_object* v_as_2466_, lean_object* v_start_2467_, lean_object* v_stop_2468_){
_start:
{
lean_object* v___x_2469_; uint8_t v___x_2470_; 
v___x_2469_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2470_ = lean_nat_dec_lt(v_start_2467_, v_stop_2468_);
if (v___x_2470_ == 0)
{
return v___x_2469_;
}
else
{
lean_object* v___x_2471_; uint8_t v___x_2472_; 
v___x_2471_ = lean_array_get_size(v_as_2466_);
v___x_2472_ = lean_nat_dec_le(v_stop_2468_, v___x_2471_);
if (v___x_2472_ == 0)
{
uint8_t v___x_2473_; 
v___x_2473_ = lean_nat_dec_lt(v_start_2467_, v___x_2471_);
if (v___x_2473_ == 0)
{
return v___x_2469_;
}
else
{
size_t v___x_2474_; size_t v___x_2475_; lean_object* v___x_2476_; 
v___x_2474_ = lean_usize_of_nat(v_start_2467_);
v___x_2475_ = lean_usize_of_nat(v___x_2471_);
v___x_2476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2465_, v_as_2466_, v___x_2474_, v___x_2475_, v___x_2469_);
return v___x_2476_;
}
}
else
{
size_t v___x_2477_; size_t v___x_2478_; lean_object* v___x_2479_; 
v___x_2477_ = lean_usize_of_nat(v_start_2467_);
v___x_2478_ = lean_usize_of_nat(v_stop_2468_);
v___x_2479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2465_, v_as_2466_, v___x_2477_, v___x_2478_, v___x_2469_);
return v___x_2479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object* v_snd_2480_, lean_object* v_as_2481_, lean_object* v_start_2482_, lean_object* v_stop_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2480_, v_as_2481_, v_start_2482_, v_stop_2483_);
lean_dec(v_stop_2483_);
lean_dec(v_start_2482_);
lean_dec_ref(v_as_2481_);
lean_dec(v_snd_2480_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object* v_hi_2485_, lean_object* v_pivot_2486_, lean_object* v_as_2487_, lean_object* v_i_2488_, lean_object* v_k_2489_){
_start:
{
uint8_t v___x_2490_; 
v___x_2490_ = lean_nat_dec_lt(v_k_2489_, v_hi_2485_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
lean_dec(v_k_2489_);
v___x_2491_ = lean_array_fswap(v_as_2487_, v_i_2488_, v_hi_2485_);
v___x_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2492_, 0, v_i_2488_);
lean_ctor_set(v___x_2492_, 1, v___x_2491_);
return v___x_2492_;
}
else
{
lean_object* v___x_2493_; lean_object* v_fst_2494_; lean_object* v_fst_2495_; uint8_t v___x_2496_; 
v___x_2493_ = lean_array_fget_borrowed(v_as_2487_, v_k_2489_);
v_fst_2494_ = lean_ctor_get(v___x_2493_, 0);
v_fst_2495_ = lean_ctor_get(v_pivot_2486_, 0);
v___x_2496_ = l_Lean_Name_quickLt(v_fst_2494_, v_fst_2495_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = lean_unsigned_to_nat(1u);
v___x_2498_ = lean_nat_add(v_k_2489_, v___x_2497_);
lean_dec(v_k_2489_);
v_k_2489_ = v___x_2498_;
goto _start;
}
else
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2500_ = lean_array_fswap(v_as_2487_, v_i_2488_, v_k_2489_);
v___x_2501_ = lean_unsigned_to_nat(1u);
v___x_2502_ = lean_nat_add(v_i_2488_, v___x_2501_);
lean_dec(v_i_2488_);
v___x_2503_ = lean_nat_add(v_k_2489_, v___x_2501_);
lean_dec(v_k_2489_);
v_as_2487_ = v___x_2500_;
v_i_2488_ = v___x_2502_;
v_k_2489_ = v___x_2503_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2505_, lean_object* v_pivot_2506_, lean_object* v_as_2507_, lean_object* v_i_2508_, lean_object* v_k_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2505_, v_pivot_2506_, v_as_2507_, v_i_2508_, v_k_2509_);
lean_dec_ref(v_pivot_2506_);
lean_dec(v_hi_2505_);
return v_res_2510_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object* v_a_2511_, lean_object* v_b_2512_){
_start:
{
lean_object* v_fst_2513_; lean_object* v_fst_2514_; uint8_t v___x_2515_; 
v_fst_2513_ = lean_ctor_get(v_a_2511_, 0);
v_fst_2514_ = lean_ctor_get(v_b_2512_, 0);
v___x_2515_ = l_Lean_Name_quickLt(v_fst_2513_, v_fst_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object* v_a_2516_, lean_object* v_b_2517_){
_start:
{
uint8_t v_res_2518_; lean_object* v_r_2519_; 
v_res_2518_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2516_, v_b_2517_);
lean_dec_ref(v_b_2517_);
lean_dec_ref(v_a_2516_);
v_r_2519_ = lean_box(v_res_2518_);
return v_r_2519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object* v_n_2520_, lean_object* v_as_2521_, lean_object* v_lo_2522_, lean_object* v_hi_2523_){
_start:
{
lean_object* v___y_2525_; uint8_t v___x_2535_; 
v___x_2535_ = lean_nat_dec_lt(v_lo_2522_, v_hi_2523_);
if (v___x_2535_ == 0)
{
lean_dec(v_lo_2522_);
return v_as_2521_;
}
else
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v_mid_2538_; lean_object* v___y_2540_; lean_object* v___y_2546_; lean_object* v___x_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
v___x_2536_ = lean_nat_add(v_lo_2522_, v_hi_2523_);
v___x_2537_ = lean_unsigned_to_nat(1u);
v_mid_2538_ = lean_nat_shiftr(v___x_2536_, v___x_2537_);
lean_dec(v___x_2536_);
v___x_2551_ = lean_array_fget_borrowed(v_as_2521_, v_mid_2538_);
v___x_2552_ = lean_array_fget_borrowed(v_as_2521_, v_lo_2522_);
v___x_2553_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2551_, v___x_2552_);
if (v___x_2553_ == 0)
{
v___y_2546_ = v_as_2521_;
goto v___jp_2545_;
}
else
{
lean_object* v___x_2554_; 
v___x_2554_ = lean_array_fswap(v_as_2521_, v_lo_2522_, v_mid_2538_);
v___y_2546_ = v___x_2554_;
goto v___jp_2545_;
}
v___jp_2539_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2541_ = lean_array_fget_borrowed(v___y_2540_, v_mid_2538_);
v___x_2542_ = lean_array_fget_borrowed(v___y_2540_, v_hi_2523_);
v___x_2543_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2541_, v___x_2542_);
if (v___x_2543_ == 0)
{
lean_dec(v_mid_2538_);
v___y_2525_ = v___y_2540_;
goto v___jp_2524_;
}
else
{
lean_object* v___x_2544_; 
v___x_2544_ = lean_array_fswap(v___y_2540_, v_mid_2538_, v_hi_2523_);
lean_dec(v_mid_2538_);
v___y_2525_ = v___x_2544_;
goto v___jp_2524_;
}
}
v___jp_2545_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; 
v___x_2547_ = lean_array_fget_borrowed(v___y_2546_, v_hi_2523_);
v___x_2548_ = lean_array_fget_borrowed(v___y_2546_, v_lo_2522_);
v___x_2549_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2547_, v___x_2548_);
if (v___x_2549_ == 0)
{
v___y_2540_ = v___y_2546_;
goto v___jp_2539_;
}
else
{
lean_object* v___x_2550_; 
v___x_2550_ = lean_array_fswap(v___y_2546_, v_lo_2522_, v_hi_2523_);
v___y_2540_ = v___x_2550_;
goto v___jp_2539_;
}
}
}
v___jp_2524_:
{
lean_object* v_pivot_2526_; lean_object* v___x_2527_; lean_object* v_fst_2528_; lean_object* v_snd_2529_; uint8_t v___x_2530_; 
v_pivot_2526_ = lean_array_fget(v___y_2525_, v_hi_2523_);
lean_inc_n(v_lo_2522_, 2);
v___x_2527_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2523_, v_pivot_2526_, v___y_2525_, v_lo_2522_, v_lo_2522_);
lean_dec(v_pivot_2526_);
v_fst_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_fst_2528_);
v_snd_2529_ = lean_ctor_get(v___x_2527_, 1);
lean_inc(v_snd_2529_);
lean_dec_ref(v___x_2527_);
v___x_2530_ = lean_nat_dec_le(v_hi_2523_, v_fst_2528_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2520_, v_snd_2529_, v_lo_2522_, v_fst_2528_);
v___x_2532_ = lean_unsigned_to_nat(1u);
v___x_2533_ = lean_nat_add(v_fst_2528_, v___x_2532_);
lean_dec(v_fst_2528_);
v_as_2521_ = v___x_2531_;
v_lo_2522_ = v___x_2533_;
goto _start;
}
else
{
lean_dec(v_fst_2528_);
lean_dec(v_lo_2522_);
return v_snd_2529_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object* v_n_2555_, lean_object* v_as_2556_, lean_object* v_lo_2557_, lean_object* v_hi_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2555_, v_as_2556_, v_lo_2557_, v_hi_2558_);
lean_dec(v_hi_2558_);
lean_dec(v_n_2555_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object* v_filterExport_2560_, lean_object* v_env_2561_, lean_object* v_as_2562_, size_t v_i_2563_, size_t v_stop_2564_, lean_object* v_b_2565_){
_start:
{
lean_object* v___y_2567_; uint8_t v___x_2571_; 
v___x_2571_ = lean_usize_dec_eq(v_i_2563_, v_stop_2564_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; lean_object* v_fst_2573_; lean_object* v_snd_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; 
v___x_2572_ = lean_array_uget_borrowed(v_as_2562_, v_i_2563_);
v_fst_2573_ = lean_ctor_get(v___x_2572_, 0);
v_snd_2574_ = lean_ctor_get(v___x_2572_, 1);
lean_inc_ref(v_filterExport_2560_);
lean_inc(v_snd_2574_);
lean_inc(v_fst_2573_);
lean_inc_ref(v_env_2561_);
v___x_2575_ = lean_apply_3(v_filterExport_2560_, v_env_2561_, v_fst_2573_, v_snd_2574_);
v___x_2576_ = lean_unbox(v___x_2575_);
if (v___x_2576_ == 0)
{
v___y_2567_ = v_b_2565_;
goto v___jp_2566_;
}
else
{
lean_object* v___x_2577_; 
lean_inc(v___x_2572_);
v___x_2577_ = lean_array_push(v_b_2565_, v___x_2572_);
v___y_2567_ = v___x_2577_;
goto v___jp_2566_;
}
}
else
{
lean_dec_ref(v_env_2561_);
lean_dec_ref(v_filterExport_2560_);
return v_b_2565_;
}
v___jp_2566_:
{
size_t v___x_2568_; size_t v___x_2569_; 
v___x_2568_ = ((size_t)1ULL);
v___x_2569_ = lean_usize_add(v_i_2563_, v___x_2568_);
v_i_2563_ = v___x_2569_;
v_b_2565_ = v___y_2567_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object* v_filterExport_2578_, lean_object* v_env_2579_, lean_object* v_as_2580_, lean_object* v_i_2581_, lean_object* v_stop_2582_, lean_object* v_b_2583_){
_start:
{
size_t v_i_boxed_2584_; size_t v_stop_boxed_2585_; lean_object* v_res_2586_; 
v_i_boxed_2584_ = lean_unbox_usize(v_i_2581_);
lean_dec(v_i_2581_);
v_stop_boxed_2585_ = lean_unbox_usize(v_stop_2582_);
lean_dec(v_stop_2582_);
v_res_2586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2578_, v_env_2579_, v_as_2580_, v_i_boxed_2584_, v_stop_boxed_2585_, v_b_2583_);
lean_dec_ref(v_as_2580_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object* v_filterExport_2587_, uint8_t v_preserveOrder_2588_, lean_object* v_env_2589_, lean_object* v_x_2590_){
_start:
{
lean_object* v___y_2592_; 
if (v_preserveOrder_2588_ == 0)
{
lean_object* v_snd_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v_r_2605_; lean_object* v___x_2606_; lean_object* v___y_2608_; lean_object* v___y_2609_; uint8_t v___x_2611_; 
v_snd_2602_ = lean_ctor_get(v_x_2590_, 1);
lean_inc(v_snd_2602_);
lean_dec_ref(v_x_2590_);
v___x_2603_ = lean_unsigned_to_nat(0u);
v___x_2604_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v_r_2605_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_2604_, v_snd_2602_);
lean_dec(v_snd_2602_);
v___x_2606_ = lean_array_get_size(v_r_2605_);
v___x_2611_ = lean_nat_dec_eq(v___x_2606_, v___x_2603_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___y_2615_; uint8_t v___x_2617_; 
v___x_2612_ = lean_unsigned_to_nat(1u);
v___x_2613_ = lean_nat_sub(v___x_2606_, v___x_2612_);
v___x_2617_ = lean_nat_dec_le(v___x_2603_, v___x_2613_);
if (v___x_2617_ == 0)
{
lean_inc(v___x_2613_);
v___y_2615_ = v___x_2613_;
goto v___jp_2614_;
}
else
{
v___y_2615_ = v___x_2603_;
goto v___jp_2614_;
}
v___jp_2614_:
{
uint8_t v___x_2616_; 
v___x_2616_ = lean_nat_dec_le(v___y_2615_, v___x_2613_);
if (v___x_2616_ == 0)
{
lean_dec(v___x_2613_);
lean_inc(v___y_2615_);
v___y_2608_ = v___y_2615_;
v___y_2609_ = v___y_2615_;
goto v___jp_2607_;
}
else
{
v___y_2608_ = v___y_2615_;
v___y_2609_ = v___x_2613_;
goto v___jp_2607_;
}
}
}
else
{
v___y_2592_ = v_r_2605_;
goto v___jp_2591_;
}
v___jp_2607_:
{
lean_object* v___x_2610_; 
v___x_2610_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_2606_, v_r_2605_, v___y_2608_, v___y_2609_);
lean_dec(v___y_2609_);
v___y_2592_ = v___x_2610_;
goto v___jp_2591_;
}
}
else
{
lean_object* v_fst_2618_; lean_object* v_snd_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v_fst_2618_ = lean_ctor_get(v_x_2590_, 0);
lean_inc(v_fst_2618_);
v_snd_2619_ = lean_ctor_get(v_x_2590_, 1);
lean_inc(v_snd_2619_);
lean_dec_ref(v_x_2590_);
v___x_2620_ = lean_array_mk(v_fst_2618_);
v___x_2621_ = l_Array_reverse___redArg(v___x_2620_);
v___x_2622_ = lean_unsigned_to_nat(0u);
v___x_2623_ = lean_array_get_size(v___x_2621_);
v___x_2624_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2619_, v___x_2621_, v___x_2622_, v___x_2623_);
lean_dec_ref(v___x_2621_);
lean_dec(v_snd_2619_);
v___y_2592_ = v___x_2624_;
goto v___jp_2591_;
}
v___jp_2591_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; uint8_t v___x_2596_; 
v___x_2593_ = lean_unsigned_to_nat(0u);
v___x_2594_ = lean_array_get_size(v___y_2592_);
v___x_2595_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2596_ = lean_nat_dec_lt(v___x_2593_, v___x_2594_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; 
lean_dec_ref(v_env_2589_);
lean_dec_ref(v_filterExport_2587_);
v___x_2597_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2595_);
lean_ctor_set(v___x_2597_, 1, v___x_2595_);
lean_ctor_set(v___x_2597_, 2, v___y_2592_);
return v___x_2597_;
}
else
{
size_t v___x_2598_; size_t v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2598_ = ((size_t)0ULL);
v___x_2599_ = lean_usize_of_nat(v___x_2594_);
v___x_2600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2587_, v_env_2589_, v___y_2592_, v___x_2598_, v___x_2599_, v___x_2595_);
lean_inc_ref(v___x_2600_);
v___x_2601_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
lean_ctor_set(v___x_2601_, 2, v___y_2592_);
return v___x_2601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object* v_filterExport_2625_, lean_object* v_preserveOrder_2626_, lean_object* v_env_2627_, lean_object* v_x_2628_){
_start:
{
uint8_t v_preserveOrder_boxed_2629_; lean_object* v_res_2630_; 
v_preserveOrder_boxed_2629_ = lean_unbox(v_preserveOrder_2626_);
v_res_2630_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2625_, v_preserveOrder_boxed_2629_, v_env_2627_, v_x_2628_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object* v_x_2640_){
_start:
{
lean_object* v_snd_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2655_; 
v_snd_2641_ = lean_ctor_get(v_x_2640_, 1);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_x_2640_);
if (v_isSharedCheck_2655_ == 0)
{
lean_object* v_unused_2656_; 
v_unused_2656_ = lean_ctor_get(v_x_2640_, 0);
lean_dec(v_unused_2656_);
v___x_2643_ = v_x_2640_;
v_isShared_2644_ = v_isSharedCheck_2655_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_snd_2641_);
lean_dec(v_x_2640_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2655_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2645_; lean_object* v___y_2647_; 
v___x_2645_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2641_) == 0)
{
lean_object* v_size_2653_; 
v_size_2653_ = lean_ctor_get(v_snd_2641_, 0);
lean_inc(v_size_2653_);
lean_dec_ref_known(v_snd_2641_, 5);
v___y_2647_ = v_size_2653_;
goto v___jp_2646_;
}
else
{
lean_object* v___x_2654_; 
v___x_2654_ = lean_unsigned_to_nat(0u);
v___y_2647_ = v___x_2654_;
goto v___jp_2646_;
}
v___jp_2646_:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2648_ = l_Nat_reprFast(v___y_2647_);
v___x_2649_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2648_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set_tag(v___x_2643_, 5);
lean_ctor_set(v___x_2643_, 1, v___x_2649_);
lean_ctor_set(v___x_2643_, 0, v___x_2645_);
v___x_2651_ = v___x_2643_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object* v_x_2657_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object* v_x_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Lean_registerParametricAttributeExt___redArg___lam__3(v_x_2659_);
lean_dec_ref(v_x_2659_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object* v___x_2661_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2661_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object* v___x_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2664_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object* v___x_2667_, lean_object* v_x_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2667_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object* v___x_2672_, lean_object* v_x_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2672_, v_x_2673_, v___y_2674_);
lean_dec_ref(v___y_2674_);
lean_dec_ref(v_x_2673_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object* v_ref_2687_, uint8_t v_preserveOrder_2688_, lean_object* v_filterExport_2689_, uint8_t v_logWrites_2690_){
_start:
{
lean_object* v___f_2692_; lean_object* v___x_2693_; lean_object* v___f_2694_; lean_object* v___f_2695_; lean_object* v___f_2696_; lean_object* v___f_2697_; lean_object* v___f_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___f_2692_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__0));
v___x_2693_ = lean_box(v_preserveOrder_2688_);
v___f_2694_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2694_, 0, v_filterExport_2689_);
lean_closure_set(v___f_2694_, 1, v___x_2693_);
v___f_2695_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__1));
v___f_2696_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__2));
v___f_2697_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__4));
v___f_2698_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__5));
v___x_2699_ = lean_box(2);
v___x_2700_ = lean_box(0);
v___x_2701_ = 0;
v___x_2702_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2702_, 0, v_ref_2687_);
lean_ctor_set(v___x_2702_, 1, v___f_2697_);
lean_ctor_set(v___x_2702_, 2, v___f_2698_);
lean_ctor_set(v___x_2702_, 3, v___f_2692_);
lean_ctor_set(v___x_2702_, 4, v___f_2694_);
lean_ctor_set(v___x_2702_, 5, v___f_2695_);
lean_ctor_set(v___x_2702_, 6, v___x_2699_);
lean_ctor_set(v___x_2702_, 7, v___x_2700_);
lean_ctor_set_uint8(v___x_2702_, sizeof(void*)*8, v___x_2701_);
lean_ctor_set_uint8(v___x_2702_, sizeof(void*)*8 + 1, v_logWrites_2690_);
v___x_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
lean_ctor_set(v___x_2703_, 1, v___f_2696_);
v___x_2704_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2703_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object* v_ref_2705_, lean_object* v_preserveOrder_2706_, lean_object* v_filterExport_2707_, lean_object* v_logWrites_2708_, lean_object* v_a_2709_){
_start:
{
uint8_t v_preserveOrder_boxed_2710_; uint8_t v_logWrites_boxed_2711_; lean_object* v_res_2712_; 
v_preserveOrder_boxed_2710_ = lean_unbox(v_preserveOrder_2706_);
v_logWrites_boxed_2711_ = lean_unbox(v_logWrites_2708_);
v_res_2712_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2705_, v_preserveOrder_boxed_2710_, v_filterExport_2707_, v_logWrites_boxed_2711_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object* v_00_u03b1_2713_, lean_object* v_ref_2714_, uint8_t v_preserveOrder_2715_, lean_object* v_filterExport_2716_, uint8_t v_logWrites_2717_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2714_, v_preserveOrder_2715_, v_filterExport_2716_, v_logWrites_2717_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object* v_00_u03b1_2720_, lean_object* v_ref_2721_, lean_object* v_preserveOrder_2722_, lean_object* v_filterExport_2723_, lean_object* v_logWrites_2724_, lean_object* v_a_2725_){
_start:
{
uint8_t v_preserveOrder_boxed_2726_; uint8_t v_logWrites_boxed_2727_; lean_object* v_res_2728_; 
v_preserveOrder_boxed_2726_ = lean_unbox(v_preserveOrder_2722_);
v_logWrites_boxed_2727_ = lean_unbox(v_logWrites_2724_);
v_res_2728_ = l_Lean_registerParametricAttributeExt(v_00_u03b1_2720_, v_ref_2721_, v_preserveOrder_boxed_2726_, v_filterExport_2723_, v_logWrites_boxed_2727_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object* v_00_u03b1_2729_, lean_object* v_filterExport_2730_, lean_object* v_env_2731_, lean_object* v_as_2732_, size_t v_i_2733_, size_t v_stop_2734_, lean_object* v_b_2735_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2730_, v_env_2731_, v_as_2732_, v_i_2733_, v_stop_2734_, v_b_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object* v_00_u03b1_2737_, lean_object* v_filterExport_2738_, lean_object* v_env_2739_, lean_object* v_as_2740_, lean_object* v_i_2741_, lean_object* v_stop_2742_, lean_object* v_b_2743_){
_start:
{
size_t v_i_boxed_2744_; size_t v_stop_boxed_2745_; lean_object* v_res_2746_; 
v_i_boxed_2744_ = lean_unbox_usize(v_i_2741_);
lean_dec(v_i_2741_);
v_stop_boxed_2745_ = lean_unbox_usize(v_stop_2742_);
lean_dec(v_stop_2742_);
v_res_2746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(v_00_u03b1_2737_, v_filterExport_2738_, v_env_2739_, v_as_2740_, v_i_boxed_2744_, v_stop_boxed_2745_, v_b_2743_);
lean_dec_ref(v_as_2740_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object* v_init_2747_, lean_object* v_t_2748_){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2747_, v_t_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object* v_init_2750_, lean_object* v_t_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(v_init_2750_, v_t_2751_);
lean_dec(v_t_2751_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object* v_00_u03b1_2753_, lean_object* v_init_2754_, lean_object* v_t_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2754_, v_t_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object* v_00_u03b1_2757_, lean_object* v_init_2758_, lean_object* v_t_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(v_00_u03b1_2757_, v_init_2758_, v_t_2759_);
lean_dec(v_t_2759_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object* v_00_u03b1_2761_, lean_object* v_n_2762_, lean_object* v_as_2763_, lean_object* v_lo_2764_, lean_object* v_hi_2765_, lean_object* v_w_2766_, lean_object* v_hlo_2767_, lean_object* v_hhi_2768_){
_start:
{
lean_object* v___x_2769_; 
v___x_2769_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2762_, v_as_2763_, v_lo_2764_, v_hi_2765_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object* v_00_u03b1_2770_, lean_object* v_n_2771_, lean_object* v_as_2772_, lean_object* v_lo_2773_, lean_object* v_hi_2774_, lean_object* v_w_2775_, lean_object* v_hlo_2776_, lean_object* v_hhi_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(v_00_u03b1_2770_, v_n_2771_, v_as_2772_, v_lo_2773_, v_hi_2774_, v_w_2775_, v_hlo_2776_, v_hhi_2777_);
lean_dec(v_hi_2774_);
lean_dec(v_n_2771_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object* v_00_u03b1_2779_, lean_object* v_snd_2780_, lean_object* v_as_2781_, lean_object* v_start_2782_, lean_object* v_stop_2783_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2780_, v_as_2781_, v_start_2782_, v_stop_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object* v_00_u03b1_2785_, lean_object* v_snd_2786_, lean_object* v_as_2787_, lean_object* v_start_2788_, lean_object* v_stop_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(v_00_u03b1_2785_, v_snd_2786_, v_as_2787_, v_start_2788_, v_stop_2789_);
lean_dec(v_stop_2789_);
lean_dec(v_start_2788_);
lean_dec_ref(v_as_2787_);
lean_dec(v_snd_2786_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object* v_00_u03b1_2791_, lean_object* v_init_2792_, lean_object* v_x_2793_){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2792_, v_x_2793_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2795_, lean_object* v_init_2796_, lean_object* v_x_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(v_00_u03b1_2795_, v_init_2796_, v_x_2797_);
lean_dec(v_x_2797_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object* v_00_u03b1_2799_, lean_object* v_n_2800_, lean_object* v_lo_2801_, lean_object* v_hi_2802_, lean_object* v_hhi_2803_, lean_object* v_pivot_2804_, lean_object* v_as_2805_, lean_object* v_i_2806_, lean_object* v_k_2807_, lean_object* v_ilo_2808_, lean_object* v_ik_2809_, lean_object* v_w_2810_){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2802_, v_pivot_2804_, v_as_2805_, v_i_2806_, v_k_2807_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2812_, lean_object* v_n_2813_, lean_object* v_lo_2814_, lean_object* v_hi_2815_, lean_object* v_hhi_2816_, lean_object* v_pivot_2817_, lean_object* v_as_2818_, lean_object* v_i_2819_, lean_object* v_k_2820_, lean_object* v_ilo_2821_, lean_object* v_ik_2822_, lean_object* v_w_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(v_00_u03b1_2812_, v_n_2813_, v_lo_2814_, v_hi_2815_, v_hhi_2816_, v_pivot_2817_, v_as_2818_, v_i_2819_, v_k_2820_, v_ilo_2821_, v_ik_2822_, v_w_2823_);
lean_dec_ref(v_pivot_2817_);
lean_dec(v_hi_2815_);
lean_dec(v_lo_2814_);
lean_dec(v_n_2813_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object* v_00_u03b1_2825_, lean_object* v_snd_2826_, lean_object* v_as_2827_, size_t v_i_2828_, size_t v_stop_2829_, lean_object* v_b_2830_){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2826_, v_as_2827_, v_i_2828_, v_stop_2829_, v_b_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2832_, lean_object* v_snd_2833_, lean_object* v_as_2834_, lean_object* v_i_2835_, lean_object* v_stop_2836_, lean_object* v_b_2837_){
_start:
{
size_t v_i_boxed_2838_; size_t v_stop_boxed_2839_; lean_object* v_res_2840_; 
v_i_boxed_2838_ = lean_unbox_usize(v_i_2835_);
lean_dec(v_i_2835_);
v_stop_boxed_2839_ = lean_unbox_usize(v_stop_2836_);
lean_dec(v_stop_2836_);
v_res_2840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(v_00_u03b1_2832_, v_snd_2833_, v_as_2834_, v_i_boxed_2838_, v_stop_boxed_2839_, v_b_2837_);
lean_dec_ref(v_as_2834_);
lean_dec(v_snd_2833_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object* v_env_2841_, lean_object* v___y_2842_){
_start:
{
lean_object* v___x_2844_; lean_object* v_nextMacroScope_2845_; lean_object* v_ngen_2846_; lean_object* v_auxDeclNGen_2847_; lean_object* v_traceState_2848_; lean_object* v_recordedDeps_2849_; lean_object* v_messages_2850_; lean_object* v_infoState_2851_; lean_object* v_snapshotTasks_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2863_; 
v___x_2844_ = lean_st_ref_take(v___y_2842_);
v_nextMacroScope_2845_ = lean_ctor_get(v___x_2844_, 1);
v_ngen_2846_ = lean_ctor_get(v___x_2844_, 2);
v_auxDeclNGen_2847_ = lean_ctor_get(v___x_2844_, 3);
v_traceState_2848_ = lean_ctor_get(v___x_2844_, 4);
v_recordedDeps_2849_ = lean_ctor_get(v___x_2844_, 6);
v_messages_2850_ = lean_ctor_get(v___x_2844_, 7);
v_infoState_2851_ = lean_ctor_get(v___x_2844_, 8);
v_snapshotTasks_2852_ = lean_ctor_get(v___x_2844_, 9);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2863_ == 0)
{
lean_object* v_unused_2864_; lean_object* v_unused_2865_; 
v_unused_2864_ = lean_ctor_get(v___x_2844_, 5);
lean_dec(v_unused_2864_);
v_unused_2865_ = lean_ctor_get(v___x_2844_, 0);
lean_dec(v_unused_2865_);
v___x_2854_ = v___x_2844_;
v_isShared_2855_ = v_isSharedCheck_2863_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_snapshotTasks_2852_);
lean_inc(v_infoState_2851_);
lean_inc(v_messages_2850_);
lean_inc(v_recordedDeps_2849_);
lean_inc(v_traceState_2848_);
lean_inc(v_auxDeclNGen_2847_);
lean_inc(v_ngen_2846_);
lean_inc(v_nextMacroScope_2845_);
lean_dec(v___x_2844_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2863_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2856_ = lean_box(0);
v___x_2857_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 5, v___x_2857_);
lean_ctor_set(v___x_2854_, 0, v_env_2841_);
v___x_2859_ = v___x_2854_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_env_2841_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v_nextMacroScope_2845_);
lean_ctor_set(v_reuseFailAlloc_2862_, 2, v_ngen_2846_);
lean_ctor_set(v_reuseFailAlloc_2862_, 3, v_auxDeclNGen_2847_);
lean_ctor_set(v_reuseFailAlloc_2862_, 4, v_traceState_2848_);
lean_ctor_set(v_reuseFailAlloc_2862_, 5, v___x_2857_);
lean_ctor_set(v_reuseFailAlloc_2862_, 6, v_recordedDeps_2849_);
lean_ctor_set(v_reuseFailAlloc_2862_, 7, v_messages_2850_);
lean_ctor_set(v_reuseFailAlloc_2862_, 8, v_infoState_2851_);
lean_ctor_set(v_reuseFailAlloc_2862_, 9, v_snapshotTasks_2852_);
v___x_2859_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_st_ref_put(v___y_2842_, v___x_2859_);
v___x_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2856_);
return v___x_2861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object* v_env_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2866_, v___y_2867_);
lean_dec(v___y_2867_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object* v_env_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v___x_2874_; 
v___x_2874_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2870_, v___y_2872_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object* v_env_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(v_env_2875_, v___y_2876_, v___y_2877_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object* v_addEntryFn_2880_, lean_object* v___x_2881_, lean_object* v_s_2882_){
_start:
{
lean_object* v_importedEntries_2883_; lean_object* v_state_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2892_; 
v_importedEntries_2883_ = lean_ctor_get(v_s_2882_, 0);
v_state_2884_ = lean_ctor_get(v_s_2882_, 1);
v_isSharedCheck_2892_ = !lean_is_exclusive(v_s_2882_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2886_ = v_s_2882_;
v_isShared_2887_ = v_isSharedCheck_2892_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_state_2884_);
lean_inc(v_importedEntries_2883_);
lean_dec(v_s_2882_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2892_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v_state_2888_; lean_object* v___x_2890_; 
v_state_2888_ = lean_apply_2(v_addEntryFn_2880_, v_state_2884_, v___x_2881_);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 1, v_state_2888_);
v___x_2890_ = v___x_2886_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_importedEntries_2883_);
lean_ctor_set(v_reuseFailAlloc_2891_, 1, v_state_2888_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object* v_afterSet_2893_, lean_object* v_getParam_2894_, lean_object* v_ext_2895_, lean_object* v_toAttributeImplCore_2896_, lean_object* v_decl_2897_, lean_object* v_stx_2898_, uint8_t v_kind_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v_nextMacroScope_2904_; lean_object* v_ngen_2905_; lean_object* v_auxDeclNGen_2906_; lean_object* v_traceState_2907_; lean_object* v_recordedDeps_2908_; lean_object* v_messages_2909_; lean_object* v_infoState_2910_; lean_object* v_snapshotTasks_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; uint8_t v___x_2965_; uint8_t v___x_2966_; 
v___x_2965_ = 0;
v___x_2966_ = l_Lean_instBEqAttributeKind_beq(v_kind_2899_, v___x_2965_);
if (v___x_2966_ == 0)
{
lean_object* v_name_2967_; lean_object* v___x_2968_; 
lean_dec(v_stx_2898_);
lean_dec(v_decl_2897_);
lean_dec_ref(v_ext_2895_);
lean_dec_ref(v_getParam_2894_);
lean_dec_ref(v_afterSet_2893_);
v_name_2967_ = lean_ctor_get(v_toAttributeImplCore_2896_, 1);
lean_inc(v_name_2967_);
lean_dec_ref(v_toAttributeImplCore_2896_);
v___x_2968_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2967_, v_kind_2899_, v___y_2900_, v___y_2901_);
return v___x_2968_;
}
else
{
goto v___jp_2959_;
}
v___jp_2903_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2917_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_2918_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2918_, 0, v___y_2916_);
lean_ctor_set(v___x_2918_, 1, v_nextMacroScope_2904_);
lean_ctor_set(v___x_2918_, 2, v_ngen_2905_);
lean_ctor_set(v___x_2918_, 3, v_auxDeclNGen_2906_);
lean_ctor_set(v___x_2918_, 4, v_traceState_2907_);
lean_ctor_set(v___x_2918_, 5, v___x_2917_);
lean_ctor_set(v___x_2918_, 6, v_recordedDeps_2908_);
lean_ctor_set(v___x_2918_, 7, v_messages_2909_);
lean_ctor_set(v___x_2918_, 8, v_infoState_2910_);
lean_ctor_set(v___x_2918_, 9, v_snapshotTasks_2911_);
v___x_2919_ = lean_st_ref_put(v___y_2913_, v___x_2918_);
lean_inc(v___y_2913_);
lean_inc_ref(v___y_2914_);
v___x_2920_ = lean_apply_5(v_afterSet_2893_, v_decl_2897_, v___y_2912_, v___y_2914_, v___y_2913_, lean_box(0));
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_dec_ref(v___y_2915_);
return v___x_2920_;
}
else
{
lean_object* v_a_2921_; uint8_t v___x_2922_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
v___x_2922_ = l_Lean_Exception_isInterrupt(v_a_2921_);
if (v___x_2922_ == 0)
{
uint8_t v___x_2923_; 
v___x_2923_ = l_Lean_Exception_isRuntime(v_a_2921_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; 
lean_dec_ref_known(v___x_2920_, 1);
v___x_2924_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v___y_2915_, v___y_2913_);
return v___x_2924_;
}
else
{
lean_dec_ref(v___y_2915_);
return v___x_2920_;
}
}
else
{
lean_dec(v_a_2921_);
lean_dec_ref(v___y_2915_);
return v___x_2920_;
}
}
}
v___jp_2925_:
{
lean_object* v___x_2929_; 
lean_inc(v___y_2928_);
lean_inc_ref(v___y_2927_);
lean_inc(v_decl_2897_);
v___x_2929_ = lean_apply_5(v_getParam_2894_, v_decl_2897_, v_stx_2898_, v___y_2927_, v___y_2928_, lean_box(0));
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v___x_2931_; lean_object* v_toEnvExtension_2932_; lean_object* v_env_2933_; lean_object* v_nextMacroScope_2934_; lean_object* v_ngen_2935_; lean_object* v_auxDeclNGen_2936_; lean_object* v_traceState_2937_; lean_object* v_recordedDeps_2938_; lean_object* v_messages_2939_; lean_object* v_infoState_2940_; lean_object* v_snapshotTasks_2941_; lean_object* v_addEntryFn_2942_; lean_object* v_asyncMode_2943_; uint8_t v_logWrites_2944_; lean_object* v___x_2945_; lean_object* v___f_2946_; uint8_t v___x_2947_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc_n(v_a_2930_, 2);
lean_dec_ref_known(v___x_2929_, 1);
v___x_2931_ = lean_st_ref_take(v___y_2928_);
v_toEnvExtension_2932_ = lean_ctor_get(v_ext_2895_, 0);
lean_inc_ref(v_toEnvExtension_2932_);
v_env_2933_ = lean_ctor_get(v___x_2931_, 0);
lean_inc_ref(v_env_2933_);
v_nextMacroScope_2934_ = lean_ctor_get(v___x_2931_, 1);
lean_inc(v_nextMacroScope_2934_);
v_ngen_2935_ = lean_ctor_get(v___x_2931_, 2);
lean_inc_ref(v_ngen_2935_);
v_auxDeclNGen_2936_ = lean_ctor_get(v___x_2931_, 3);
lean_inc_ref(v_auxDeclNGen_2936_);
v_traceState_2937_ = lean_ctor_get(v___x_2931_, 4);
lean_inc_ref(v_traceState_2937_);
v_recordedDeps_2938_ = lean_ctor_get(v___x_2931_, 6);
lean_inc_ref(v_recordedDeps_2938_);
v_messages_2939_ = lean_ctor_get(v___x_2931_, 7);
lean_inc_ref(v_messages_2939_);
v_infoState_2940_ = lean_ctor_get(v___x_2931_, 8);
lean_inc_ref(v_infoState_2940_);
v_snapshotTasks_2941_ = lean_ctor_get(v___x_2931_, 9);
lean_inc_ref(v_snapshotTasks_2941_);
lean_dec(v___x_2931_);
v_addEntryFn_2942_ = lean_ctor_get(v_ext_2895_, 3);
lean_inc(v_addEntryFn_2942_);
lean_dec_ref(v_ext_2895_);
v_asyncMode_2943_ = lean_ctor_get(v_toEnvExtension_2932_, 2);
lean_inc(v_asyncMode_2943_);
v_logWrites_2944_ = lean_ctor_get_uint8(v_toEnvExtension_2932_, sizeof(void*)*6);
lean_inc(v_decl_2897_);
v___x_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2945_, 0, v_decl_2897_);
lean_ctor_set(v___x_2945_, 1, v_a_2930_);
v___f_2946_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2946_, 0, v_addEntryFn_2942_);
lean_closure_set(v___f_2946_, 1, v___x_2945_);
v___x_2947_ = 1;
if (v_logWrites_2944_ == 0)
{
lean_object* v___x_2948_; 
lean_inc(v_decl_2897_);
v___x_2948_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2932_, v_env_2933_, v___f_2946_, v_asyncMode_2943_, v_decl_2897_, v___x_2947_);
lean_dec(v_asyncMode_2943_);
v_nextMacroScope_2904_ = v_nextMacroScope_2934_;
v_ngen_2905_ = v_ngen_2935_;
v_auxDeclNGen_2906_ = v_auxDeclNGen_2936_;
v_traceState_2907_ = v_traceState_2937_;
v_recordedDeps_2908_ = v_recordedDeps_2938_;
v_messages_2909_ = v_messages_2939_;
v_infoState_2910_ = v_infoState_2940_;
v_snapshotTasks_2911_ = v_snapshotTasks_2941_;
v___y_2912_ = v_a_2930_;
v___y_2913_ = v___y_2928_;
v___y_2914_ = v___y_2927_;
v___y_2915_ = v___y_2926_;
v___y_2916_ = v___x_2948_;
goto v___jp_2903_;
}
else
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
lean_inc_n(v_decl_2897_, 2);
v___x_2949_ = l_Lean_Environment_logDeclChange(v_env_2933_, v_decl_2897_);
v___x_2950_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2932_, v___x_2949_, v___f_2946_, v_asyncMode_2943_, v_decl_2897_, v___x_2947_);
lean_dec(v_asyncMode_2943_);
v_nextMacroScope_2904_ = v_nextMacroScope_2934_;
v_ngen_2905_ = v_ngen_2935_;
v_auxDeclNGen_2906_ = v_auxDeclNGen_2936_;
v_traceState_2907_ = v_traceState_2937_;
v_recordedDeps_2908_ = v_recordedDeps_2938_;
v_messages_2909_ = v_messages_2939_;
v_infoState_2910_ = v_infoState_2940_;
v_snapshotTasks_2911_ = v_snapshotTasks_2941_;
v___y_2912_ = v_a_2930_;
v___y_2913_ = v___y_2928_;
v___y_2914_ = v___y_2927_;
v___y_2915_ = v___y_2926_;
v___y_2916_ = v___x_2950_;
goto v___jp_2903_;
}
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
lean_dec_ref(v___y_2926_);
lean_dec(v_decl_2897_);
lean_dec_ref(v_ext_2895_);
lean_dec_ref(v_afterSet_2893_);
v_a_2951_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2929_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2929_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
v___jp_2959_:
{
lean_object* v___x_2960_; lean_object* v_env_2961_; lean_object* v___x_2962_; 
v___x_2960_ = lean_st_ref_get(v___y_2901_);
v_env_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc_ref(v_env_2961_);
lean_dec(v___x_2960_);
v___x_2962_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2961_, v_decl_2897_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_dec_ref(v_toAttributeImplCore_2896_);
v___y_2926_ = v_env_2961_;
v___y_2927_ = v___y_2900_;
v___y_2928_ = v___y_2901_;
goto v___jp_2925_;
}
else
{
lean_object* v_name_2963_; lean_object* v___x_2964_; 
lean_dec_ref_known(v___x_2962_, 1);
lean_dec_ref(v_env_2961_);
lean_dec(v_stx_2898_);
lean_dec_ref(v_ext_2895_);
lean_dec_ref(v_getParam_2894_);
lean_dec_ref(v_afterSet_2893_);
v_name_2963_ = lean_ctor_get(v_toAttributeImplCore_2896_, 1);
lean_inc(v_name_2963_);
lean_dec_ref(v_toAttributeImplCore_2896_);
v___x_2964_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2963_, v_decl_2897_, v___y_2900_, v___y_2901_);
return v___x_2964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object* v_afterSet_2969_, lean_object* v_getParam_2970_, lean_object* v_ext_2971_, lean_object* v_toAttributeImplCore_2972_, lean_object* v_decl_2973_, lean_object* v_stx_2974_, lean_object* v_kind_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
uint8_t v_kind_boxed_2979_; lean_object* v_res_2980_; 
v_kind_boxed_2979_ = lean_unbox(v_kind_2975_);
v_res_2980_ = l_Lean_registerParametricAttributeForExt___redArg___lam__1(v_afterSet_2969_, v_getParam_2970_, v_ext_2971_, v_toAttributeImplCore_2972_, v_decl_2973_, v_stx_2974_, v_kind_boxed_2979_, v___y_2976_, v___y_2977_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__2(lean_object* v_toAttributeImplCore_2981_, lean_object* v_decl_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
lean_object* v_name_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v_name_2986_ = lean_ctor_get(v_toAttributeImplCore_2981_, 1);
lean_inc(v_name_2986_);
lean_dec_ref(v_toAttributeImplCore_2981_);
v___x_2987_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_2988_ = l_Lean_MessageData_ofName(v_name_2986_);
v___x_2989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2987_);
lean_ctor_set(v___x_2989_, 1, v___x_2988_);
v___x_2990_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_2991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2989_);
lean_ctor_set(v___x_2991_, 1, v___x_2990_);
v___x_2992_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2991_, v___y_2983_, v___y_2984_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__2___boxed(lean_object* v_toAttributeImplCore_2993_, lean_object* v_decl_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_Lean_registerParametricAttributeForExt___redArg___lam__2(v_toAttributeImplCore_2993_, v_decl_2994_, v___y_2995_, v___y_2996_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v_decl_2994_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object* v_impl_2999_, lean_object* v_ext_3000_){
_start:
{
lean_object* v_toAttributeImplCore_3002_; lean_object* v_getParam_3003_; lean_object* v_afterSet_3004_; uint8_t v_preserveOrder_3005_; lean_object* v___f_3006_; lean_object* v___f_3007_; lean_object* v_attrImpl_3008_; lean_object* v___x_3009_; 
v_toAttributeImplCore_3002_ = lean_ctor_get(v_impl_2999_, 0);
lean_inc_ref_n(v_toAttributeImplCore_3002_, 3);
v_getParam_3003_ = lean_ctor_get(v_impl_2999_, 1);
lean_inc_ref(v_getParam_3003_);
v_afterSet_3004_ = lean_ctor_get(v_impl_2999_, 2);
lean_inc_ref(v_afterSet_3004_);
v_preserveOrder_3005_ = lean_ctor_get_uint8(v_impl_2999_, sizeof(void*)*4);
lean_dec_ref(v_impl_2999_);
lean_inc_ref(v_ext_3000_);
v___f_3006_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3006_, 0, v_afterSet_3004_);
lean_closure_set(v___f_3006_, 1, v_getParam_3003_);
lean_closure_set(v___f_3006_, 2, v_ext_3000_);
lean_closure_set(v___f_3006_, 3, v_toAttributeImplCore_3002_);
v___f_3007_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__2___boxed), 5, 1);
lean_closure_set(v___f_3007_, 0, v_toAttributeImplCore_3002_);
v_attrImpl_3008_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_attrImpl_3008_, 0, v_toAttributeImplCore_3002_);
lean_ctor_set(v_attrImpl_3008_, 1, v___f_3006_);
lean_ctor_set(v_attrImpl_3008_, 2, v___f_3007_);
lean_inc_ref(v_attrImpl_3008_);
v___x_3009_ = l_Lean_registerBuiltinAttribute(v_attrImpl_3008_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3017_; 
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3017_ == 0)
{
lean_object* v_unused_3018_; 
v_unused_3018_ = lean_ctor_get(v___x_3009_, 0);
lean_dec(v_unused_3018_);
v___x_3011_ = v___x_3009_;
v_isShared_3012_ = v_isSharedCheck_3017_;
goto v_resetjp_3010_;
}
else
{
lean_dec(v___x_3009_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3017_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3013_; lean_object* v___x_3015_; 
v___x_3013_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3013_, 0, v_attrImpl_3008_);
lean_ctor_set(v___x_3013_, 1, v_ext_3000_);
lean_ctor_set_uint8(v___x_3013_, sizeof(void*)*2, v_preserveOrder_3005_);
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 0, v___x_3013_);
v___x_3015_ = v___x_3011_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3013_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec_ref_known(v_attrImpl_3008_, 3);
lean_dec_ref(v_ext_3000_);
v_a_3019_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3009_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3009_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object* v_impl_3027_, lean_object* v_ext_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3027_, v_ext_3028_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object* v_00_u03b1_3031_, lean_object* v_impl_3032_, lean_object* v_ext_3033_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3032_, v_ext_3033_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object* v_00_u03b1_3036_, lean_object* v_impl_3037_, lean_object* v_ext_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_Lean_registerParametricAttributeForExt(v_00_u03b1_3036_, v_impl_3037_, v_ext_3038_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_3041_){
_start:
{
lean_object* v_toAttributeImplCore_3043_; uint8_t v_preserveOrder_3044_; lean_object* v_filterExport_3045_; lean_object* v_ref_3046_; uint8_t v___x_3047_; lean_object* v___x_3048_; 
v_toAttributeImplCore_3043_ = lean_ctor_get(v_impl_3041_, 0);
v_preserveOrder_3044_ = lean_ctor_get_uint8(v_impl_3041_, sizeof(void*)*4);
v_filterExport_3045_ = lean_ctor_get(v_impl_3041_, 3);
v_ref_3046_ = lean_ctor_get(v_toAttributeImplCore_3043_, 0);
v___x_3047_ = 0;
lean_inc_ref(v_filterExport_3045_);
lean_inc(v_ref_3046_);
v___x_3048_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_3046_, v_preserveOrder_3044_, v_filterExport_3045_, v___x_3047_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3050_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3048_, 1);
v___x_3050_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3041_, v_a_3049_);
return v___x_3050_;
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_dec_ref(v_impl_3041_);
v_a_3051_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3048_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3048_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_3059_, lean_object* v_a_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_Lean_registerParametricAttribute___redArg(v_impl_3059_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_3062_, lean_object* v_impl_3063_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Lean_registerParametricAttribute___redArg(v_impl_3063_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_3066_, lean_object* v_impl_3067_, lean_object* v_a_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l_Lean_registerParametricAttribute(v_00_u03b1_3066_, v_impl_3067_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object* v_inst_3075_, lean_object* v_ext_3076_, uint8_t v_preserveOrder_3077_, lean_object* v_env_3078_, lean_object* v_decl_3079_){
_start:
{
lean_object* v___y_3081_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3093_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3078_, v_decl_3079_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_toEnvExtension_3094_; lean_object* v_asyncMode_3095_; lean_object* v___x_3096_; uint8_t v___x_3097_; lean_object* v___x_3098_; lean_object* v_snd_3099_; lean_object* v___x_3100_; 
lean_dec(v_inst_3075_);
v_toEnvExtension_3094_ = lean_ctor_get(v_ext_3076_, 0);
v_asyncMode_3095_ = lean_ctor_get(v_toEnvExtension_3094_, 2);
v___x_3096_ = lean_box(0);
v___x_3097_ = 0;
v___x_3098_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3092_, v_ext_3076_, v_env_3078_, v_asyncMode_3095_, v___x_3096_, v___x_3097_);
v_snd_3099_ = lean_ctor_get(v___x_3098_, 1);
lean_inc(v_snd_3099_);
lean_dec(v___x_3098_);
v___x_3100_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3099_, v_decl_3079_);
lean_dec(v_decl_3079_);
lean_dec(v_snd_3099_);
return v___x_3100_;
}
else
{
if (v_preserveOrder_3077_ == 0)
{
lean_object* v_val_3101_; uint8_t v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; 
v_val_3101_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_val_3101_);
lean_dec_ref_known(v___x_3093_, 1);
v___x_3102_ = 0;
v___x_3103_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3092_, v_ext_3076_, v_env_3078_, v_val_3101_, v___x_3102_);
lean_dec(v_val_3101_);
lean_dec_ref(v_env_3078_);
v___x_3104_ = lean_unsigned_to_nat(0u);
v___x_3105_ = lean_array_get_size(v___x_3103_);
v___x_3106_ = lean_nat_dec_lt(v___x_3104_, v___x_3105_);
if (v___x_3106_ == 0)
{
lean_object* v___x_3107_; 
lean_dec_ref(v___x_3103_);
lean_dec(v_decl_3079_);
lean_dec(v_inst_3075_);
v___x_3107_ = lean_box(0);
return v___x_3107_;
}
else
{
lean_object* v___x_3108_; lean_object* v___x_3109_; uint8_t v___x_3110_; 
v___x_3108_ = lean_unsigned_to_nat(1u);
v___x_3109_ = lean_nat_sub(v___x_3105_, v___x_3108_);
v___x_3110_ = lean_nat_dec_le(v___x_3104_, v___x_3109_);
if (v___x_3110_ == 0)
{
lean_object* v___x_3111_; 
lean_dec(v___x_3109_);
lean_dec_ref(v___x_3103_);
lean_dec(v_decl_3079_);
lean_dec(v_inst_3075_);
v___x_3111_ = lean_box(0);
return v___x_3111_;
}
else
{
lean_object* v___f_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___f_3112_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
v___x_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3113_, 0, v_decl_3079_);
lean_ctor_set(v___x_3113_, 1, v_inst_3075_);
v___x_3114_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3115_ = l_Array_binSearchAux___redArg(v___f_3112_, v___x_3114_, v___x_3103_, v___x_3113_, v___x_3104_, v___x_3109_);
lean_dec_ref(v___x_3103_);
v___y_3081_ = v___x_3115_;
goto v___jp_3080_;
}
}
}
else
{
lean_object* v_val_3116_; uint8_t v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
lean_dec(v_inst_3075_);
v_val_3116_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_val_3116_);
lean_dec_ref_known(v___x_3093_, 1);
v___x_3117_ = 0;
v___x_3118_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3092_, v_ext_3076_, v_env_3078_, v_val_3116_, v___x_3117_);
lean_dec(v_val_3116_);
lean_dec_ref(v_env_3078_);
v___x_3119_ = l_Lean_findByName_x3f___redArg(v___x_3118_, v_decl_3079_);
lean_dec(v_decl_3079_);
lean_dec_ref(v___x_3118_);
v___y_3081_ = v___x_3119_;
goto v___jp_3080_;
}
}
v___jp_3080_:
{
if (lean_obj_tag(v___y_3081_) == 0)
{
lean_object* v___x_3082_; 
v___x_3082_ = lean_box(0);
return v___x_3082_;
}
else
{
lean_object* v_val_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3091_; 
v_val_3083_ = lean_ctor_get(v___y_3081_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___y_3081_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3085_ = v___y_3081_;
v_isShared_3086_ = v_isSharedCheck_3091_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_val_3083_);
lean_dec(v___y_3081_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3091_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v_snd_3087_; lean_object* v___x_3089_; 
v_snd_3087_ = lean_ctor_get(v_val_3083_, 1);
lean_inc(v_snd_3087_);
lean_dec(v_val_3083_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 0, v_snd_3087_);
v___x_3089_ = v___x_3085_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_snd_3087_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object* v_inst_3120_, lean_object* v_ext_3121_, lean_object* v_preserveOrder_3122_, lean_object* v_env_3123_, lean_object* v_decl_3124_){
_start:
{
uint8_t v_preserveOrder_boxed_3125_; lean_object* v_res_3126_; 
v_preserveOrder_boxed_3125_ = lean_unbox(v_preserveOrder_3122_);
v_res_3126_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3120_, v_ext_3121_, v_preserveOrder_boxed_3125_, v_env_3123_, v_decl_3124_);
lean_dec_ref(v_ext_3121_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object* v_00_u03b1_3127_, lean_object* v_inst_3128_, lean_object* v_ext_3129_, uint8_t v_preserveOrder_3130_, lean_object* v_env_3131_, lean_object* v_decl_3132_){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3128_, v_ext_3129_, v_preserveOrder_3130_, v_env_3131_, v_decl_3132_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object* v_00_u03b1_3134_, lean_object* v_inst_3135_, lean_object* v_ext_3136_, lean_object* v_preserveOrder_3137_, lean_object* v_env_3138_, lean_object* v_decl_3139_){
_start:
{
uint8_t v_preserveOrder_boxed_3140_; lean_object* v_res_3141_; 
v_preserveOrder_boxed_3140_ = lean_unbox(v_preserveOrder_3137_);
v_res_3141_ = l_Lean_ParametricAttribute_getParamFromExt_x3f(v_00_u03b1_3134_, v_inst_3135_, v_ext_3136_, v_preserveOrder_boxed_3140_, v_env_3138_, v_decl_3139_);
lean_dec_ref(v_ext_3136_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3142_, lean_object* v_attr_3143_, lean_object* v_env_3144_, lean_object* v_decl_3145_){
_start:
{
lean_object* v_ext_3146_; uint8_t v_preserveOrder_3147_; lean_object* v___x_3148_; 
v_ext_3146_ = lean_ctor_get(v_attr_3143_, 1);
v_preserveOrder_3147_ = lean_ctor_get_uint8(v_attr_3143_, sizeof(void*)*2);
v___x_3148_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3142_, v_ext_3146_, v_preserveOrder_3147_, v_env_3144_, v_decl_3145_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3149_, lean_object* v_attr_3150_, lean_object* v_env_3151_, lean_object* v_decl_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3149_, v_attr_3150_, v_env_3151_, v_decl_3152_);
lean_dec_ref(v_attr_3150_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3154_, lean_object* v_inst_3155_, lean_object* v_attr_3156_, lean_object* v_env_3157_, lean_object* v_decl_3158_){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3155_, v_attr_3156_, v_env_3157_, v_decl_3158_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3160_, lean_object* v_inst_3161_, lean_object* v_attr_3162_, lean_object* v_env_3163_, lean_object* v_decl_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3160_, v_inst_3161_, v_attr_3162_, v_env_3163_, v_decl_3164_);
lean_dec_ref(v_attr_3162_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object* v_ext_3170_, lean_object* v_attr_3171_, lean_object* v_env_3172_, lean_object* v_decl_3173_, lean_object* v_param_3174_){
_start:
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3172_, v_decl_3173_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v_toEnvExtension_3176_; lean_object* v_addEntryFn_3177_; lean_object* v_asyncMode_3178_; uint8_t v_logWrites_3179_; uint8_t v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v_snd_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3219_; 
v_toEnvExtension_3176_ = lean_ctor_get(v_ext_3170_, 0);
lean_inc_ref(v_toEnvExtension_3176_);
v_addEntryFn_3177_ = lean_ctor_get(v_ext_3170_, 3);
lean_inc(v_addEntryFn_3177_);
v_asyncMode_3178_ = lean_ctor_get(v_toEnvExtension_3176_, 2);
lean_inc(v_asyncMode_3178_);
v_logWrites_3179_ = lean_ctor_get_uint8(v_toEnvExtension_3176_, sizeof(void*)*6);
v___x_3180_ = 0;
v___x_3181_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3182_ = lean_box(0);
lean_inc_ref(v_env_3172_);
v___x_3183_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3181_, v_ext_3170_, v_env_3172_, v_asyncMode_3178_, v___x_3182_, v___x_3180_);
lean_dec_ref(v_ext_3170_);
v_snd_3184_ = lean_ctor_get(v___x_3183_, 1);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3219_ == 0)
{
lean_object* v_unused_3220_; 
v_unused_3220_ = lean_ctor_get(v___x_3183_, 0);
lean_dec(v_unused_3220_);
v___x_3186_ = v___x_3183_;
v_isShared_3187_ = v_isSharedCheck_3219_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_snd_3184_);
lean_dec(v___x_3183_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3219_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3188_; 
v___x_3188_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3184_, v_decl_3173_);
lean_dec(v_snd_3184_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v___x_3190_; 
lean_dec_ref(v_attr_3171_);
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 1, v_param_3174_);
lean_ctor_set(v___x_3186_, 0, v_decl_3173_);
v___x_3190_ = v___x_3186_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_decl_3173_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v_param_3174_);
v___x_3190_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___f_3191_; uint8_t v___x_3192_; 
v___f_3191_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3191_, 0, v_addEntryFn_3177_);
lean_closure_set(v___f_3191_, 1, v___x_3190_);
v___x_3192_ = 1;
if (v_logWrites_3179_ == 0)
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3176_, v_env_3172_, v___f_3191_, v_asyncMode_3178_, v___x_3182_, v___x_3192_);
lean_dec(v_asyncMode_3178_);
v___x_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3193_);
return v___x_3194_;
}
else
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
lean_inc_ref(v_toEnvExtension_3176_);
v___x_3195_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3176_, v_env_3172_);
lean_dec_ref(v_env_3172_);
v___x_3196_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3176_, v___x_3195_, v___f_3191_, v_asyncMode_3178_, v___x_3182_, v___x_3192_);
lean_dec(v_asyncMode_3178_);
v___x_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
return v___x_3197_;
}
}
}
else
{
lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3217_; 
lean_del_object(v___x_3186_);
lean_dec(v_asyncMode_3178_);
lean_dec(v_addEntryFn_3177_);
lean_dec_ref(v_toEnvExtension_3176_);
lean_dec(v_param_3174_);
lean_dec_ref(v_env_3172_);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3217_ == 0)
{
lean_object* v_unused_3218_; 
v_unused_3218_ = lean_ctor_get(v___x_3188_, 0);
lean_dec(v_unused_3218_);
v___x_3200_ = v___x_3188_;
v_isShared_3201_ = v_isSharedCheck_3217_;
goto v_resetjp_3199_;
}
else
{
lean_dec(v___x_3188_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3217_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v_toAttributeImplCore_3202_; lean_object* v_name_3203_; uint8_t v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3215_; 
v_toAttributeImplCore_3202_ = lean_ctor_get(v_attr_3171_, 0);
lean_inc_ref(v_toAttributeImplCore_3202_);
lean_dec_ref(v_attr_3171_);
v_name_3203_ = lean_ctor_get(v_toAttributeImplCore_3202_, 1);
lean_inc(v_name_3203_);
lean_dec_ref(v_toAttributeImplCore_3202_);
v___x_3204_ = 1;
v___x_3205_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3206_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3203_, v___x_3204_);
v___x_3207_ = lean_string_append(v___x_3205_, v___x_3206_);
lean_dec_ref(v___x_3206_);
v___x_3208_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3209_ = lean_string_append(v___x_3207_, v___x_3208_);
v___x_3210_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3173_, v___x_3204_);
v___x_3211_ = lean_string_append(v___x_3209_, v___x_3210_);
lean_dec_ref(v___x_3210_);
v___x_3212_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2));
v___x_3213_ = lean_string_append(v___x_3211_, v___x_3212_);
if (v_isShared_3201_ == 0)
{
lean_ctor_set_tag(v___x_3200_, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3213_);
v___x_3215_ = v___x_3200_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3213_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
}
else
{
lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3239_; 
lean_dec(v_param_3174_);
lean_dec_ref(v_env_3172_);
lean_dec_ref(v_ext_3170_);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; 
v_unused_3240_ = lean_ctor_get(v___x_3175_, 0);
lean_dec(v_unused_3240_);
v___x_3222_ = v___x_3175_;
v_isShared_3223_ = v_isSharedCheck_3239_;
goto v_resetjp_3221_;
}
else
{
lean_dec(v___x_3175_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3239_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v_toAttributeImplCore_3224_; lean_object* v_name_3225_; uint8_t v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3237_; 
v_toAttributeImplCore_3224_ = lean_ctor_get(v_attr_3171_, 0);
lean_inc_ref(v_toAttributeImplCore_3224_);
lean_dec_ref(v_attr_3171_);
v_name_3225_ = lean_ctor_get(v_toAttributeImplCore_3224_, 1);
lean_inc(v_name_3225_);
lean_dec_ref(v_toAttributeImplCore_3224_);
v___x_3226_ = 1;
v___x_3227_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3228_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3225_, v___x_3226_);
v___x_3229_ = lean_string_append(v___x_3227_, v___x_3228_);
lean_dec_ref(v___x_3228_);
v___x_3230_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3231_ = lean_string_append(v___x_3229_, v___x_3230_);
v___x_3232_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3173_, v___x_3226_);
v___x_3233_ = lean_string_append(v___x_3231_, v___x_3232_);
lean_dec_ref(v___x_3232_);
v___x_3234_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3));
v___x_3235_ = lean_string_append(v___x_3233_, v___x_3234_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set_tag(v___x_3222_, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3235_);
v___x_3237_ = v___x_3222_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object* v_00_u03b1_3241_, lean_object* v_ext_3242_, lean_object* v_attr_3243_, lean_object* v_env_3244_, lean_object* v_decl_3245_, lean_object* v_param_3246_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3242_, v_attr_3243_, v_env_3244_, v_decl_3245_, v_param_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3248_, lean_object* v_env_3249_, lean_object* v_decl_3250_, lean_object* v_param_3251_){
_start:
{
lean_object* v_attr_3252_; lean_object* v_ext_3253_; lean_object* v___x_3254_; 
v_attr_3252_ = lean_ctor_get(v_attr_3248_, 0);
lean_inc_ref(v_attr_3252_);
v_ext_3253_ = lean_ctor_get(v_attr_3248_, 1);
lean_inc_ref(v_ext_3253_);
lean_dec_ref(v_attr_3248_);
v___x_3254_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3253_, v_attr_3252_, v_env_3249_, v_decl_3250_, v_param_3251_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3255_, lean_object* v_attr_3256_, lean_object* v_env_3257_, lean_object* v_decl_3258_, lean_object* v_param_3259_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3256_, v_env_3257_, v_decl_3258_, v_param_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(lean_object* v_x_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3264_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0___boxed(lean_object* v_x_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(v_x_3266_, v___y_3267_);
lean_dec_ref(v___y_3267_);
lean_dec_ref(v_x_3266_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(lean_object* v_s_3270_, lean_object* v_x_3271_){
_start:
{
lean_inc(v_s_3270_);
return v_s_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1___boxed(lean_object* v_s_3272_, lean_object* v_x_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(v_s_3272_, v_x_3273_);
lean_dec_ref(v_x_3273_);
lean_dec(v_s_3272_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(lean_object* v_x_3275_, lean_object* v_x_3276_){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2___boxed(lean_object* v_x_3278_, lean_object* v_x_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(v_x_3278_, v_x_3279_);
lean_dec(v_x_3279_);
lean_dec_ref(v_x_3278_);
return v_res_3280_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3(void){
_start:
{
lean_object* v___f_3284_; lean_object* v___f_3285_; lean_object* v___f_3286_; lean_object* v___f_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___f_3284_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3285_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2));
v___f_3286_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1));
v___f_3287_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0));
v___x_3288_ = lean_box(0);
v___x_3289_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_3290_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
lean_ctor_set(v___x_3290_, 1, v___x_3288_);
lean_ctor_set(v___x_3290_, 2, v___f_3287_);
lean_ctor_set(v___x_3290_, 3, v___f_3286_);
lean_ctor_set(v___x_3290_, 4, v___f_3285_);
lean_ctor_set(v___x_3290_, 5, v___f_3284_);
return v___x_3290_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3291_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3);
v___x_3292_ = lean_box(0);
v___x_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
lean_ctor_set(v___x_3293_, 1, v___x_3291_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg(){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___boxed(lean_object* v___dummy_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v_res_3297_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__0(void){
_start:
{
lean_object* v___x_3298_; 
v___x_3298_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3299_){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg(){
_start:
{
lean_object* v___x_3302_; 
v___x_3302_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg___boxed(lean_object* v___dummy_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Lean_instInhabitedEnumAttributes___redArg();
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3305_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3306_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3308_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3310_);
lean_dec(v_x_3310_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3312_, lean_object* v_x_3313_, lean_object* v_x_3314_){
_start:
{
if (lean_obj_tag(v_x_3314_) == 0)
{
return v_x_3313_;
}
else
{
lean_object* v_head_3315_; lean_object* v_tail_3316_; lean_object* v___x_3317_; 
v_head_3315_ = lean_ctor_get(v_x_3314_, 0);
lean_inc(v_head_3315_);
v_tail_3316_ = lean_ctor_get(v_x_3314_, 1);
lean_inc(v_tail_3316_);
lean_dec_ref_known(v_x_3314_, 2);
v___x_3317_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3312_, v_head_3315_);
if (lean_obj_tag(v___x_3317_) == 1)
{
lean_object* v_val_3318_; lean_object* v___x_3319_; 
v_val_3318_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_val_3318_);
lean_dec_ref_known(v___x_3317_, 1);
v___x_3319_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3315_, v_val_3318_, v_x_3313_);
v_x_3313_ = v___x_3319_;
v_x_3314_ = v_tail_3316_;
goto _start;
}
else
{
lean_dec(v___x_3317_);
lean_dec(v_head_3315_);
v_x_3314_ = v_tail_3316_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3322_, lean_object* v_x_3323_, lean_object* v_x_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3322_, v_x_3323_, v_x_3324_);
lean_dec(v_newState_3322_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3326_, lean_object* v_newState_3327_, lean_object* v_consts_3328_, lean_object* v_st_3329_){
_start:
{
lean_object* v___x_3330_; 
v___x_3330_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3327_, v_st_3329_, v_consts_3328_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3331_, lean_object* v_newState_3332_, lean_object* v_consts_3333_, lean_object* v_st_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3331_, v_newState_3332_, v_consts_3333_, v_st_3334_);
lean_dec(v_newState_3332_);
lean_dec(v_x_3331_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3345_){
_start:
{
lean_object* v___x_3346_; lean_object* v___y_3348_; 
v___x_3346_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3345_) == 0)
{
lean_object* v_size_3352_; 
v_size_3352_ = lean_ctor_get(v_s_3345_, 0);
lean_inc(v_size_3352_);
lean_dec_ref_known(v_s_3345_, 5);
v___y_3348_ = v_size_3352_;
goto v___jp_3347_;
}
else
{
lean_object* v___x_3353_; 
v___x_3353_ = lean_unsigned_to_nat(0u);
v___y_3348_ = v___x_3353_;
goto v___jp_3347_;
}
v___jp_3347_:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3349_ = l_Nat_reprFast(v___y_3348_);
v___x_3350_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
v___x_3351_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3346_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
return v___x_3351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3354_, lean_object* v_as_3355_, size_t v_i_3356_, size_t v_stop_3357_, lean_object* v_b_3358_){
_start:
{
lean_object* v___y_3360_; uint8_t v___x_3364_; 
v___x_3364_ = lean_usize_dec_eq(v_i_3356_, v_stop_3357_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; lean_object* v_fst_3366_; uint8_t v___x_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
v___x_3365_ = lean_array_uget_borrowed(v_as_3355_, v_i_3356_);
v_fst_3366_ = lean_ctor_get(v___x_3365_, 0);
v___x_3367_ = 1;
lean_inc_ref(v_env_3354_);
v___x_3368_ = l_Lean_Environment_setExporting(v_env_3354_, v___x_3367_);
lean_inc(v_fst_3366_);
v___x_3369_ = l_Lean_Environment_contains(v___x_3368_, v_fst_3366_, v___x_3364_);
if (v___x_3369_ == 0)
{
v___y_3360_ = v_b_3358_;
goto v___jp_3359_;
}
else
{
lean_object* v___x_3370_; 
lean_inc(v___x_3365_);
v___x_3370_ = lean_array_push(v_b_3358_, v___x_3365_);
v___y_3360_ = v___x_3370_;
goto v___jp_3359_;
}
}
else
{
lean_dec_ref(v_env_3354_);
return v_b_3358_;
}
v___jp_3359_:
{
size_t v___x_3361_; size_t v___x_3362_; 
v___x_3361_ = ((size_t)1ULL);
v___x_3362_ = lean_usize_add(v_i_3356_, v___x_3361_);
v_i_3356_ = v___x_3362_;
v_b_3358_ = v___y_3360_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3371_, lean_object* v_as_3372_, lean_object* v_i_3373_, lean_object* v_stop_3374_, lean_object* v_b_3375_){
_start:
{
size_t v_i_boxed_3376_; size_t v_stop_boxed_3377_; lean_object* v_res_3378_; 
v_i_boxed_3376_ = lean_unbox_usize(v_i_3373_);
lean_dec(v_i_3373_);
v_stop_boxed_3377_ = lean_unbox_usize(v_stop_3374_);
lean_dec(v_stop_3374_);
v_res_3378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3371_, v_as_3372_, v_i_boxed_3376_, v_stop_boxed_3377_, v_b_3375_);
lean_dec_ref(v_as_3372_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3379_, lean_object* v_m_3380_){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___y_3384_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___y_3395_; lean_object* v___y_3396_; uint8_t v___x_3398_; 
v___x_3381_ = lean_unsigned_to_nat(0u);
v___x_3382_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_3392_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_3382_, v_m_3380_);
v___x_3393_ = lean_array_get_size(v___x_3392_);
v___x_3398_ = lean_nat_dec_eq(v___x_3393_, v___x_3381_);
if (v___x_3398_ == 0)
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___y_3402_; uint8_t v___x_3404_; 
v___x_3399_ = lean_unsigned_to_nat(1u);
v___x_3400_ = lean_nat_sub(v___x_3393_, v___x_3399_);
v___x_3404_ = lean_nat_dec_le(v___x_3381_, v___x_3400_);
if (v___x_3404_ == 0)
{
lean_inc(v___x_3400_);
v___y_3402_ = v___x_3400_;
goto v___jp_3401_;
}
else
{
v___y_3402_ = v___x_3381_;
goto v___jp_3401_;
}
v___jp_3401_:
{
uint8_t v___x_3403_; 
v___x_3403_ = lean_nat_dec_le(v___y_3402_, v___x_3400_);
if (v___x_3403_ == 0)
{
lean_dec(v___x_3400_);
lean_inc(v___y_3402_);
v___y_3395_ = v___y_3402_;
v___y_3396_ = v___y_3402_;
goto v___jp_3394_;
}
else
{
v___y_3395_ = v___y_3402_;
v___y_3396_ = v___x_3400_;
goto v___jp_3394_;
}
}
}
else
{
v___y_3384_ = v___x_3392_;
goto v___jp_3383_;
}
v___jp_3383_:
{
lean_object* v___x_3385_; uint8_t v___x_3386_; 
v___x_3385_ = lean_array_get_size(v___y_3384_);
v___x_3386_ = lean_nat_dec_lt(v___x_3381_, v___x_3385_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3387_; 
lean_dec_ref(v_env_3379_);
v___x_3387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3382_);
lean_ctor_set(v___x_3387_, 1, v___x_3382_);
lean_ctor_set(v___x_3387_, 2, v___y_3384_);
return v___x_3387_;
}
else
{
size_t v___x_3388_; size_t v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3388_ = ((size_t)0ULL);
v___x_3389_ = lean_usize_of_nat(v___x_3385_);
v___x_3390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3379_, v___y_3384_, v___x_3388_, v___x_3389_, v___x_3382_);
lean_inc_ref(v___x_3390_);
v___x_3391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3390_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
lean_ctor_set(v___x_3391_, 2, v___y_3384_);
return v___x_3391_;
}
}
v___jp_3394_:
{
lean_object* v___x_3397_; 
v___x_3397_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_3393_, v___x_3392_, v___y_3395_, v___y_3396_);
lean_dec(v___y_3396_);
v___y_3384_ = v___x_3397_;
goto v___jp_3383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3405_, lean_object* v_m_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3405_, v_m_3406_);
lean_dec(v_m_3406_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3408_, lean_object* v_p_3409_){
_start:
{
lean_object* v_fst_3410_; lean_object* v_snd_3411_; lean_object* v___x_3412_; 
v_fst_3410_ = lean_ctor_get(v_p_3409_, 0);
lean_inc(v_fst_3410_);
v_snd_3411_ = lean_ctor_get(v_p_3409_, 1);
lean_inc(v_snd_3411_);
lean_dec_ref(v_p_3409_);
v___x_3412_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3410_, v_snd_3411_, v_s_3408_);
return v___x_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3413_, lean_object* v_x_3414_, lean_object* v_x_3415_){
_start:
{
lean_object* v___x_3417_; 
v___x_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3413_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3418_, lean_object* v_x_3419_, lean_object* v_x_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3418_, v_x_3419_, v_x_3420_);
lean_dec_ref(v_x_3420_);
lean_dec_ref(v_x_3419_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3423_){
_start:
{
if (lean_obj_tag(v_as_3423_) == 0)
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = lean_box(0);
v___x_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3425_);
return v___x_3426_;
}
else
{
lean_object* v_head_3427_; lean_object* v_tail_3428_; lean_object* v___x_3429_; 
v_head_3427_ = lean_ctor_get(v_as_3423_, 0);
lean_inc(v_head_3427_);
v_tail_3428_ = lean_ctor_get(v_as_3423_, 1);
lean_inc(v_tail_3428_);
lean_dec_ref_known(v_as_3423_, 2);
v___x_3429_ = l_Lean_registerBuiltinAttribute(v_head_3427_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_dec_ref_known(v___x_3429_, 1);
v_as_3423_ = v_tail_3428_;
goto _start;
}
else
{
lean_dec(v_tail_3428_);
return v___x_3429_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3431_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_addEntryFn_3434_, lean_object* v___x_3435_, lean_object* v_s_3436_){
_start:
{
lean_object* v_importedEntries_3437_; lean_object* v_state_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3446_; 
v_importedEntries_3437_ = lean_ctor_get(v_s_3436_, 0);
v_state_3438_ = lean_ctor_get(v_s_3436_, 1);
v_isSharedCheck_3446_ = !lean_is_exclusive(v_s_3436_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3440_ = v_s_3436_;
v_isShared_3441_ = v_isSharedCheck_3446_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_state_3438_);
lean_inc(v_importedEntries_3437_);
lean_dec(v_s_3436_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3446_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v_state_3442_; lean_object* v___x_3444_; 
v_state_3442_ = lean_apply_2(v_addEntryFn_3434_, v_state_3438_, v___x_3435_);
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 1, v_state_3442_);
v___x_3444_ = v___x_3440_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_importedEntries_3437_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v_state_3442_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2(lean_object* v_validate_3447_, lean_object* v_snd_3448_, lean_object* v_a_3449_, lean_object* v_fst_3450_, lean_object* v_decl_3451_, lean_object* v_stx_3452_, uint8_t v_kind_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v_nextMacroScope_3460_; lean_object* v_ngen_3461_; lean_object* v_auxDeclNGen_3462_; lean_object* v_traceState_3463_; lean_object* v_recordedDeps_3464_; lean_object* v_messages_3465_; lean_object* v_infoState_3466_; lean_object* v_snapshotTasks_3467_; lean_object* v___y_3468_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___x_3503_; 
v___x_3503_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3452_, v___y_3454_, v___y_3455_);
if (lean_obj_tag(v___x_3503_) == 0)
{
uint8_t v___x_3504_; uint8_t v___x_3505_; 
lean_dec_ref_known(v___x_3503_, 1);
v___x_3504_ = 0;
v___x_3505_ = l_Lean_instBEqAttributeKind_beq(v_kind_3453_, v___x_3504_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3506_; 
lean_dec(v_decl_3451_);
lean_dec_ref(v_a_3449_);
lean_dec(v_snd_3448_);
lean_dec_ref(v_validate_3447_);
v___x_3506_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3450_, v_kind_3453_, v___y_3454_, v___y_3455_);
return v___x_3506_;
}
else
{
goto v___jp_3498_;
}
}
else
{
lean_dec(v_decl_3451_);
lean_dec(v_fst_3450_);
lean_dec_ref(v_a_3449_);
lean_dec(v_snd_3448_);
lean_dec_ref(v_validate_3447_);
return v___x_3503_;
}
v___jp_3457_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3469_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_3470_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3470_, 0, v___y_3468_);
lean_ctor_set(v___x_3470_, 1, v_nextMacroScope_3460_);
lean_ctor_set(v___x_3470_, 2, v_ngen_3461_);
lean_ctor_set(v___x_3470_, 3, v_auxDeclNGen_3462_);
lean_ctor_set(v___x_3470_, 4, v_traceState_3463_);
lean_ctor_set(v___x_3470_, 5, v___x_3469_);
lean_ctor_set(v___x_3470_, 6, v_recordedDeps_3464_);
lean_ctor_set(v___x_3470_, 7, v_messages_3465_);
lean_ctor_set(v___x_3470_, 8, v_infoState_3466_);
lean_ctor_set(v___x_3470_, 9, v_snapshotTasks_3467_);
v___x_3471_ = lean_st_ref_put(v___y_3459_, v___x_3470_);
v___x_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3472_, 0, v___y_3458_);
return v___x_3472_;
}
v___jp_3473_:
{
lean_object* v___x_3476_; 
lean_inc(v___y_3475_);
lean_inc_ref(v___y_3474_);
lean_inc(v_snd_3448_);
lean_inc(v_decl_3451_);
v___x_3476_ = lean_apply_5(v_validate_3447_, v_decl_3451_, v_snd_3448_, v___y_3474_, v___y_3475_, lean_box(0));
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v___x_3477_; lean_object* v_toEnvExtension_3478_; lean_object* v_env_3479_; lean_object* v_nextMacroScope_3480_; lean_object* v_ngen_3481_; lean_object* v_auxDeclNGen_3482_; lean_object* v_traceState_3483_; lean_object* v_recordedDeps_3484_; lean_object* v_messages_3485_; lean_object* v_infoState_3486_; lean_object* v_snapshotTasks_3487_; lean_object* v_addEntryFn_3488_; lean_object* v_asyncMode_3489_; uint8_t v_logWrites_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___f_3493_; uint8_t v___x_3494_; 
lean_dec_ref_known(v___x_3476_, 1);
v___x_3477_ = lean_st_ref_take(v___y_3475_);
v_toEnvExtension_3478_ = lean_ctor_get(v_a_3449_, 0);
lean_inc_ref(v_toEnvExtension_3478_);
v_env_3479_ = lean_ctor_get(v___x_3477_, 0);
lean_inc_ref(v_env_3479_);
v_nextMacroScope_3480_ = lean_ctor_get(v___x_3477_, 1);
lean_inc(v_nextMacroScope_3480_);
v_ngen_3481_ = lean_ctor_get(v___x_3477_, 2);
lean_inc_ref(v_ngen_3481_);
v_auxDeclNGen_3482_ = lean_ctor_get(v___x_3477_, 3);
lean_inc_ref(v_auxDeclNGen_3482_);
v_traceState_3483_ = lean_ctor_get(v___x_3477_, 4);
lean_inc_ref(v_traceState_3483_);
v_recordedDeps_3484_ = lean_ctor_get(v___x_3477_, 6);
lean_inc_ref(v_recordedDeps_3484_);
v_messages_3485_ = lean_ctor_get(v___x_3477_, 7);
lean_inc_ref(v_messages_3485_);
v_infoState_3486_ = lean_ctor_get(v___x_3477_, 8);
lean_inc_ref(v_infoState_3486_);
v_snapshotTasks_3487_ = lean_ctor_get(v___x_3477_, 9);
lean_inc_ref(v_snapshotTasks_3487_);
lean_dec(v___x_3477_);
v_addEntryFn_3488_ = lean_ctor_get(v_a_3449_, 3);
lean_inc(v_addEntryFn_3488_);
lean_dec_ref(v_a_3449_);
v_asyncMode_3489_ = lean_ctor_get(v_toEnvExtension_3478_, 2);
lean_inc(v_asyncMode_3489_);
v_logWrites_3490_ = lean_ctor_get_uint8(v_toEnvExtension_3478_, sizeof(void*)*6);
v___x_3491_ = lean_box(0);
lean_inc(v_decl_3451_);
v___x_3492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3492_, 0, v_decl_3451_);
lean_ctor_set(v___x_3492_, 1, v_snd_3448_);
v___f_3493_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3493_, 0, v_addEntryFn_3488_);
lean_closure_set(v___f_3493_, 1, v___x_3492_);
v___x_3494_ = 1;
if (v_logWrites_3490_ == 0)
{
lean_object* v___x_3495_; 
v___x_3495_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3478_, v_env_3479_, v___f_3493_, v_asyncMode_3489_, v_decl_3451_, v___x_3494_);
lean_dec(v_asyncMode_3489_);
v___y_3458_ = v___x_3491_;
v___y_3459_ = v___y_3475_;
v_nextMacroScope_3460_ = v_nextMacroScope_3480_;
v_ngen_3461_ = v_ngen_3481_;
v_auxDeclNGen_3462_ = v_auxDeclNGen_3482_;
v_traceState_3463_ = v_traceState_3483_;
v_recordedDeps_3464_ = v_recordedDeps_3484_;
v_messages_3465_ = v_messages_3485_;
v_infoState_3466_ = v_infoState_3486_;
v_snapshotTasks_3467_ = v_snapshotTasks_3487_;
v___y_3468_ = v___x_3495_;
goto v___jp_3457_;
}
else
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
lean_inc_ref(v_toEnvExtension_3478_);
v___x_3496_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3478_, v_env_3479_);
lean_dec_ref(v_env_3479_);
v___x_3497_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3478_, v___x_3496_, v___f_3493_, v_asyncMode_3489_, v_decl_3451_, v___x_3494_);
lean_dec(v_asyncMode_3489_);
v___y_3458_ = v___x_3491_;
v___y_3459_ = v___y_3475_;
v_nextMacroScope_3460_ = v_nextMacroScope_3480_;
v_ngen_3461_ = v_ngen_3481_;
v_auxDeclNGen_3462_ = v_auxDeclNGen_3482_;
v_traceState_3463_ = v_traceState_3483_;
v_recordedDeps_3464_ = v_recordedDeps_3484_;
v_messages_3465_ = v_messages_3485_;
v_infoState_3466_ = v_infoState_3486_;
v_snapshotTasks_3467_ = v_snapshotTasks_3487_;
v___y_3468_ = v___x_3497_;
goto v___jp_3457_;
}
}
else
{
lean_dec(v_decl_3451_);
lean_dec_ref(v_a_3449_);
lean_dec(v_snd_3448_);
return v___x_3476_;
}
}
v___jp_3498_:
{
lean_object* v___x_3499_; lean_object* v_env_3500_; lean_object* v___x_3501_; 
v___x_3499_ = lean_st_ref_get(v___y_3455_);
v_env_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc_ref(v_env_3500_);
lean_dec(v___x_3499_);
v___x_3501_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3500_, v_decl_3451_);
lean_dec_ref(v_env_3500_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_dec(v_fst_3450_);
v___y_3474_ = v___y_3454_;
v___y_3475_ = v___y_3455_;
goto v___jp_3473_;
}
else
{
lean_object* v___x_3502_; 
lean_dec_ref_known(v___x_3501_, 1);
lean_dec_ref(v_a_3449_);
lean_dec(v_snd_3448_);
lean_dec_ref(v_validate_3447_);
v___x_3502_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3450_, v_decl_3451_, v___y_3454_, v___y_3455_);
return v___x_3502_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2___boxed(lean_object* v_validate_3507_, lean_object* v_snd_3508_, lean_object* v_a_3509_, lean_object* v_fst_3510_, lean_object* v_decl_3511_, lean_object* v_stx_3512_, lean_object* v_kind_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
uint8_t v_kind_boxed_3517_; lean_object* v_res_3518_; 
v_kind_boxed_3517_ = lean_unbox(v_kind_3513_);
v_res_3518_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2(v_validate_3507_, v_snd_3508_, v_a_3509_, v_fst_3510_, v_decl_3511_, v_stx_3512_, v_kind_boxed_3517_, v___y_3514_, v___y_3515_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3519_, lean_object* v_decl_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3524_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3525_ = l_Lean_MessageData_ofName(v_fst_3519_);
v___x_3526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3524_);
lean_ctor_set(v___x_3526_, 1, v___x_3525_);
v___x_3527_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3526_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
v___x_3529_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3528_, v___y_3521_, v___y_3522_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3530_, lean_object* v_decl_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3530_, v_decl_3531_, v___y_3532_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v_decl_3531_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3536_, lean_object* v_a_3537_, lean_object* v_ref_3538_, uint8_t v_applicationTime_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
if (lean_obj_tag(v_a_3540_) == 0)
{
lean_object* v___x_3542_; 
lean_dec(v_ref_3538_);
lean_dec_ref(v_a_3537_);
lean_dec_ref(v_validate_3536_);
v___x_3542_ = l_List_reverse___redArg(v_a_3541_);
return v___x_3542_;
}
else
{
lean_object* v_head_3543_; lean_object* v_snd_3544_; lean_object* v_tail_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3560_; 
v_head_3543_ = lean_ctor_get(v_a_3540_, 0);
lean_inc(v_head_3543_);
v_snd_3544_ = lean_ctor_get(v_head_3543_, 1);
lean_inc(v_snd_3544_);
v_tail_3545_ = lean_ctor_get(v_a_3540_, 1);
v_isSharedCheck_3560_ = !lean_is_exclusive(v_a_3540_);
if (v_isSharedCheck_3560_ == 0)
{
lean_object* v_unused_3561_; 
v_unused_3561_ = lean_ctor_get(v_a_3540_, 0);
lean_dec(v_unused_3561_);
v___x_3547_ = v_a_3540_;
v_isShared_3548_ = v_isSharedCheck_3560_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_tail_3545_);
lean_dec(v_a_3540_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3560_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v_fst_3549_; lean_object* v_fst_3550_; lean_object* v_snd_3551_; lean_object* v___f_3552_; lean_object* v___f_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3557_; 
v_fst_3549_ = lean_ctor_get(v_head_3543_, 0);
lean_inc_n(v_fst_3549_, 3);
lean_dec(v_head_3543_);
v_fst_3550_ = lean_ctor_get(v_snd_3544_, 0);
lean_inc(v_fst_3550_);
v_snd_3551_ = lean_ctor_get(v_snd_3544_, 1);
lean_inc(v_snd_3551_);
lean_dec(v_snd_3544_);
v___f_3552_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3552_, 0, v_fst_3549_);
lean_inc_ref(v_a_3537_);
lean_inc_ref(v_validate_3536_);
v___f_3553_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2___boxed), 10, 4);
lean_closure_set(v___f_3553_, 0, v_validate_3536_);
lean_closure_set(v___f_3553_, 1, v_snd_3551_);
lean_closure_set(v___f_3553_, 2, v_a_3537_);
lean_closure_set(v___f_3553_, 3, v_fst_3549_);
lean_inc(v_ref_3538_);
v___x_3554_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3554_, 0, v_ref_3538_);
lean_ctor_set(v___x_3554_, 1, v_fst_3549_);
lean_ctor_set(v___x_3554_, 2, v_fst_3550_);
lean_ctor_set_uint8(v___x_3554_, sizeof(void*)*3, v_applicationTime_3539_);
v___x_3555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3554_);
lean_ctor_set(v___x_3555_, 1, v___f_3553_);
lean_ctor_set(v___x_3555_, 2, v___f_3552_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 1, v_a_3541_);
lean_ctor_set(v___x_3547_, 0, v___x_3555_);
v___x_3557_ = v___x_3547_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3555_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v_a_3541_);
v___x_3557_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
v_a_3540_ = v_tail_3545_;
v_a_3541_ = v___x_3557_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3562_, lean_object* v_a_3563_, lean_object* v_ref_3564_, lean_object* v_applicationTime_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_){
_start:
{
uint8_t v_applicationTime_boxed_3568_; lean_object* v_res_3569_; 
v_applicationTime_boxed_3568_ = lean_unbox(v_applicationTime_3565_);
v_res_3569_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3562_, v_a_3563_, v_ref_3564_, v_applicationTime_boxed_3568_, v_a_3566_, v_a_3567_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3583_, lean_object* v_validate_3584_, uint8_t v_applicationTime_3585_, lean_object* v_ref_3586_){
_start:
{
lean_object* v___f_3588_; lean_object* v___f_3589_; lean_object* v___f_3590_; lean_object* v___f_3591_; lean_object* v___f_3592_; lean_object* v___f_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; uint8_t v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___f_3588_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3589_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3590_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3591_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3592_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3593_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3594_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3595_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
v___x_3596_ = 0;
lean_inc(v_ref_3586_);
v___x_3597_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_3597_, 0, v_ref_3586_);
lean_ctor_set(v___x_3597_, 1, v___f_3592_);
lean_ctor_set(v___x_3597_, 2, v___f_3593_);
lean_ctor_set(v___x_3597_, 3, v___f_3591_);
lean_ctor_set(v___x_3597_, 4, v___f_3590_);
lean_ctor_set(v___x_3597_, 5, v___f_3589_);
lean_ctor_set(v___x_3597_, 6, v___x_3594_);
lean_ctor_set(v___x_3597_, 7, v___x_3595_);
lean_ctor_set_uint8(v___x_3597_, sizeof(void*)*8, v___x_3596_);
lean_ctor_set_uint8(v___x_3597_, sizeof(void*)*8 + 1, v___x_3596_);
v___x_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3597_);
lean_ctor_set(v___x_3598_, 1, v___f_3588_);
v___x_3599_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3598_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc_n(v_a_3600_, 2);
lean_dec_ref_known(v___x_3599_, 1);
v___x_3601_ = lean_box(0);
v___x_3602_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3584_, v_a_3600_, v_ref_3586_, v_applicationTime_3585_, v_attrDescrs_3583_, v___x_3601_);
lean_inc(v___x_3602_);
v___x_3603_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3602_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3611_; 
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3611_ == 0)
{
lean_object* v_unused_3612_; 
v_unused_3612_ = lean_ctor_get(v___x_3603_, 0);
lean_dec(v_unused_3612_);
v___x_3605_ = v___x_3603_;
v_isShared_3606_ = v_isSharedCheck_3611_;
goto v_resetjp_3604_;
}
else
{
lean_dec(v___x_3603_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3611_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3607_; lean_object* v___x_3609_; 
v___x_3607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3602_);
lean_ctor_set(v___x_3607_, 1, v_a_3600_);
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 0, v___x_3607_);
v___x_3609_ = v___x_3605_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3607_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
else
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
lean_dec(v___x_3602_);
lean_dec(v_a_3600_);
v_a_3613_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3603_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3603_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
lean_dec(v_ref_3586_);
lean_dec_ref(v_validate_3584_);
lean_dec(v_attrDescrs_3583_);
v_a_3621_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3599_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3599_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3629_, lean_object* v_validate_3630_, lean_object* v_applicationTime_3631_, lean_object* v_ref_3632_, lean_object* v_a_3633_){
_start:
{
uint8_t v_applicationTime_boxed_3634_; lean_object* v_res_3635_; 
v_applicationTime_boxed_3634_ = lean_unbox(v_applicationTime_3631_);
v_res_3635_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3629_, v_validate_3630_, v_applicationTime_boxed_3634_, v_ref_3632_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3636_, lean_object* v_attrDescrs_3637_, lean_object* v_validate_3638_, uint8_t v_applicationTime_3639_, lean_object* v_ref_3640_){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3637_, v_validate_3638_, v_applicationTime_3639_, v_ref_3640_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3643_, lean_object* v_attrDescrs_3644_, lean_object* v_validate_3645_, lean_object* v_applicationTime_3646_, lean_object* v_ref_3647_, lean_object* v_a_3648_){
_start:
{
uint8_t v_applicationTime_boxed_3649_; lean_object* v_res_3650_; 
v_applicationTime_boxed_3649_ = lean_unbox(v_applicationTime_3646_);
v_res_3650_ = l_Lean_registerEnumAttributes(v_00_u03b1_3643_, v_attrDescrs_3644_, v_validate_3645_, v_applicationTime_boxed_3649_, v_ref_3647_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3651_, lean_object* v_env_3652_, lean_object* v_as_3653_, size_t v_i_3654_, size_t v_stop_3655_, lean_object* v_b_3656_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3652_, v_as_3653_, v_i_3654_, v_stop_3655_, v_b_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3658_, lean_object* v_env_3659_, lean_object* v_as_3660_, lean_object* v_i_3661_, lean_object* v_stop_3662_, lean_object* v_b_3663_){
_start:
{
size_t v_i_boxed_3664_; size_t v_stop_boxed_3665_; lean_object* v_res_3666_; 
v_i_boxed_3664_ = lean_unbox_usize(v_i_3661_);
lean_dec(v_i_3661_);
v_stop_boxed_3665_ = lean_unbox_usize(v_stop_3662_);
lean_dec(v_stop_3662_);
v_res_3666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3658_, v_env_3659_, v_as_3660_, v_i_boxed_3664_, v_stop_boxed_3665_, v_b_3663_);
lean_dec_ref(v_as_3660_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3667_, lean_object* v_newState_3668_, lean_object* v_x_3669_, lean_object* v_x_3670_){
_start:
{
lean_object* v___x_3671_; 
v___x_3671_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3668_, v_x_3669_, v_x_3670_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3672_, lean_object* v_newState_3673_, lean_object* v_x_3674_, lean_object* v_x_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3672_, v_newState_3673_, v_x_3674_, v_x_3675_);
lean_dec(v_newState_3673_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3677_, lean_object* v_validate_3678_, lean_object* v_a_3679_, lean_object* v_ref_3680_, uint8_t v_applicationTime_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_){
_start:
{
lean_object* v___x_3684_; 
v___x_3684_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3678_, v_a_3679_, v_ref_3680_, v_applicationTime_3681_, v_a_3682_, v_a_3683_);
return v___x_3684_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3685_, lean_object* v_validate_3686_, lean_object* v_a_3687_, lean_object* v_ref_3688_, lean_object* v_applicationTime_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_){
_start:
{
uint8_t v_applicationTime_boxed_3692_; lean_object* v_res_3693_; 
v_applicationTime_boxed_3692_ = lean_unbox(v_applicationTime_3689_);
v_res_3693_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3685_, v_validate_3686_, v_a_3687_, v_ref_3688_, v_applicationTime_boxed_3692_, v_a_3690_, v_a_3691_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3694_, lean_object* v_attr_3695_, lean_object* v_env_3696_, lean_object* v_decl_3697_){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = lean_box(1);
v___x_3699_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3696_, v_decl_3697_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v_ext_3700_; lean_object* v_toEnvExtension_3701_; lean_object* v_asyncMode_3702_; uint8_t v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
lean_dec(v_inst_3694_);
v_ext_3700_ = lean_ctor_get(v_attr_3695_, 1);
lean_inc_ref(v_ext_3700_);
lean_dec_ref(v_attr_3695_);
v_toEnvExtension_3701_ = lean_ctor_get(v_ext_3700_, 0);
v_asyncMode_3702_ = lean_ctor_get(v_toEnvExtension_3701_, 2);
lean_inc(v_asyncMode_3702_);
v___x_3703_ = 0;
lean_inc(v_decl_3697_);
v___x_3704_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3698_, v_ext_3700_, v_env_3696_, v_asyncMode_3702_, v_decl_3697_, v___x_3703_);
lean_dec(v_asyncMode_3702_);
lean_dec_ref(v_ext_3700_);
v___x_3705_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3704_, v_decl_3697_);
lean_dec(v_decl_3697_);
lean_dec(v___x_3704_);
return v___x_3705_;
}
else
{
lean_object* v_val_3706_; lean_object* v_ext_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3737_; 
v_val_3706_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_val_3706_);
lean_dec_ref_known(v___x_3699_, 1);
v_ext_3707_ = lean_ctor_get(v_attr_3695_, 1);
v_isSharedCheck_3737_ = !lean_is_exclusive(v_attr_3695_);
if (v_isSharedCheck_3737_ == 0)
{
lean_object* v_unused_3738_; 
v_unused_3738_ = lean_ctor_get(v_attr_3695_, 0);
lean_dec(v_unused_3738_);
v___x_3709_ = v_attr_3695_;
v_isShared_3710_ = v_isSharedCheck_3737_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_ext_3707_);
lean_dec(v_attr_3695_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3737_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
uint8_t v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; uint8_t v___x_3715_; 
v___x_3711_ = 0;
v___x_3712_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3698_, v_ext_3707_, v_env_3696_, v_val_3706_, v___x_3711_);
lean_dec(v_val_3706_);
lean_dec_ref(v_env_3696_);
lean_dec_ref(v_ext_3707_);
v___x_3713_ = lean_unsigned_to_nat(0u);
v___x_3714_ = lean_array_get_size(v___x_3712_);
v___x_3715_ = lean_nat_dec_lt(v___x_3713_, v___x_3714_);
if (v___x_3715_ == 0)
{
lean_object* v___x_3716_; 
lean_dec_ref(v___x_3712_);
lean_del_object(v___x_3709_);
lean_dec(v_decl_3697_);
lean_dec(v_inst_3694_);
v___x_3716_ = lean_box(0);
return v___x_3716_;
}
else
{
lean_object* v___x_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; 
v___x_3717_ = lean_unsigned_to_nat(1u);
v___x_3718_ = lean_nat_sub(v___x_3714_, v___x_3717_);
v___x_3719_ = lean_nat_dec_le(v___x_3713_, v___x_3718_);
if (v___x_3719_ == 0)
{
lean_object* v___x_3720_; 
lean_dec(v___x_3718_);
lean_dec_ref(v___x_3712_);
lean_del_object(v___x_3709_);
lean_dec(v_decl_3697_);
lean_dec(v_inst_3694_);
v___x_3720_ = lean_box(0);
return v___x_3720_;
}
else
{
lean_object* v___f_3721_; lean_object* v___x_3723_; 
v___f_3721_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 1, v_inst_3694_);
lean_ctor_set(v___x_3709_, 0, v_decl_3697_);
v___x_3723_ = v___x_3709_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_decl_3697_);
lean_ctor_set(v_reuseFailAlloc_3736_, 1, v_inst_3694_);
v___x_3723_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3724_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3725_ = l_Array_binSearchAux___redArg(v___f_3721_, v___x_3724_, v___x_3712_, v___x_3723_, v___x_3713_, v___x_3718_);
lean_dec_ref(v___x_3712_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v___x_3726_; 
v___x_3726_ = lean_box(0);
return v___x_3726_;
}
else
{
lean_object* v_val_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3735_; 
v_val_3727_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3729_ = v___x_3725_;
v_isShared_3730_ = v_isSharedCheck_3735_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_val_3727_);
lean_dec(v___x_3725_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3735_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v_snd_3731_; lean_object* v___x_3733_; 
v_snd_3731_ = lean_ctor_get(v_val_3727_, 1);
lean_inc(v_snd_3731_);
lean_dec(v_val_3727_);
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 0, v_snd_3731_);
v___x_3733_ = v___x_3729_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_snd_3731_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3739_, lean_object* v_inst_3740_, lean_object* v_attr_3741_, lean_object* v_env_3742_, lean_object* v_decl_3743_){
_start:
{
lean_object* v___x_3744_; 
v___x_3744_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3740_, v_attr_3741_, v_env_3742_, v_decl_3743_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3753_, lean_object* v_env_3754_, lean_object* v_decl_3755_, lean_object* v_val_3756_){
_start:
{
lean_object* v_ext_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3827_; 
v_ext_3757_ = lean_ctor_get(v_attrs_3753_, 1);
v_isSharedCheck_3827_ = !lean_is_exclusive(v_attrs_3753_);
if (v_isSharedCheck_3827_ == 0)
{
lean_object* v_unused_3828_; 
v_unused_3828_ = lean_ctor_get(v_attrs_3753_, 0);
lean_dec(v_unused_3828_);
v___x_3759_ = v_attrs_3753_;
v_isShared_3760_ = v_isSharedCheck_3827_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_ext_3757_);
lean_dec(v_attrs_3753_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3827_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v_toEnvExtension_3761_; lean_object* v_name_3762_; lean_object* v_addEntryFn_3763_; lean_object* v___x_3764_; uint8_t v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v_pfx_3773_; lean_object* v___x_3774_; 
v_toEnvExtension_3761_ = lean_ctor_get(v_ext_3757_, 0);
lean_inc_ref(v_toEnvExtension_3761_);
v_name_3762_ = lean_ctor_get(v_ext_3757_, 1);
v_addEntryFn_3763_ = lean_ctor_get(v_ext_3757_, 3);
lean_inc(v_addEntryFn_3763_);
v___x_3764_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3765_ = 1;
lean_inc(v_name_3762_);
v___x_3766_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3762_, v___x_3765_);
v___x_3767_ = lean_string_append(v___x_3764_, v___x_3766_);
lean_dec_ref(v___x_3766_);
v___x_3768_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3769_ = lean_string_append(v___x_3767_, v___x_3768_);
lean_inc(v_decl_3755_);
v___x_3770_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3755_, v___x_3765_);
v___x_3771_ = lean_string_append(v___x_3769_, v___x_3770_);
lean_dec_ref(v___x_3770_);
v___x_3772_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3773_ = lean_string_append(v___x_3771_, v___x_3772_);
v___x_3774_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3754_, v_decl_3755_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v_asyncMode_3775_; uint8_t v_logWrites_3776_; uint8_t v___x_3777_; 
v_asyncMode_3775_ = lean_ctor_get(v_toEnvExtension_3761_, 2);
lean_inc(v_asyncMode_3775_);
v_logWrites_3776_ = lean_ctor_get_uint8(v_toEnvExtension_3761_, sizeof(void*)*6);
lean_inc(v_decl_3755_);
lean_inc_ref(v_env_3754_);
v___x_3777_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3754_, v_decl_3755_, v_asyncMode_3775_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___y_3781_; lean_object* v___x_3785_; 
lean_dec(v_asyncMode_3775_);
lean_dec(v_addEntryFn_3763_);
lean_dec_ref(v_toEnvExtension_3761_);
lean_del_object(v___x_3759_);
lean_dec_ref(v_ext_3757_);
lean_dec(v_val_3756_);
lean_dec(v_decl_3755_);
v___x_3778_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3779_ = lean_string_append(v_pfx_3773_, v___x_3778_);
v___x_3785_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3754_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v___x_3786_; 
v___x_3786_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3781_ = v___x_3786_;
goto v___jp_3780_;
}
else
{
lean_object* v_val_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v_val_3787_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_val_3787_);
lean_dec_ref_known(v___x_3785_, 1);
v___x_3788_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3789_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3787_, v___x_3765_);
v___x_3790_ = l_addParenHeuristic(v___x_3789_);
v___x_3791_ = lean_string_append(v___x_3788_, v___x_3790_);
lean_dec_ref(v___x_3790_);
v___x_3792_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3793_ = lean_string_append(v___x_3791_, v___x_3792_);
v___y_3781_ = v___x_3793_;
goto v___jp_3780_;
}
v___jp_3780_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3782_ = lean_string_append(v___x_3779_, v___y_3781_);
lean_dec_ref(v___y_3781_);
v___x_3783_ = lean_string_append(v___x_3782_, v___x_3772_);
v___x_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
return v___x_3784_;
}
}
else
{
lean_object* v___x_3794_; uint8_t v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3794_ = lean_box(1);
v___x_3795_ = 0;
lean_inc(v_decl_3755_);
lean_inc_ref(v_env_3754_);
v___x_3796_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3794_, v_ext_3757_, v_env_3754_, v_asyncMode_3775_, v_decl_3755_, v___x_3795_);
lean_dec_ref(v_ext_3757_);
v___x_3797_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3796_, v_decl_3755_);
lean_dec(v___x_3796_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v___x_3799_; 
lean_dec_ref(v_pfx_3773_);
lean_inc(v_decl_3755_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 1, v_val_3756_);
lean_ctor_set(v___x_3759_, 0, v_decl_3755_);
v___x_3799_ = v___x_3759_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_decl_3755_);
lean_ctor_set(v_reuseFailAlloc_3806_, 1, v_val_3756_);
v___x_3799_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
lean_object* v___f_3800_; 
v___f_3800_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3800_, 0, v_addEntryFn_3763_);
lean_closure_set(v___f_3800_, 1, v___x_3799_);
if (v_logWrites_3776_ == 0)
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3761_, v_env_3754_, v___f_3800_, v_asyncMode_3775_, v_decl_3755_, v___x_3777_);
lean_dec(v_asyncMode_3775_);
v___x_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3801_);
return v___x_3802_;
}
else
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
lean_inc_ref(v_toEnvExtension_3761_);
v___x_3803_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3761_, v_env_3754_);
lean_dec_ref(v_env_3754_);
v___x_3804_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3761_, v___x_3803_, v___f_3800_, v_asyncMode_3775_, v_decl_3755_, v___x_3777_);
lean_dec(v_asyncMode_3775_);
v___x_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3804_);
return v___x_3805_;
}
}
}
else
{
lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3815_; 
lean_dec(v_asyncMode_3775_);
lean_dec(v_addEntryFn_3763_);
lean_dec_ref(v_toEnvExtension_3761_);
lean_del_object(v___x_3759_);
lean_dec(v_val_3756_);
lean_dec(v_decl_3755_);
lean_dec_ref(v_env_3754_);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3815_ == 0)
{
lean_object* v_unused_3816_; 
v_unused_3816_ = lean_ctor_get(v___x_3797_, 0);
lean_dec(v_unused_3816_);
v___x_3808_ = v___x_3797_;
v_isShared_3809_ = v_isSharedCheck_3815_;
goto v_resetjp_3807_;
}
else
{
lean_dec(v___x_3797_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3815_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3813_; 
v___x_3810_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3811_ = lean_string_append(v_pfx_3773_, v___x_3810_);
if (v_isShared_3809_ == 0)
{
lean_ctor_set_tag(v___x_3808_, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3811_);
v___x_3813_ = v___x_3808_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3811_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
}
else
{
lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3825_; 
lean_dec(v_addEntryFn_3763_);
lean_dec_ref(v_toEnvExtension_3761_);
lean_del_object(v___x_3759_);
lean_dec_ref(v_ext_3757_);
lean_dec(v_val_3756_);
lean_dec(v_decl_3755_);
lean_dec_ref(v_env_3754_);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3825_ == 0)
{
lean_object* v_unused_3826_; 
v_unused_3826_ = lean_ctor_get(v___x_3774_, 0);
lean_dec(v_unused_3826_);
v___x_3818_ = v___x_3774_;
v_isShared_3819_ = v_isSharedCheck_3825_;
goto v_resetjp_3817_;
}
else
{
lean_dec(v___x_3774_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3825_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3823_; 
v___x_3820_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3821_ = lean_string_append(v_pfx_3773_, v___x_3820_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set_tag(v___x_3818_, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3821_);
v___x_3823_ = v___x_3818_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3821_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3829_, lean_object* v_attrs_3830_, lean_object* v_env_3831_, lean_object* v_decl_3832_, lean_object* v_val_3833_){
_start:
{
lean_object* v___x_3834_; 
v___x_3834_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3830_, v_env_3831_, v_decl_3832_, v_val_3833_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3836_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3837_ = lean_st_mk_ref(v___x_3836_);
v___x_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3837_);
return v___x_3838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3843_, lean_object* v_builder_3844_){
_start:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; uint8_t v___x_3848_; 
v___x_3846_ = l_Lean_attributeImplBuilderTableRef;
v___x_3847_ = lean_st_ref_get(v___x_3846_);
v___x_3848_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3847_, v_builderId_3843_);
lean_dec(v___x_3847_);
if (v___x_3848_ == 0)
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3849_ = lean_st_ref_take(v___x_3846_);
v___x_3850_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3849_, v_builderId_3843_, v_builder_3844_);
v___x_3851_ = lean_st_ref_put(v___x_3846_, v___x_3850_);
v___x_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3851_);
return v___x_3852_;
}
else
{
lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
lean_dec_ref(v_builder_3844_);
v___x_3853_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3854_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3843_, v___x_3848_);
v___x_3855_ = lean_string_append(v___x_3853_, v___x_3854_);
lean_dec_ref(v___x_3854_);
v___x_3856_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3857_ = lean_string_append(v___x_3855_, v___x_3856_);
v___x_3858_ = lean_mk_io_user_error(v___x_3857_);
v___x_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3858_);
return v___x_3859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3860_, lean_object* v_builder_3861_, lean_object* v_a_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Lean_registerAttributeImplBuilder(v_builderId_3860_, v_builder_3861_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3864_){
_start:
{
if (lean_obj_tag(v_e_3864_) == 0)
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3874_; 
v_a_3866_ = lean_ctor_get(v_e_3864_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v_e_3864_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3868_ = v_e_3864_;
v_isShared_3869_ = v_isSharedCheck_3874_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v_e_3864_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3874_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3870_; lean_object* v___x_3872_; 
v___x_3870_ = lean_mk_io_user_error(v_a_3866_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set_tag(v___x_3868_, 1);
lean_ctor_set(v___x_3868_, 0, v___x_3870_);
v___x_3872_ = v___x_3868_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v___x_3870_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
else
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3882_; 
v_a_3875_ = lean_ctor_get(v_e_3864_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v_e_3864_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3877_ = v_e_3864_;
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v_e_3864_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3880_; 
if (v_isShared_3878_ == 0)
{
lean_ctor_set_tag(v___x_3877_, 0);
v___x_3880_ = v___x_3877_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_a_3875_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3883_, lean_object* v_a_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3883_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3886_, lean_object* v_e_3887_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3887_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3890_, lean_object* v_e_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3890_, v_e_3891_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3894_, lean_object* v_x_3895_){
_start:
{
if (lean_obj_tag(v_x_3895_) == 0)
{
lean_object* v___x_3896_; 
v___x_3896_ = lean_box(0);
return v___x_3896_;
}
else
{
lean_object* v_key_3897_; lean_object* v_value_3898_; lean_object* v_tail_3899_; uint8_t v___x_3900_; 
v_key_3897_ = lean_ctor_get(v_x_3895_, 0);
v_value_3898_ = lean_ctor_get(v_x_3895_, 1);
v_tail_3899_ = lean_ctor_get(v_x_3895_, 2);
v___x_3900_ = lean_name_eq(v_key_3897_, v_a_3894_);
if (v___x_3900_ == 0)
{
v_x_3895_ = v_tail_3899_;
goto _start;
}
else
{
lean_object* v___x_3902_; 
lean_inc(v_value_3898_);
v___x_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3902_, 0, v_value_3898_);
return v___x_3902_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3903_, lean_object* v_x_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3903_, v_x_3904_);
lean_dec(v_x_3904_);
lean_dec(v_a_3903_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3906_, lean_object* v_a_3907_){
_start:
{
lean_object* v_buckets_3908_; lean_object* v___x_3909_; uint64_t v___y_3911_; 
v_buckets_3908_ = lean_ctor_get(v_m_3906_, 1);
v___x_3909_ = lean_array_get_size(v_buckets_3908_);
if (lean_obj_tag(v_a_3907_) == 0)
{
uint64_t v___x_3925_; 
v___x_3925_ = 1723ULL;
v___y_3911_ = v___x_3925_;
goto v___jp_3910_;
}
else
{
uint64_t v_hash_3926_; 
v_hash_3926_ = lean_ctor_get_uint64(v_a_3907_, sizeof(void*)*2);
v___y_3911_ = v_hash_3926_;
goto v___jp_3910_;
}
v___jp_3910_:
{
uint64_t v___x_3912_; uint64_t v___x_3913_; uint64_t v_fold_3914_; uint64_t v___x_3915_; uint64_t v___x_3916_; uint64_t v___x_3917_; size_t v___x_3918_; size_t v___x_3919_; size_t v___x_3920_; size_t v___x_3921_; size_t v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3912_ = 32ULL;
v___x_3913_ = lean_uint64_shift_right(v___y_3911_, v___x_3912_);
v_fold_3914_ = lean_uint64_xor(v___y_3911_, v___x_3913_);
v___x_3915_ = 16ULL;
v___x_3916_ = lean_uint64_shift_right(v_fold_3914_, v___x_3915_);
v___x_3917_ = lean_uint64_xor(v_fold_3914_, v___x_3916_);
v___x_3918_ = lean_uint64_to_usize(v___x_3917_);
v___x_3919_ = lean_usize_of_nat(v___x_3909_);
v___x_3920_ = ((size_t)1ULL);
v___x_3921_ = lean_usize_sub(v___x_3919_, v___x_3920_);
v___x_3922_ = lean_usize_land(v___x_3918_, v___x_3921_);
v___x_3923_ = lean_array_uget_borrowed(v_buckets_3908_, v___x_3922_);
v___x_3924_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3907_, v___x_3923_);
return v___x_3924_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3927_, lean_object* v_a_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3927_, v_a_3928_);
lean_dec(v_a_3928_);
lean_dec_ref(v_m_3927_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3931_){
_start:
{
lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v_builderId_3935_; lean_object* v_ref_3936_; lean_object* v_args_3937_; lean_object* v___x_3938_; 
v___x_3933_ = l_Lean_attributeImplBuilderTableRef;
v___x_3934_ = lean_st_ref_get(v___x_3933_);
v_builderId_3935_ = lean_ctor_get(v_e_3931_, 0);
lean_inc(v_builderId_3935_);
v_ref_3936_ = lean_ctor_get(v_e_3931_, 1);
lean_inc(v_ref_3936_);
v_args_3937_ = lean_ctor_get(v_e_3931_, 2);
lean_inc(v_args_3937_);
lean_dec_ref(v_e_3931_);
v___x_3938_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3934_, v_builderId_3935_);
lean_dec(v___x_3934_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v___x_3939_; uint8_t v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
lean_dec(v_args_3937_);
lean_dec(v_ref_3936_);
v___x_3939_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3940_ = 1;
v___x_3941_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3935_, v___x_3940_);
v___x_3942_ = lean_string_append(v___x_3939_, v___x_3941_);
lean_dec_ref(v___x_3941_);
v___x_3943_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3944_ = lean_string_append(v___x_3942_, v___x_3943_);
v___x_3945_ = lean_mk_io_user_error(v___x_3944_);
v___x_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3945_);
return v___x_3946_;
}
else
{
lean_object* v_val_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
lean_dec(v_builderId_3935_);
v_val_3947_ = lean_ctor_get(v___x_3938_, 0);
lean_inc(v_val_3947_);
lean_dec_ref_known(v___x_3938_, 1);
v___x_3948_ = lean_apply_2(v_val_3947_, v_ref_3936_, v_args_3937_);
v___x_3949_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3948_);
return v___x_3949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3950_, lean_object* v_a_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l_Lean_mkAttributeImplOfEntry(v_e_3950_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3953_, lean_object* v_m_3954_, lean_object* v_a_3955_){
_start:
{
lean_object* v___x_3956_; 
v___x_3956_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3954_, v_a_3955_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3957_, lean_object* v_m_3958_, lean_object* v_a_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3957_, v_m_3958_, v_a_3959_);
lean_dec(v_a_3959_);
lean_dec_ref(v_m_3958_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3961_, lean_object* v_a_3962_, lean_object* v_x_3963_){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3962_, v_x_3963_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3965_, lean_object* v_a_3966_, lean_object* v_x_3967_){
_start:
{
lean_object* v_res_3968_; 
v_res_3968_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3965_, v_a_3966_, v_x_3967_);
lean_dec(v_x_3967_);
lean_dec(v_a_3966_);
return v_res_3968_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3969_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3970_ = lean_box(0);
v___x_3971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
lean_ctor_set(v___x_3971_, 1, v___x_3969_);
return v___x_3971_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3972_; 
v___x_3972_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3972_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3973_; 
v___x_3973_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3975_ = l_Lean_attributeMapRef;
v___x_3976_ = lean_st_ref_get(v___x_3975_);
v___x_3977_ = lean_box(0);
v___x_3978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3977_);
lean_ctor_set(v___x_3978_, 1, v___x_3976_);
v___x_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3978_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3987_, lean_object* v_opts_3988_, lean_object* v_declName_3989_){
_start:
{
uint8_t v___x_3992_; lean_object* v___x_3993_; 
v___x_3992_ = 0;
lean_inc(v_declName_3989_);
lean_inc_ref(v_env_3987_);
v___x_3993_ = l_Lean_Environment_find_x3f(v_env_3987_, v_declName_3989_, v___x_3992_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v___x_3994_; uint8_t v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
lean_dec_ref(v_env_3987_);
v___x_3994_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3995_ = 1;
v___x_3996_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3989_, v___x_3995_);
v___x_3997_ = lean_string_append(v___x_3994_, v___x_3996_);
lean_dec_ref(v___x_3996_);
v___x_3998_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3999_ = lean_string_append(v___x_3997_, v___x_3998_);
v___x_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3999_);
return v___x_4000_;
}
else
{
lean_object* v_val_4001_; lean_object* v___x_4002_; 
v_val_4001_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_val_4001_);
lean_dec_ref_known(v___x_3993_, 1);
v___x_4002_ = l_Lean_ConstantInfo_type(v_val_4001_);
lean_dec(v_val_4001_);
if (lean_obj_tag(v___x_4002_) == 4)
{
lean_object* v_declName_4003_; 
v_declName_4003_ = lean_ctor_get(v___x_4002_, 0);
lean_inc(v_declName_4003_);
lean_dec_ref_known(v___x_4002_, 2);
if (lean_obj_tag(v_declName_4003_) == 1)
{
lean_object* v_pre_4004_; 
v_pre_4004_ = lean_ctor_get(v_declName_4003_, 0);
lean_inc(v_pre_4004_);
if (lean_obj_tag(v_pre_4004_) == 1)
{
lean_object* v_pre_4005_; 
v_pre_4005_ = lean_ctor_get(v_pre_4004_, 0);
if (lean_obj_tag(v_pre_4005_) == 0)
{
lean_object* v_str_4006_; lean_object* v_str_4007_; lean_object* v___x_4008_; uint8_t v___x_4009_; 
v_str_4006_ = lean_ctor_get(v_declName_4003_, 1);
lean_inc_ref(v_str_4006_);
lean_dec_ref_known(v_declName_4003_, 2);
v_str_4007_ = lean_ctor_get(v_pre_4004_, 1);
lean_inc_ref(v_str_4007_);
lean_dec_ref_known(v_pre_4004_, 2);
v___x_4008_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_4009_ = lean_string_dec_eq(v_str_4007_, v___x_4008_);
lean_dec_ref(v_str_4007_);
if (v___x_4009_ == 0)
{
lean_dec_ref(v_str_4006_);
lean_dec(v_declName_3989_);
lean_dec_ref(v_env_3987_);
goto v___jp_3990_;
}
else
{
lean_object* v___x_4010_; uint8_t v___x_4011_; 
v___x_4010_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_4011_ = lean_string_dec_eq(v_str_4006_, v___x_4010_);
lean_dec_ref(v_str_4006_);
if (v___x_4011_ == 0)
{
lean_dec(v_declName_3989_);
lean_dec_ref(v_env_3987_);
goto v___jp_3990_;
}
else
{
lean_object* v___x_4012_; 
v___x_4012_ = l_Lean_Environment_evalConst___redArg(v_env_3987_, v_opts_3988_, v_declName_3989_, v___x_4011_);
lean_dec(v_declName_3989_);
lean_dec_ref(v_env_3987_);
return v___x_4012_;
}
}
}
else
{
lean_dec_ref_known(v_pre_4004_, 2);
lean_dec_ref_known(v_declName_4003_, 2);
lean_dec(v_declName_3989_);
lean_dec_ref(v_env_3987_);
goto v___jp_3990_;
}
}
else
{
lean_dec(v_pre_4004_);
lean_dec_ref_known(v_declName_4003_, 2);
lean_dec(v_declName_3989_);
lean_dec_ref(v_env_3987_);
goto v___jp_3990_;
}
}
else
{
lean_dec(v_declName_4003_);
lean_dec(v_declName_3989_);
lean_dec_ref(v_env_3987_);
goto v___jp_3990_;
}
}
else
{
lean_dec_ref(v___x_4002_);
lean_dec(v_declName_3989_);
lean_dec_ref(v_env_3987_);
goto v___jp_3990_;
}
}
v___jp_3990_:
{
lean_object* v___x_3991_; 
v___x_3991_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_4013_, lean_object* v_opts_4014_, lean_object* v_declName_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_4013_, v_opts_4014_, v_declName_4015_);
lean_dec_ref(v_opts_4014_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_4017_, size_t v_i_4018_, size_t v_stop_4019_, lean_object* v_b_4020_){
_start:
{
uint8_t v___x_4022_; 
v___x_4022_ = lean_usize_dec_eq(v_i_4018_, v_stop_4019_);
if (v___x_4022_ == 0)
{
lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4023_ = lean_array_uget_borrowed(v_as_4017_, v_i_4018_);
lean_inc(v___x_4023_);
v___x_4024_ = l_Lean_mkAttributeImplOfEntry(v___x_4023_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v_a_4025_; lean_object* v_toAttributeImplCore_4026_; lean_object* v_name_4027_; lean_object* v___x_4028_; size_t v___x_4029_; size_t v___x_4030_; 
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_a_4025_);
lean_dec_ref_known(v___x_4024_, 1);
v_toAttributeImplCore_4026_ = lean_ctor_get(v_a_4025_, 0);
v_name_4027_ = lean_ctor_get(v_toAttributeImplCore_4026_, 1);
lean_inc(v_name_4027_);
v___x_4028_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_4020_, v_name_4027_, v_a_4025_);
v___x_4029_ = ((size_t)1ULL);
v___x_4030_ = lean_usize_add(v_i_4018_, v___x_4029_);
v_i_4018_ = v___x_4030_;
v_b_4020_ = v___x_4028_;
goto _start;
}
else
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4039_; 
lean_dec_ref(v_b_4020_);
v_a_4032_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4034_ = v___x_4024_;
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v___x_4024_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4037_; 
if (v_isShared_4035_ == 0)
{
v___x_4037_ = v___x_4034_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_a_4032_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
}
}
else
{
lean_object* v___x_4040_; 
v___x_4040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4040_, 0, v_b_4020_);
return v___x_4040_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_4041_, lean_object* v_i_4042_, lean_object* v_stop_4043_, lean_object* v_b_4044_, lean_object* v___y_4045_){
_start:
{
size_t v_i_boxed_4046_; size_t v_stop_boxed_4047_; lean_object* v_res_4048_; 
v_i_boxed_4046_ = lean_unbox_usize(v_i_4042_);
lean_dec(v_i_4042_);
v_stop_boxed_4047_ = lean_unbox_usize(v_stop_4043_);
lean_dec(v_stop_4043_);
v_res_4048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4041_, v_i_boxed_4046_, v_stop_boxed_4047_, v_b_4044_);
lean_dec_ref(v_as_4041_);
return v_res_4048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_4049_, size_t v_i_4050_, size_t v_stop_4051_, lean_object* v_b_4052_, lean_object* v___y_4053_){
_start:
{
lean_object* v_a_4056_; uint8_t v___x_4060_; 
v___x_4060_ = lean_usize_dec_eq(v_i_4050_, v_stop_4051_);
if (v___x_4060_ == 0)
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; uint8_t v___x_4064_; 
v___x_4061_ = lean_array_uget_borrowed(v_as_4049_, v_i_4050_);
v___x_4062_ = lean_unsigned_to_nat(0u);
v___x_4063_ = lean_array_get_size(v___x_4061_);
v___x_4064_ = lean_nat_dec_lt(v___x_4062_, v___x_4063_);
if (v___x_4064_ == 0)
{
v_a_4056_ = v_b_4052_;
goto v___jp_4055_;
}
else
{
size_t v___x_4065_; size_t v___x_4066_; lean_object* v___x_4067_; 
v___x_4065_ = ((size_t)0ULL);
v___x_4066_ = lean_usize_of_nat(v___x_4063_);
v___x_4067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4061_, v___x_4065_, v___x_4066_, v_b_4052_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v___x_4067_, 1);
v_a_4056_ = v_a_4068_;
goto v___jp_4055_;
}
else
{
return v___x_4067_;
}
}
}
else
{
lean_object* v___x_4069_; 
v___x_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4069_, 0, v_b_4052_);
return v___x_4069_;
}
v___jp_4055_:
{
size_t v___x_4057_; size_t v___x_4058_; 
v___x_4057_ = ((size_t)1ULL);
v___x_4058_ = lean_usize_add(v_i_4050_, v___x_4057_);
v_i_4050_ = v___x_4058_;
v_b_4052_ = v_a_4056_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4070_, lean_object* v_i_4071_, lean_object* v_stop_4072_, lean_object* v_b_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
size_t v_i_boxed_4076_; size_t v_stop_boxed_4077_; lean_object* v_res_4078_; 
v_i_boxed_4076_ = lean_unbox_usize(v_i_4071_);
lean_dec(v_i_4071_);
v_stop_boxed_4077_ = lean_unbox_usize(v_stop_4072_);
lean_dec(v_stop_4072_);
v_res_4078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4070_, v_i_boxed_4076_, v_stop_boxed_4077_, v_b_4073_, v___y_4074_);
lean_dec_ref(v___y_4074_);
lean_dec_ref(v_as_4070_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4079_, lean_object* v_a_4080_){
_start:
{
lean_object* v_a_4083_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; uint8_t v___x_4091_; 
v___x_4087_ = l_Lean_attributeMapRef;
v___x_4088_ = lean_st_ref_get(v___x_4087_);
v___x_4089_ = lean_unsigned_to_nat(0u);
v___x_4090_ = lean_array_get_size(v_es_4079_);
v___x_4091_ = lean_nat_dec_lt(v___x_4089_, v___x_4090_);
if (v___x_4091_ == 0)
{
v_a_4083_ = v___x_4088_;
goto v___jp_4082_;
}
else
{
size_t v___x_4092_; size_t v___x_4093_; lean_object* v___x_4094_; 
v___x_4092_ = ((size_t)0ULL);
v___x_4093_ = lean_usize_of_nat(v___x_4090_);
v___x_4094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4079_, v___x_4092_, v___x_4093_, v___x_4088_, v_a_4080_);
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_object* v_a_4095_; 
v_a_4095_ = lean_ctor_get(v___x_4094_, 0);
lean_inc(v_a_4095_);
lean_dec_ref_known(v___x_4094_, 1);
v_a_4083_ = v_a_4095_;
goto v___jp_4082_;
}
else
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
v_a_4096_ = lean_ctor_get(v___x_4094_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4094_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4094_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4094_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4101_; 
if (v_isShared_4099_ == 0)
{
v___x_4101_ = v___x_4098_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_a_4096_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
v___jp_4082_:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4084_ = lean_box(0);
v___x_4085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4084_);
lean_ctor_set(v___x_4085_, 1, v_a_4083_);
v___x_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4085_);
return v___x_4086_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4104_, v_a_4105_);
lean_dec_ref(v_a_4105_);
lean_dec_ref(v_es_4104_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4108_, size_t v_i_4109_, size_t v_stop_4110_, lean_object* v_b_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v___x_4114_; 
v___x_4114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4108_, v_i_4109_, v_stop_4110_, v_b_4111_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4115_, lean_object* v_i_4116_, lean_object* v_stop_4117_, lean_object* v_b_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
size_t v_i_boxed_4121_; size_t v_stop_boxed_4122_; lean_object* v_res_4123_; 
v_i_boxed_4121_ = lean_unbox_usize(v_i_4116_);
lean_dec(v_i_4116_);
v_stop_boxed_4122_ = lean_unbox_usize(v_stop_4117_);
lean_dec(v_stop_4117_);
v_res_4123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4115_, v_i_boxed_4121_, v_stop_boxed_4122_, v_b_4118_, v___y_4119_);
lean_dec_ref(v___y_4119_);
lean_dec_ref(v_as_4115_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4124_, lean_object* v_e_4125_){
_start:
{
lean_object* v_snd_4126_; lean_object* v_toAttributeImplCore_4127_; lean_object* v_fst_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4146_; 
v_snd_4126_ = lean_ctor_get(v_e_4125_, 1);
lean_inc(v_snd_4126_);
v_toAttributeImplCore_4127_ = lean_ctor_get(v_snd_4126_, 0);
v_fst_4128_ = lean_ctor_get(v_e_4125_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v_e_4125_);
if (v_isSharedCheck_4146_ == 0)
{
lean_object* v_unused_4147_; 
v_unused_4147_ = lean_ctor_get(v_e_4125_, 1);
lean_dec(v_unused_4147_);
v___x_4130_ = v_e_4125_;
v_isShared_4131_ = v_isSharedCheck_4146_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_fst_4128_);
lean_dec(v_e_4125_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4146_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v_newEntries_4132_; lean_object* v_map_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4145_; 
v_newEntries_4132_ = lean_ctor_get(v_s_4124_, 0);
v_map_4133_ = lean_ctor_get(v_s_4124_, 1);
v_isSharedCheck_4145_ = !lean_is_exclusive(v_s_4124_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4135_ = v_s_4124_;
v_isShared_4136_ = v_isSharedCheck_4145_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_map_4133_);
lean_inc(v_newEntries_4132_);
lean_dec(v_s_4124_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4145_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v_name_4137_; lean_object* v___x_4139_; 
v_name_4137_ = lean_ctor_get(v_toAttributeImplCore_4127_, 1);
lean_inc(v_name_4137_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set_tag(v___x_4130_, 1);
lean_ctor_set(v___x_4130_, 1, v_newEntries_4132_);
v___x_4139_ = v___x_4130_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_fst_4128_);
lean_ctor_set(v_reuseFailAlloc_4144_, 1, v_newEntries_4132_);
v___x_4139_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
lean_object* v___x_4140_; lean_object* v___x_4142_; 
v___x_4140_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4133_, v_name_4137_, v_snd_4126_);
if (v_isShared_4136_ == 0)
{
lean_ctor_set(v___x_4135_, 1, v___x_4140_);
lean_ctor_set(v___x_4135_, 0, v___x_4139_);
v___x_4142_ = v___x_4135_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v___x_4139_);
lean_ctor_set(v_reuseFailAlloc_4143_, 1, v___x_4140_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4148_, lean_object* v_s_4149_){
_start:
{
lean_object* v_newEntries_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v_newEntries_4150_ = lean_ctor_get(v_s_4149_, 0);
lean_inc(v_newEntries_4150_);
lean_dec_ref(v_s_4149_);
v___x_4151_ = l_List_reverse___redArg(v_newEntries_4150_);
v___x_4152_ = lean_array_mk(v___x_4151_);
lean_inc_ref_n(v___x_4152_, 2);
v___x_4153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4152_);
lean_ctor_set(v___x_4153_, 1, v___x_4152_);
lean_ctor_set(v___x_4153_, 2, v___x_4152_);
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4154_, lean_object* v_s_4155_){
_start:
{
lean_object* v_res_4156_; 
v_res_4156_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4154_, v_s_4155_);
lean_dec_ref(v_x_4154_);
return v_res_4156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4157_){
_start:
{
lean_object* v_newEntries_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4169_; 
v_newEntries_4158_ = lean_ctor_get(v_s_4157_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v_s_4157_);
if (v_isSharedCheck_4169_ == 0)
{
lean_object* v_unused_4170_; 
v_unused_4170_ = lean_ctor_get(v_s_4157_, 1);
lean_dec(v_unused_4170_);
v___x_4160_ = v_s_4157_;
v_isShared_4161_ = v_isSharedCheck_4169_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_newEntries_4158_);
lean_dec(v_s_4157_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4169_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4167_; 
v___x_4162_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4163_ = l_List_lengthTR___redArg(v_newEntries_4158_);
lean_dec(v_newEntries_4158_);
v___x_4164_ = l_Nat_reprFast(v___x_4163_);
v___x_4165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4164_);
if (v_isShared_4161_ == 0)
{
lean_ctor_set_tag(v___x_4160_, 5);
lean_ctor_set(v___x_4160_, 1, v___x_4165_);
lean_ctor_set(v___x_4160_, 0, v___x_4162_);
v___x_4167_ = v___x_4160_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4162_);
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
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4171_){
_start:
{
lean_object* v_newEntries_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v_newEntries_4172_ = lean_ctor_get(v_s_4171_, 0);
lean_inc(v_newEntries_4172_);
lean_dec_ref(v_s_4171_);
v___x_4173_ = l_List_reverse___redArg(v_newEntries_4172_);
v___x_4174_ = lean_array_mk(v___x_4173_);
return v___x_4174_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___f_4187_; lean_object* v___f_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4184_ = 0;
v___x_4185_ = lean_box(0);
v___x_4186_ = lean_box(2);
v___f_4187_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4188_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4189_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4190_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4191_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4192_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4193_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_4193_, 0, v___x_4192_);
lean_ctor_set(v___x_4193_, 1, v___x_4191_);
lean_ctor_set(v___x_4193_, 2, v___x_4190_);
lean_ctor_set(v___x_4193_, 3, v___x_4189_);
lean_ctor_set(v___x_4193_, 4, v___f_4188_);
lean_ctor_set(v___x_4193_, 5, v___f_4187_);
lean_ctor_set(v___x_4193_, 6, v___x_4186_);
lean_ctor_set(v___x_4193_, 7, v___x_4185_);
lean_ctor_set_uint8(v___x_4193_, sizeof(void*)*8, v___x_4184_);
lean_ctor_set_uint8(v___x_4193_, sizeof(void*)*8 + 1, v___x_4184_);
return v___x_4193_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___f_4194_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4195_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4195_);
lean_ctor_set(v___x_4196_, 1, v___f_4194_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4198_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4199_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4198_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4202_){
_start:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; uint8_t v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4204_ = l_Lean_attributeMapRef;
v___x_4205_ = lean_st_ref_get(v___x_4204_);
v___x_4206_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4205_, v_n_4202_);
lean_dec(v___x_4205_);
v___x_4207_ = lean_box(v___x_4206_);
v___x_4208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4207_);
return v___x_4208_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4209_, lean_object* v_a_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l_Lean_isBuiltinAttribute(v_n_4209_);
lean_dec(v_n_4209_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4212_, lean_object* v_x_4213_){
_start:
{
if (lean_obj_tag(v_x_4213_) == 0)
{
return v_x_4212_;
}
else
{
lean_object* v_key_4214_; lean_object* v_tail_4215_; lean_object* v___x_4216_; 
v_key_4214_ = lean_ctor_get(v_x_4213_, 0);
v_tail_4215_ = lean_ctor_get(v_x_4213_, 2);
lean_inc(v_key_4214_);
v___x_4216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4216_, 0, v_key_4214_);
lean_ctor_set(v___x_4216_, 1, v_x_4212_);
v_x_4212_ = v___x_4216_;
v_x_4213_ = v_tail_4215_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4218_, lean_object* v_x_4219_){
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4218_, v_x_4219_);
lean_dec(v_x_4219_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4221_, size_t v_i_4222_, size_t v_stop_4223_, lean_object* v_b_4224_){
_start:
{
uint8_t v___x_4225_; 
v___x_4225_ = lean_usize_dec_eq(v_i_4222_, v_stop_4223_);
if (v___x_4225_ == 0)
{
lean_object* v___x_4226_; lean_object* v___x_4227_; size_t v___x_4228_; size_t v___x_4229_; 
v___x_4226_ = lean_array_uget_borrowed(v_as_4221_, v_i_4222_);
v___x_4227_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4224_, v___x_4226_);
v___x_4228_ = ((size_t)1ULL);
v___x_4229_ = lean_usize_add(v_i_4222_, v___x_4228_);
v_i_4222_ = v___x_4229_;
v_b_4224_ = v___x_4227_;
goto _start;
}
else
{
return v_b_4224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4231_, lean_object* v_i_4232_, lean_object* v_stop_4233_, lean_object* v_b_4234_){
_start:
{
size_t v_i_boxed_4235_; size_t v_stop_boxed_4236_; lean_object* v_res_4237_; 
v_i_boxed_4235_ = lean_unbox_usize(v_i_4232_);
lean_dec(v_i_4232_);
v_stop_boxed_4236_ = lean_unbox_usize(v_stop_4233_);
lean_dec(v_stop_4233_);
v_res_4237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4231_, v_i_boxed_4235_, v_stop_boxed_4236_, v_b_4234_);
lean_dec_ref(v_as_4231_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v_buckets_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; uint8_t v___x_4245_; 
v___x_4239_ = l_Lean_attributeMapRef;
v___x_4240_ = lean_st_ref_get(v___x_4239_);
v_buckets_4241_ = lean_ctor_get(v___x_4240_, 1);
lean_inc_ref(v_buckets_4241_);
lean_dec(v___x_4240_);
v___x_4242_ = lean_box(0);
v___x_4243_ = lean_unsigned_to_nat(0u);
v___x_4244_ = lean_array_get_size(v_buckets_4241_);
v___x_4245_ = lean_nat_dec_lt(v___x_4243_, v___x_4244_);
if (v___x_4245_ == 0)
{
lean_object* v___x_4246_; 
lean_dec_ref(v_buckets_4241_);
v___x_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4242_);
return v___x_4246_;
}
else
{
size_t v___x_4247_; size_t v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4247_ = ((size_t)0ULL);
v___x_4248_ = lean_usize_of_nat(v___x_4244_);
v___x_4249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4241_, v___x_4247_, v___x_4248_, v___x_4242_);
lean_dec_ref(v_buckets_4241_);
v___x_4250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4249_);
return v___x_4250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = l_Lean_getBuiltinAttributeNames();
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4254_){
_start:
{
lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
v___x_4256_ = l_Lean_attributeMapRef;
v___x_4257_ = lean_st_ref_get(v___x_4256_);
v___x_4258_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4257_, v_attrName_4254_);
lean_dec(v___x_4257_);
if (lean_obj_tag(v___x_4258_) == 0)
{
lean_object* v___x_4259_; uint8_t v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4259_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4260_ = 1;
v___x_4261_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4254_, v___x_4260_);
v___x_4262_ = lean_string_append(v___x_4259_, v___x_4261_);
lean_dec_ref(v___x_4261_);
v___x_4263_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4264_ = lean_string_append(v___x_4262_, v___x_4263_);
v___x_4265_ = lean_mk_io_user_error(v___x_4264_);
v___x_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4266_, 0, v___x_4265_);
return v___x_4266_;
}
else
{
lean_object* v_val_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4274_; 
lean_dec(v_attrName_4254_);
v_val_4267_ = lean_ctor_get(v___x_4258_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4258_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4269_ = v___x_4258_;
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_val_4267_);
lean_dec(v___x_4258_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4272_; 
if (v_isShared_4270_ == 0)
{
lean_ctor_set_tag(v___x_4269_, 0);
v___x_4272_ = v___x_4269_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_val_4267_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4275_, lean_object* v_a_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4275_);
return v_res_4277_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4278_, lean_object* v_attrName_4279_){
_start:
{
lean_object* v___x_4280_; lean_object* v_toEnvExtension_4281_; lean_object* v_asyncMode_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; uint8_t v___x_4285_; lean_object* v___x_4286_; lean_object* v_map_4287_; uint8_t v___x_4288_; 
v___x_4280_ = l_Lean_attributeExtension;
v_toEnvExtension_4281_ = lean_ctor_get(v___x_4280_, 0);
v_asyncMode_4282_ = lean_ctor_get(v_toEnvExtension_4281_, 2);
v___x_4283_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4284_ = lean_box(0);
v___x_4285_ = 0;
v___x_4286_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4283_, v___x_4280_, v_env_4278_, v_asyncMode_4282_, v___x_4284_, v___x_4285_);
v_map_4287_ = lean_ctor_get(v___x_4286_, 1);
lean_inc_ref(v_map_4287_);
lean_dec(v___x_4286_);
v___x_4288_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4287_, v_attrName_4279_);
lean_dec_ref(v_map_4287_);
return v___x_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4289_, lean_object* v_attrName_4290_){
_start:
{
uint8_t v_res_4291_; lean_object* v_r_4292_; 
v_res_4291_ = l_Lean_isAttribute(v_env_4289_, v_attrName_4290_);
lean_dec(v_attrName_4290_);
v_r_4292_ = lean_box(v_res_4291_);
return v_r_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4293_){
_start:
{
lean_object* v___x_4294_; lean_object* v_toEnvExtension_4295_; lean_object* v_asyncMode_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; uint8_t v___x_4299_; lean_object* v___x_4300_; lean_object* v_map_4301_; lean_object* v_buckets_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; uint8_t v___x_4306_; 
v___x_4294_ = l_Lean_attributeExtension;
v_toEnvExtension_4295_ = lean_ctor_get(v___x_4294_, 0);
v_asyncMode_4296_ = lean_ctor_get(v_toEnvExtension_4295_, 2);
v___x_4297_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4298_ = lean_box(0);
v___x_4299_ = 0;
v___x_4300_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4297_, v___x_4294_, v_env_4293_, v_asyncMode_4296_, v___x_4298_, v___x_4299_);
v_map_4301_ = lean_ctor_get(v___x_4300_, 1);
lean_inc_ref(v_map_4301_);
lean_dec(v___x_4300_);
v_buckets_4302_ = lean_ctor_get(v_map_4301_, 1);
lean_inc_ref(v_buckets_4302_);
lean_dec_ref(v_map_4301_);
v___x_4303_ = lean_box(0);
v___x_4304_ = lean_unsigned_to_nat(0u);
v___x_4305_ = lean_array_get_size(v_buckets_4302_);
v___x_4306_ = lean_nat_dec_lt(v___x_4304_, v___x_4305_);
if (v___x_4306_ == 0)
{
lean_dec_ref(v_buckets_4302_);
return v___x_4303_;
}
else
{
size_t v___x_4307_; size_t v___x_4308_; lean_object* v___x_4309_; 
v___x_4307_ = ((size_t)0ULL);
v___x_4308_ = lean_usize_of_nat(v___x_4305_);
v___x_4309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4302_, v___x_4307_, v___x_4308_, v___x_4303_);
lean_dec_ref(v_buckets_4302_);
return v___x_4309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4310_, lean_object* v_attrName_4311_){
_start:
{
lean_object* v___x_4312_; lean_object* v_toEnvExtension_4313_; lean_object* v_asyncMode_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; uint8_t v___x_4317_; lean_object* v___x_4318_; lean_object* v_map_4319_; lean_object* v___x_4320_; 
v___x_4312_ = l_Lean_attributeExtension;
v_toEnvExtension_4313_ = lean_ctor_get(v___x_4312_, 0);
v_asyncMode_4314_ = lean_ctor_get(v_toEnvExtension_4313_, 2);
v___x_4315_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4316_ = lean_box(0);
v___x_4317_ = 0;
v___x_4318_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4315_, v___x_4312_, v_env_4310_, v_asyncMode_4314_, v___x_4316_, v___x_4317_);
v_map_4319_ = lean_ctor_get(v___x_4318_, 1);
lean_inc_ref(v_map_4319_);
lean_dec(v___x_4318_);
v___x_4320_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4319_, v_attrName_4311_);
lean_dec_ref(v_map_4319_);
if (lean_obj_tag(v___x_4320_) == 0)
{
lean_object* v___x_4321_; uint8_t v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4321_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4322_ = 1;
v___x_4323_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4311_, v___x_4322_);
v___x_4324_ = lean_string_append(v___x_4321_, v___x_4323_);
lean_dec_ref(v___x_4323_);
v___x_4325_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4326_ = lean_string_append(v___x_4324_, v___x_4325_);
v___x_4327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4326_);
return v___x_4327_;
}
else
{
lean_object* v_val_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
lean_dec(v_attrName_4311_);
v_val_4328_ = lean_ctor_get(v___x_4320_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4320_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___x_4320_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_val_4328_);
lean_dec(v___x_4320_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4333_; 
if (v_isShared_4331_ == 0)
{
v___x_4333_ = v___x_4330_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_val_4328_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___lam__0(lean_object* v_addEntryFn_4336_, lean_object* v___x_4337_, lean_object* v_s_4338_){
_start:
{
lean_object* v_importedEntries_4339_; lean_object* v_state_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4348_; 
v_importedEntries_4339_ = lean_ctor_get(v_s_4338_, 0);
v_state_4340_ = lean_ctor_get(v_s_4338_, 1);
v_isSharedCheck_4348_ = !lean_is_exclusive(v_s_4338_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4342_ = v_s_4338_;
v_isShared_4343_ = v_isSharedCheck_4348_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_state_4340_);
lean_inc(v_importedEntries_4339_);
lean_dec(v_s_4338_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4348_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v_state_4344_; lean_object* v___x_4346_; 
v_state_4344_ = lean_apply_2(v_addEntryFn_4336_, v_state_4340_, v___x_4337_);
if (v_isShared_4343_ == 0)
{
lean_ctor_set(v___x_4342_, 1, v_state_4344_);
v___x_4346_ = v___x_4342_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_importedEntries_4339_);
lean_ctor_set(v_reuseFailAlloc_4347_, 1, v_state_4344_);
v___x_4346_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
return v___x_4346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4349_, lean_object* v_builderId_4350_, lean_object* v_ref_4351_, lean_object* v_args_4352_){
_start:
{
lean_object* v_entry_4354_; lean_object* v___x_4355_; 
v_entry_4354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4354_, 0, v_builderId_4350_);
lean_ctor_set(v_entry_4354_, 1, v_ref_4351_);
lean_ctor_set(v_entry_4354_, 2, v_args_4352_);
lean_inc_ref(v_entry_4354_);
v___x_4355_ = l_Lean_mkAttributeImplOfEntry(v_entry_4354_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4390_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4358_ = v___x_4355_;
v_isShared_4359_ = v_isSharedCheck_4390_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___x_4355_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4390_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v_toAttributeImplCore_4360_; lean_object* v_name_4361_; uint8_t v___x_4362_; 
v_toAttributeImplCore_4360_ = lean_ctor_get(v_a_4356_, 0);
v_name_4361_ = lean_ctor_get(v_toAttributeImplCore_4360_, 1);
lean_inc_ref(v_env_4349_);
v___x_4362_ = l_Lean_isAttribute(v_env_4349_, v_name_4361_);
if (v___x_4362_ == 0)
{
lean_object* v___x_4363_; lean_object* v_toEnvExtension_4364_; lean_object* v_addEntryFn_4365_; lean_object* v_asyncMode_4366_; uint8_t v_logWrites_4367_; lean_object* v___x_4368_; lean_object* v___f_4369_; lean_object* v___x_4370_; uint8_t v___x_4371_; 
v___x_4363_ = l_Lean_attributeExtension;
v_toEnvExtension_4364_ = lean_ctor_get(v___x_4363_, 0);
v_addEntryFn_4365_ = lean_ctor_get(v___x_4363_, 3);
v_asyncMode_4366_ = lean_ctor_get(v_toEnvExtension_4364_, 2);
v_logWrites_4367_ = lean_ctor_get_uint8(v_toEnvExtension_4364_, sizeof(void*)*6);
v___x_4368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4368_, 0, v_entry_4354_);
lean_ctor_set(v___x_4368_, 1, v_a_4356_);
lean_inc(v_addEntryFn_4365_);
v___f_4369_ = lean_alloc_closure((void*)(l_Lean_registerAttributeOfBuilder___lam__0), 3, 2);
lean_closure_set(v___f_4369_, 0, v_addEntryFn_4365_);
lean_closure_set(v___f_4369_, 1, v___x_4368_);
v___x_4370_ = lean_box(0);
v___x_4371_ = 1;
if (v_logWrites_4367_ == 0)
{
lean_object* v___x_4372_; lean_object* v___x_4374_; 
lean_inc_ref(v_toEnvExtension_4364_);
v___x_4372_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4364_, v_env_4349_, v___f_4369_, v_asyncMode_4366_, v___x_4370_, v___x_4371_);
if (v_isShared_4359_ == 0)
{
lean_ctor_set(v___x_4358_, 0, v___x_4372_);
v___x_4374_ = v___x_4358_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v___x_4372_);
v___x_4374_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
return v___x_4374_;
}
}
else
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4379_; 
lean_inc_ref_n(v_toEnvExtension_4364_, 2);
v___x_4376_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4364_, v_env_4349_);
lean_dec_ref(v_env_4349_);
v___x_4377_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4364_, v___x_4376_, v___f_4369_, v_asyncMode_4366_, v___x_4370_, v___x_4371_);
if (v_isShared_4359_ == 0)
{
lean_ctor_set(v___x_4358_, 0, v___x_4377_);
v___x_4379_ = v___x_4358_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v___x_4377_);
v___x_4379_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
return v___x_4379_;
}
}
}
else
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4388_; 
lean_inc(v_name_4361_);
lean_dec(v_a_4356_);
lean_dec_ref_known(v_entry_4354_, 3);
lean_dec_ref(v_env_4349_);
v___x_4381_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4382_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4361_, v___x_4362_);
v___x_4383_ = lean_string_append(v___x_4381_, v___x_4382_);
lean_dec_ref(v___x_4382_);
v___x_4384_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4385_ = lean_string_append(v___x_4383_, v___x_4384_);
v___x_4386_ = lean_mk_io_user_error(v___x_4385_);
if (v_isShared_4359_ == 0)
{
lean_ctor_set_tag(v___x_4358_, 1);
lean_ctor_set(v___x_4358_, 0, v___x_4386_);
v___x_4388_ = v___x_4358_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v___x_4386_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
}
else
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4398_; 
lean_dec_ref_known(v_entry_4354_, 3);
lean_dec_ref(v_env_4349_);
v_a_4391_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4393_ = v___x_4355_;
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4355_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4396_; 
if (v_isShared_4394_ == 0)
{
v___x_4396_ = v___x_4393_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4391_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4399_, lean_object* v_builderId_4400_, lean_object* v_ref_4401_, lean_object* v_args_4402_, lean_object* v_a_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l_Lean_registerAttributeOfBuilder(v_env_4399_, v_builderId_4400_, v_ref_4401_, v_args_4402_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
if (lean_obj_tag(v_x_4405_) == 0)
{
lean_object* v_a_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v_a_4409_ = lean_ctor_get(v_x_4405_, 0);
lean_inc(v_a_4409_);
lean_dec_ref_known(v_x_4405_, 1);
v___x_4410_ = l_Lean_stringToMessageData(v_a_4409_);
v___x_4411_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4410_, v___y_4406_, v___y_4407_);
return v___x_4411_;
}
else
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
v_a_4412_ = lean_ctor_get(v_x_4405_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v_x_4405_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v_x_4405_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v_x_4405_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4417_; 
if (v_isShared_4415_ == 0)
{
lean_ctor_set_tag(v___x_4414_, 0);
v___x_4417_ = v___x_4414_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4412_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_){
_start:
{
lean_object* v_res_4424_; 
v_res_4424_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4420_, v___y_4421_, v___y_4422_);
lean_dec(v___y_4422_);
lean_dec_ref(v___y_4421_);
return v_res_4424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4425_, lean_object* v_attrName_4426_, lean_object* v_stx_4427_, uint8_t v_kind_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_){
_start:
{
lean_object* v___x_4432_; lean_object* v_env_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___x_4432_ = lean_st_ref_get(v_a_4430_);
v_env_4433_ = lean_ctor_get(v___x_4432_, 0);
lean_inc_ref(v_env_4433_);
lean_dec(v___x_4432_);
v___x_4434_ = l_Lean_getAttributeImpl(v_env_4433_, v_attrName_4426_);
v___x_4435_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4434_, v_a_4429_, v_a_4430_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v_a_4436_; lean_object* v_add_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
lean_inc(v_a_4436_);
lean_dec_ref_known(v___x_4435_, 1);
v_add_4437_ = lean_ctor_get(v_a_4436_, 1);
lean_inc_ref(v_add_4437_);
lean_dec(v_a_4436_);
v___x_4438_ = lean_box(v_kind_4428_);
lean_inc(v_a_4430_);
lean_inc_ref(v_a_4429_);
v___x_4439_ = lean_apply_6(v_add_4437_, v_declName_4425_, v_stx_4427_, v___x_4438_, v_a_4429_, v_a_4430_, lean_box(0));
return v___x_4439_;
}
else
{
lean_object* v_a_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4447_; 
lean_dec(v_stx_4427_);
lean_dec(v_declName_4425_);
v_a_4440_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_4442_ = v___x_4435_;
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_a_4440_);
lean_dec(v___x_4435_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4445_; 
if (v_isShared_4443_ == 0)
{
v___x_4445_ = v___x_4442_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_a_4440_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4448_, lean_object* v_attrName_4449_, lean_object* v_stx_4450_, lean_object* v_kind_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_){
_start:
{
uint8_t v_kind_boxed_4455_; lean_object* v_res_4456_; 
v_kind_boxed_4455_ = lean_unbox(v_kind_4451_);
v_res_4456_ = l_Lean_Attribute_add(v_declName_4448_, v_attrName_4449_, v_stx_4450_, v_kind_boxed_4455_, v_a_4452_, v_a_4453_);
lean_dec(v_a_4453_);
lean_dec_ref(v_a_4452_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4457_, lean_object* v_x_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
lean_object* v___x_4462_; 
v___x_4462_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4458_, v___y_4459_, v___y_4460_);
return v___x_4462_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4463_, lean_object* v_x_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
lean_object* v_res_4468_; 
v_res_4468_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4463_, v_x_4464_, v___y_4465_, v___y_4466_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4469_, lean_object* v_attrName_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_){
_start:
{
lean_object* v___x_4474_; lean_object* v_env_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4474_ = lean_st_ref_get(v_a_4472_);
v_env_4475_ = lean_ctor_get(v___x_4474_, 0);
lean_inc_ref(v_env_4475_);
lean_dec(v___x_4474_);
v___x_4476_ = l_Lean_getAttributeImpl(v_env_4475_, v_attrName_4470_);
v___x_4477_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4476_, v_a_4471_, v_a_4472_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_a_4478_; lean_object* v_erase_4479_; lean_object* v___x_4480_; 
v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
lean_inc(v_a_4478_);
lean_dec_ref_known(v___x_4477_, 1);
v_erase_4479_ = lean_ctor_get(v_a_4478_, 2);
lean_inc_ref(v_erase_4479_);
lean_dec(v_a_4478_);
lean_inc(v_a_4472_);
lean_inc_ref(v_a_4471_);
v___x_4480_ = lean_apply_4(v_erase_4479_, v_declName_4469_, v_a_4471_, v_a_4472_, lean_box(0));
return v___x_4480_;
}
else
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
lean_dec(v_declName_4469_);
v_a_4481_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4483_ = v___x_4477_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4477_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
if (v_isShared_4484_ == 0)
{
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_a_4481_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4489_, lean_object* v_attrName_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_){
_start:
{
lean_object* v_res_4494_; 
v_res_4494_ = l_Lean_Attribute_erase(v_declName_4489_, v_attrName_4490_, v_a_4491_, v_a_4492_);
lean_dec(v_a_4492_);
lean_dec_ref(v_a_4491_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___lam__0(lean_object* v___y_4495_, lean_object* v_ps_4496_){
_start:
{
lean_object* v_importedEntries_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4504_; 
v_importedEntries_4497_ = lean_ctor_get(v_ps_4496_, 0);
v_isSharedCheck_4504_ = !lean_is_exclusive(v_ps_4496_);
if (v_isSharedCheck_4504_ == 0)
{
lean_object* v_unused_4505_; 
v_unused_4505_ = lean_ctor_get(v_ps_4496_, 1);
lean_dec(v_unused_4505_);
v___x_4499_ = v_ps_4496_;
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_importedEntries_4497_);
lean_dec(v_ps_4496_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4502_; 
if (v_isShared_4500_ == 0)
{
lean_ctor_set(v___x_4499_, 1, v___y_4495_);
v___x_4502_ = v___x_4499_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_importedEntries_4497_);
lean_ctor_set(v_reuseFailAlloc_4503_, 1, v___y_4495_);
v___x_4502_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
return v___x_4502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4506_, lean_object* v_x_4507_){
_start:
{
if (lean_obj_tag(v_x_4507_) == 0)
{
return v_x_4506_;
}
else
{
lean_object* v_key_4508_; lean_object* v_value_4509_; lean_object* v_tail_4510_; lean_object* v_newEntries_4511_; lean_object* v_map_4512_; uint8_t v___x_4513_; 
v_key_4508_ = lean_ctor_get(v_x_4507_, 0);
lean_inc(v_key_4508_);
v_value_4509_ = lean_ctor_get(v_x_4507_, 1);
lean_inc(v_value_4509_);
v_tail_4510_ = lean_ctor_get(v_x_4507_, 2);
lean_inc(v_tail_4510_);
lean_dec_ref_known(v_x_4507_, 3);
v_newEntries_4511_ = lean_ctor_get(v_x_4506_, 0);
v_map_4512_ = lean_ctor_get(v_x_4506_, 1);
v___x_4513_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4512_, v_key_4508_);
if (v___x_4513_ == 0)
{
lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4522_; 
lean_inc_ref(v_map_4512_);
lean_inc(v_newEntries_4511_);
v_isSharedCheck_4522_ = !lean_is_exclusive(v_x_4506_);
if (v_isSharedCheck_4522_ == 0)
{
lean_object* v_unused_4523_; lean_object* v_unused_4524_; 
v_unused_4523_ = lean_ctor_get(v_x_4506_, 1);
lean_dec(v_unused_4523_);
v_unused_4524_ = lean_ctor_get(v_x_4506_, 0);
lean_dec(v_unused_4524_);
v___x_4515_ = v_x_4506_;
v_isShared_4516_ = v_isSharedCheck_4522_;
goto v_resetjp_4514_;
}
else
{
lean_dec(v_x_4506_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4522_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4517_; lean_object* v___x_4519_; 
v___x_4517_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4512_, v_key_4508_, v_value_4509_);
if (v_isShared_4516_ == 0)
{
lean_ctor_set(v___x_4515_, 1, v___x_4517_);
v___x_4519_ = v___x_4515_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_newEntries_4511_);
lean_ctor_set(v_reuseFailAlloc_4521_, 1, v___x_4517_);
v___x_4519_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
v_x_4506_ = v___x_4519_;
v_x_4507_ = v_tail_4510_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4509_);
lean_dec(v_key_4508_);
v_x_4507_ = v_tail_4510_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4526_, size_t v_i_4527_, size_t v_stop_4528_, lean_object* v_b_4529_){
_start:
{
uint8_t v___x_4530_; 
v___x_4530_ = lean_usize_dec_eq(v_i_4527_, v_stop_4528_);
if (v___x_4530_ == 0)
{
lean_object* v___x_4531_; lean_object* v___x_4532_; size_t v___x_4533_; size_t v___x_4534_; 
v___x_4531_ = lean_array_uget_borrowed(v_as_4526_, v_i_4527_);
lean_inc(v___x_4531_);
v___x_4532_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4529_, v___x_4531_);
v___x_4533_ = ((size_t)1ULL);
v___x_4534_ = lean_usize_add(v_i_4527_, v___x_4533_);
v_i_4527_ = v___x_4534_;
v_b_4529_ = v___x_4532_;
goto _start;
}
else
{
return v_b_4529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4536_, lean_object* v_i_4537_, lean_object* v_stop_4538_, lean_object* v_b_4539_){
_start:
{
size_t v_i_boxed_4540_; size_t v_stop_boxed_4541_; lean_object* v_res_4542_; 
v_i_boxed_4540_ = lean_unbox_usize(v_i_4537_);
lean_dec(v_i_4537_);
v_stop_boxed_4541_ = lean_unbox_usize(v_stop_4538_);
lean_dec(v_stop_4538_);
v_res_4542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4536_, v_i_boxed_4540_, v_stop_boxed_4541_, v_b_4539_);
lean_dec_ref(v_as_4536_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4543_){
_start:
{
lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v_toEnvExtension_4549_; lean_object* v_asyncMode_4550_; uint8_t v_logWrites_4551_; lean_object* v___y_4553_; lean_object* v_buckets_4562_; lean_object* v___x_4563_; uint8_t v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; uint8_t v___x_4568_; 
v___x_4545_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4546_ = l_Lean_attributeMapRef;
v___x_4547_ = lean_st_ref_get(v___x_4546_);
v___x_4548_ = l_Lean_attributeExtension;
v_toEnvExtension_4549_ = lean_ctor_get(v___x_4548_, 0);
v_asyncMode_4550_ = lean_ctor_get(v_toEnvExtension_4549_, 2);
v_logWrites_4551_ = lean_ctor_get_uint8(v_toEnvExtension_4549_, sizeof(void*)*6);
v_buckets_4562_ = lean_ctor_get(v___x_4547_, 1);
lean_inc_ref(v_buckets_4562_);
lean_dec(v___x_4547_);
v___x_4563_ = lean_box(0);
v___x_4564_ = 0;
lean_inc_ref(v_env_4543_);
v___x_4565_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4545_, v___x_4548_, v_env_4543_, v_asyncMode_4550_, v___x_4563_, v___x_4564_);
v___x_4566_ = lean_unsigned_to_nat(0u);
v___x_4567_ = lean_array_get_size(v_buckets_4562_);
v___x_4568_ = lean_nat_dec_lt(v___x_4566_, v___x_4567_);
if (v___x_4568_ == 0)
{
lean_dec_ref(v_buckets_4562_);
v___y_4553_ = v___x_4565_;
goto v___jp_4552_;
}
else
{
size_t v___x_4569_; size_t v___x_4570_; lean_object* v___x_4571_; 
v___x_4569_ = ((size_t)0ULL);
v___x_4570_ = lean_usize_of_nat(v___x_4567_);
v___x_4571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4562_, v___x_4569_, v___x_4570_, v___x_4565_);
lean_dec_ref(v_buckets_4562_);
v___y_4553_ = v___x_4571_;
goto v___jp_4552_;
}
v___jp_4552_:
{
lean_object* v___f_4554_; lean_object* v___x_4555_; uint8_t v___x_4556_; 
v___f_4554_ = lean_alloc_closure((void*)(l_Lean_updateEnvAttributesImpl___lam__0), 2, 1);
lean_closure_set(v___f_4554_, 0, v___y_4553_);
v___x_4555_ = lean_box(0);
v___x_4556_ = 1;
if (v_logWrites_4551_ == 0)
{
lean_object* v___x_4557_; lean_object* v___x_4558_; 
lean_inc_ref(v_toEnvExtension_4549_);
v___x_4557_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4549_, v_env_4543_, v___f_4554_, v_asyncMode_4550_, v___x_4555_, v___x_4556_);
v___x_4558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4557_);
return v___x_4558_;
}
else
{
lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; 
lean_inc_ref_n(v_toEnvExtension_4549_, 2);
v___x_4559_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4549_, v_env_4543_);
lean_dec_ref(v_env_4543_);
v___x_4560_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4549_, v___x_4559_, v___f_4554_, v_asyncMode_4550_, v___x_4555_, v___x_4556_);
v___x_4561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4560_);
return v___x_4561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4572_, lean_object* v_a_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = lean_update_env_attributes(v_env_4572_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v_size_4578_; lean_object* v___x_4579_; 
v___x_4576_ = l_Lean_attributeMapRef;
v___x_4577_ = lean_st_ref_get(v___x_4576_);
v_size_4578_ = lean_ctor_get(v___x_4577_, 0);
lean_inc(v_size_4578_);
lean_dec(v___x_4577_);
v___x_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4579_, 0, v_size_4578_);
return v___x_4579_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = lean_get_num_attributes();
return v_res_4581_;
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
res = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_1429509408____hygCtx___hyg_2_();
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
