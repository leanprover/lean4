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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
uint8_t v___y_1035__boxed_314_; lean_object* v_res_315_; 
v___y_1035__boxed_314_ = lean_unbox(v___y_310_);
v_res_315_ = l_Lean_instInhabitedAttributeImpl_default___lam__0(v_x_308_, v___y_309_, v___y_1035__boxed_314_, v___y_311_, v___y_312_);
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
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_319_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_320_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
lean_ctor_set(v___x_322_, 2, v___x_321_);
lean_ctor_set(v___x_322_, 3, v___x_321_);
lean_ctor_set(v___x_322_, 4, v___x_320_);
lean_ctor_set(v___x_322_, 5, v___x_320_);
lean_ctor_set(v___x_322_, 6, v___x_320_);
lean_ctor_set(v___x_322_, 7, v___x_320_);
lean_ctor_set(v___x_322_, 8, v___x_320_);
lean_ctor_set(v___x_322_, 9, v___x_320_);
lean_ctor_set(v___x_322_, 10, v___x_320_);
lean_ctor_set(v___x_322_, 11, v___x_319_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = lean_unsigned_to_nat(32u);
v___x_324_ = lean_mk_empty_array_with_capacity(v___x_323_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_326_ = ((size_t)5ULL);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_unsigned_to_nat(32u);
v___x_329_ = lean_mk_empty_array_with_capacity(v___x_328_);
v___x_330_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3);
v___x_331_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v___x_329_);
lean_ctor_set(v___x_331_, 2, v___x_327_);
lean_ctor_set(v___x_331_, 3, v___x_327_);
lean_ctor_set_usize(v___x_331_, 4, v___x_326_);
return v___x_331_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_332_ = lean_box(1);
v___x_333_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4);
v___x_334_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_333_);
lean_ctor_set(v___x_335_, 2, v___x_332_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(lean_object* v_msgData_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; lean_object* v_toCold_341_; lean_object* v_env_342_; lean_object* v_options_343_; uint8_t v___x_344_; lean_object* v_env_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_340_ = lean_st_ref_get(v___y_338_);
v_toCold_341_ = lean_ctor_get(v___y_337_, 0);
v_env_342_ = lean_ctor_get(v___x_340_, 0);
lean_inc_ref(v_env_342_);
lean_dec(v___x_340_);
v_options_343_ = lean_ctor_get(v_toCold_341_, 2);
v___x_344_ = 0;
v_env_345_ = l_Lean_Environment_setRecordingDeps(v_env_342_, v___x_344_);
v___x_346_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2);
v___x_347_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_343_);
v___x_348_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_348_, 0, v_env_345_);
lean_ctor_set(v___x_348_, 1, v___x_346_);
lean_ctor_set(v___x_348_, 2, v___x_347_);
lean_ctor_set(v___x_348_, 3, v_options_343_);
v___x_349_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v_msgData_336_);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___boxed(lean_object* v_msgData_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msgData_351_, v___y_352_, v___y_353_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(lean_object* v_msg_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_ref_360_; lean_object* v___x_361_; lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_370_; 
v_ref_360_ = lean_ctor_get(v___y_357_, 2);
v___x_361_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msg_356_, v___y_357_, v___y_358_);
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_370_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_368_; 
lean_inc(v_ref_360_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v_ref_360_);
lean_ctor_set(v___x_366_, 1, v_a_362_);
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 1);
lean_ctor_set(v___x_364_, 0, v___x_366_);
v___x_368_ = v___x_364_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg___boxed(lean_object* v_msg_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_371_, v___y_372_, v___y_373_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
return v_res_375_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0));
v___x_378_ = l_Lean_stringToMessageData(v___x_377_);
return v___x_378_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2));
v___x_381_ = l_Lean_stringToMessageData(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1(lean_object* v___x_382_, lean_object* v_decl_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_name_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_name_387_ = lean_ctor_get(v___x_382_, 1);
lean_inc(v_name_387_);
lean_dec_ref(v___x_382_);
v___x_388_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_389_ = l_Lean_MessageData_ofName(v_name_387_);
v___x_390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_388_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_390_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_392_, v___y_384_, v___y_385_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed(lean_object* v___x_394_, lean_object* v_decl_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_instInhabitedAttributeImpl_default___lam__1(v___x_394_, v_decl_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v_decl_395_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(lean_object* v_00_u03b1_408_, lean_object* v_msg_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_409_, v___y_410_, v___y_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___boxed(lean_object* v_00_u03b1_414_, lean_object* v_msg_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(v_00_u03b1_414_, v_msg_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
return v_res_419_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_421_ = lean_box(0);
v___x_422_ = lean_unsigned_to_nat(16u);
v___x_423_ = lean_mk_array(v___x_422_, v___x_421_);
return v___x_423_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v___x_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_429_ = lean_st_mk_ref(v___x_428_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
return v_res_432_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object* v_a_433_, lean_object* v_x_434_){
_start:
{
if (lean_obj_tag(v_x_434_) == 0)
{
uint8_t v___x_435_; 
v___x_435_ = 0;
return v___x_435_;
}
else
{
lean_object* v_key_436_; lean_object* v_tail_437_; uint8_t v___x_438_; 
v_key_436_ = lean_ctor_get(v_x_434_, 0);
v_tail_437_ = lean_ctor_get(v_x_434_, 2);
v___x_438_ = lean_name_eq(v_key_436_, v_a_433_);
if (v___x_438_ == 0)
{
v_x_434_ = v_tail_437_;
goto _start;
}
else
{
return v___x_438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg___boxed(lean_object* v_a_440_, lean_object* v_x_441_){
_start:
{
uint8_t v_res_442_; lean_object* v_r_443_; 
v_res_442_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_440_, v_x_441_);
lean_dec(v_x_441_);
lean_dec(v_a_440_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(lean_object* v_m_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_buckets_446_; lean_object* v___x_447_; uint64_t v___y_449_; 
v_buckets_446_ = lean_ctor_get(v_m_444_, 1);
v___x_447_ = lean_array_get_size(v_buckets_446_);
if (lean_obj_tag(v_a_445_) == 0)
{
uint64_t v___x_463_; 
v___x_463_ = 1723ULL;
v___y_449_ = v___x_463_;
goto v___jp_448_;
}
else
{
uint64_t v_hash_464_; 
v_hash_464_ = lean_ctor_get_uint64(v_a_445_, sizeof(void*)*2);
v___y_449_ = v_hash_464_;
goto v___jp_448_;
}
v___jp_448_:
{
uint64_t v___x_450_; uint64_t v___x_451_; uint64_t v_fold_452_; uint64_t v___x_453_; uint64_t v___x_454_; uint64_t v___x_455_; size_t v___x_456_; size_t v___x_457_; size_t v___x_458_; size_t v___x_459_; size_t v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_450_ = 32ULL;
v___x_451_ = lean_uint64_shift_right(v___y_449_, v___x_450_);
v_fold_452_ = lean_uint64_xor(v___y_449_, v___x_451_);
v___x_453_ = 16ULL;
v___x_454_ = lean_uint64_shift_right(v_fold_452_, v___x_453_);
v___x_455_ = lean_uint64_xor(v_fold_452_, v___x_454_);
v___x_456_ = lean_uint64_to_usize(v___x_455_);
v___x_457_ = lean_usize_of_nat(v___x_447_);
v___x_458_ = ((size_t)1ULL);
v___x_459_ = lean_usize_sub(v___x_457_, v___x_458_);
v___x_460_ = lean_usize_land(v___x_456_, v___x_459_);
v___x_461_ = lean_array_uget_borrowed(v_buckets_446_, v___x_460_);
v___x_462_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_445_, v___x_461_);
return v___x_462_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___boxed(lean_object* v_m_465_, lean_object* v_a_466_){
_start:
{
uint8_t v_res_467_; lean_object* v_r_468_; 
v_res_467_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_465_, v_a_466_);
lean_dec(v_a_466_);
lean_dec_ref(v_m_465_);
v_r_468_ = lean_box(v_res_467_);
return v_r_468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(lean_object* v_a_469_, lean_object* v_b_470_, lean_object* v_x_471_){
_start:
{
if (lean_obj_tag(v_x_471_) == 0)
{
lean_dec(v_b_470_);
lean_dec(v_a_469_);
return v_x_471_;
}
else
{
lean_object* v_key_472_; lean_object* v_value_473_; lean_object* v_tail_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_486_; 
v_key_472_ = lean_ctor_get(v_x_471_, 0);
v_value_473_ = lean_ctor_get(v_x_471_, 1);
v_tail_474_ = lean_ctor_get(v_x_471_, 2);
v_isSharedCheck_486_ = !lean_is_exclusive(v_x_471_);
if (v_isSharedCheck_486_ == 0)
{
v___x_476_ = v_x_471_;
v_isShared_477_ = v_isSharedCheck_486_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_tail_474_);
lean_inc(v_value_473_);
lean_inc(v_key_472_);
lean_dec(v_x_471_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_486_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
uint8_t v___x_478_; 
v___x_478_ = lean_name_eq(v_key_472_, v_a_469_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_479_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_469_, v_b_470_, v_tail_474_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 2, v___x_479_);
v___x_481_ = v___x_476_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_key_472_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_value_473_);
lean_ctor_set(v_reuseFailAlloc_482_, 2, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
else
{
lean_object* v___x_484_; 
lean_dec(v_value_473_);
lean_dec(v_key_472_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 1, v_b_470_);
lean_ctor_set(v___x_476_, 0, v_a_469_);
v___x_484_ = v___x_476_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_469_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_b_470_);
lean_ctor_set(v_reuseFailAlloc_485_, 2, v_tail_474_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_487_, lean_object* v_x_488_){
_start:
{
if (lean_obj_tag(v_x_488_) == 0)
{
return v_x_487_;
}
else
{
lean_object* v_key_489_; lean_object* v_value_490_; lean_object* v_tail_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_517_; 
v_key_489_ = lean_ctor_get(v_x_488_, 0);
v_value_490_ = lean_ctor_get(v_x_488_, 1);
v_tail_491_ = lean_ctor_get(v_x_488_, 2);
v_isSharedCheck_517_ = !lean_is_exclusive(v_x_488_);
if (v_isSharedCheck_517_ == 0)
{
v___x_493_ = v_x_488_;
v_isShared_494_ = v_isSharedCheck_517_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_tail_491_);
lean_inc(v_value_490_);
lean_inc(v_key_489_);
lean_dec(v_x_488_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_517_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; uint64_t v___y_497_; 
v___x_495_ = lean_array_get_size(v_x_487_);
if (lean_obj_tag(v_key_489_) == 0)
{
uint64_t v___x_515_; 
v___x_515_ = 1723ULL;
v___y_497_ = v___x_515_;
goto v___jp_496_;
}
else
{
uint64_t v_hash_516_; 
v_hash_516_ = lean_ctor_get_uint64(v_key_489_, sizeof(void*)*2);
v___y_497_ = v_hash_516_;
goto v___jp_496_;
}
v___jp_496_:
{
uint64_t v___x_498_; uint64_t v___x_499_; uint64_t v_fold_500_; uint64_t v___x_501_; uint64_t v___x_502_; uint64_t v___x_503_; size_t v___x_504_; size_t v___x_505_; size_t v___x_506_; size_t v___x_507_; size_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_498_ = 32ULL;
v___x_499_ = lean_uint64_shift_right(v___y_497_, v___x_498_);
v_fold_500_ = lean_uint64_xor(v___y_497_, v___x_499_);
v___x_501_ = 16ULL;
v___x_502_ = lean_uint64_shift_right(v_fold_500_, v___x_501_);
v___x_503_ = lean_uint64_xor(v_fold_500_, v___x_502_);
v___x_504_ = lean_uint64_to_usize(v___x_503_);
v___x_505_ = lean_usize_of_nat(v___x_495_);
v___x_506_ = ((size_t)1ULL);
v___x_507_ = lean_usize_sub(v___x_505_, v___x_506_);
v___x_508_ = lean_usize_land(v___x_504_, v___x_507_);
v___x_509_ = lean_array_uget_borrowed(v_x_487_, v___x_508_);
lean_inc(v___x_509_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 2, v___x_509_);
v___x_511_ = v___x_493_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_key_489_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_value_490_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v___x_509_);
v___x_511_ = v_reuseFailAlloc_514_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_512_; 
v___x_512_ = lean_array_uset(v_x_487_, v___x_508_, v___x_511_);
v_x_487_ = v___x_512_;
v_x_488_ = v_tail_491_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(lean_object* v_i_518_, lean_object* v_source_519_, lean_object* v_target_520_){
_start:
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = lean_array_get_size(v_source_519_);
v___x_522_ = lean_nat_dec_lt(v_i_518_, v___x_521_);
if (v___x_522_ == 0)
{
lean_dec_ref(v_source_519_);
lean_dec(v_i_518_);
return v_target_520_;
}
else
{
lean_object* v_es_523_; lean_object* v___x_524_; lean_object* v_source_525_; lean_object* v_target_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v_es_523_ = lean_array_fget(v_source_519_, v_i_518_);
v___x_524_ = lean_box(0);
v_source_525_ = lean_array_fset(v_source_519_, v_i_518_, v___x_524_);
v_target_526_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_target_520_, v_es_523_);
v___x_527_ = lean_unsigned_to_nat(1u);
v___x_528_ = lean_nat_add(v_i_518_, v___x_527_);
lean_dec(v_i_518_);
v_i_518_ = v___x_528_;
v_source_519_ = v_source_525_;
v_target_520_ = v_target_526_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(lean_object* v_data_530_){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v_nbuckets_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_531_ = lean_array_get_size(v_data_530_);
v___x_532_ = lean_unsigned_to_nat(2u);
v_nbuckets_533_ = lean_nat_mul(v___x_531_, v___x_532_);
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = lean_box(0);
v___x_536_ = lean_mk_array(v_nbuckets_533_, v___x_535_);
v___x_537_ = lean_array_propagate_mark(v_data_530_, v___x_536_);
v___x_538_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v___x_534_, v_data_530_, v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(lean_object* v_m_539_, lean_object* v_a_540_, lean_object* v_b_541_){
_start:
{
lean_object* v_size_542_; lean_object* v_buckets_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_589_; 
v_size_542_ = lean_ctor_get(v_m_539_, 0);
v_buckets_543_ = lean_ctor_get(v_m_539_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v_m_539_);
if (v_isSharedCheck_589_ == 0)
{
v___x_545_ = v_m_539_;
v_isShared_546_ = v_isSharedCheck_589_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_buckets_543_);
lean_inc(v_size_542_);
lean_dec(v_m_539_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_589_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; uint64_t v___y_549_; 
v___x_547_ = lean_array_get_size(v_buckets_543_);
if (lean_obj_tag(v_a_540_) == 0)
{
uint64_t v___x_587_; 
v___x_587_ = 1723ULL;
v___y_549_ = v___x_587_;
goto v___jp_548_;
}
else
{
uint64_t v_hash_588_; 
v_hash_588_ = lean_ctor_get_uint64(v_a_540_, sizeof(void*)*2);
v___y_549_ = v_hash_588_;
goto v___jp_548_;
}
v___jp_548_:
{
uint64_t v___x_550_; uint64_t v___x_551_; uint64_t v_fold_552_; uint64_t v___x_553_; uint64_t v___x_554_; uint64_t v___x_555_; size_t v___x_556_; size_t v___x_557_; size_t v___x_558_; size_t v___x_559_; size_t v___x_560_; lean_object* v_bkt_561_; uint8_t v___x_562_; 
v___x_550_ = 32ULL;
v___x_551_ = lean_uint64_shift_right(v___y_549_, v___x_550_);
v_fold_552_ = lean_uint64_xor(v___y_549_, v___x_551_);
v___x_553_ = 16ULL;
v___x_554_ = lean_uint64_shift_right(v_fold_552_, v___x_553_);
v___x_555_ = lean_uint64_xor(v_fold_552_, v___x_554_);
v___x_556_ = lean_uint64_to_usize(v___x_555_);
v___x_557_ = lean_usize_of_nat(v___x_547_);
v___x_558_ = ((size_t)1ULL);
v___x_559_ = lean_usize_sub(v___x_557_, v___x_558_);
v___x_560_ = lean_usize_land(v___x_556_, v___x_559_);
v_bkt_561_ = lean_array_uget_borrowed(v_buckets_543_, v___x_560_);
v___x_562_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_540_, v_bkt_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v_size_x27_564_; lean_object* v___x_565_; lean_object* v_buckets_x27_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_563_ = lean_unsigned_to_nat(1u);
v_size_x27_564_ = lean_nat_add(v_size_542_, v___x_563_);
lean_dec(v_size_542_);
lean_inc(v_bkt_561_);
v___x_565_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_565_, 0, v_a_540_);
lean_ctor_set(v___x_565_, 1, v_b_541_);
lean_ctor_set(v___x_565_, 2, v_bkt_561_);
v_buckets_x27_566_ = lean_array_uset(v_buckets_543_, v___x_560_, v___x_565_);
v___x_567_ = lean_unsigned_to_nat(4u);
v___x_568_ = lean_nat_mul(v_size_x27_564_, v___x_567_);
v___x_569_ = lean_unsigned_to_nat(3u);
v___x_570_ = lean_nat_div(v___x_568_, v___x_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_array_get_size(v_buckets_x27_566_);
v___x_572_ = lean_nat_dec_le(v___x_570_, v___x_571_);
lean_dec(v___x_570_);
if (v___x_572_ == 0)
{
lean_object* v_val_573_; lean_object* v___x_575_; 
v_val_573_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_buckets_x27_566_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 1, v_val_573_);
lean_ctor_set(v___x_545_, 0, v_size_x27_564_);
v___x_575_ = v___x_545_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_size_x27_564_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_val_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
else
{
lean_object* v___x_578_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 1, v_buckets_x27_566_);
lean_ctor_set(v___x_545_, 0, v_size_x27_564_);
v___x_578_ = v___x_545_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_size_x27_564_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_buckets_x27_566_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
else
{
lean_object* v___x_580_; lean_object* v_buckets_x27_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
lean_inc(v_bkt_561_);
v___x_580_ = lean_box(0);
v_buckets_x27_581_ = lean_array_uset(v_buckets_543_, v___x_560_, v___x_580_);
v___x_582_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_540_, v_b_541_, v_bkt_561_);
v___x_583_ = lean_array_uset(v_buckets_x27_581_, v___x_560_, v___x_582_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 1, v___x_583_);
v___x_585_ = v___x_545_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_size_542_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_registerBuiltinAttribute___closed__1(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__0));
v___x_592_ = lean_mk_io_user_error(v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute(lean_object* v_attr_595_){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v_toAttributeImplCore_599_; lean_object* v_name_600_; uint8_t v___x_601_; 
v___x_597_ = l_Lean_attributeMapRef;
v___x_598_ = lean_st_ref_get(v___x_597_);
v_toAttributeImplCore_599_ = lean_ctor_get(v_attr_595_, 0);
v_name_600_ = lean_ctor_get(v_toAttributeImplCore_599_, 1);
lean_inc(v_name_600_);
v___x_601_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_598_, v_name_600_);
lean_dec(v___x_598_);
if (v___x_601_ == 0)
{
uint8_t v___x_602_; 
v___x_602_ = l_Lean_initializing();
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec(v_name_600_);
lean_dec_ref(v_attr_595_);
v___x_603_ = lean_obj_once(&l_Lean_registerBuiltinAttribute___closed__1, &l_Lean_registerBuiltinAttribute___closed__1_once, _init_l_Lean_registerBuiltinAttribute___closed__1);
v___x_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_605_ = lean_st_ref_take(v___x_597_);
v___x_606_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_605_, v_name_600_, v_attr_595_);
v___x_607_ = lean_st_ref_put(v___x_597_, v___x_606_);
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
return v___x_608_;
}
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
lean_dec_ref(v_attr_595_);
v___x_609_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_610_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_600_, v___x_601_);
v___x_611_ = lean_string_append(v___x_609_, v___x_610_);
lean_dec_ref(v___x_610_);
v___x_612_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_613_ = lean_string_append(v___x_611_, v___x_612_);
v___x_614_ = lean_mk_io_user_error(v___x_613_);
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute___boxed(lean_object* v_attr_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_registerBuiltinAttribute(v_attr_616_);
return v_res_618_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(lean_object* v_00_u03b2_619_, lean_object* v_m_620_, lean_object* v_a_621_){
_start:
{
uint8_t v___x_622_; 
v___x_622_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_620_, v_a_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___boxed(lean_object* v_00_u03b2_623_, lean_object* v_m_624_, lean_object* v_a_625_){
_start:
{
uint8_t v_res_626_; lean_object* v_r_627_; 
v_res_626_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(v_00_u03b2_623_, v_m_624_, v_a_625_);
lean_dec(v_a_625_);
lean_dec_ref(v_m_624_);
v_r_627_ = lean_box(v_res_626_);
return v_r_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1(lean_object* v_00_u03b2_628_, lean_object* v_m_629_, lean_object* v_a_630_, lean_object* v_b_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_m_629_, v_a_630_, v_b_631_);
return v___x_632_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_object* v_00_u03b2_633_, lean_object* v_a_634_, lean_object* v_x_635_){
_start:
{
uint8_t v___x_636_; 
v___x_636_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_634_, v_x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___boxed(lean_object* v_00_u03b2_637_, lean_object* v_a_638_, lean_object* v_x_639_){
_start:
{
uint8_t v_res_640_; lean_object* v_r_641_; 
v_res_640_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(v_00_u03b2_637_, v_a_638_, v_x_639_);
lean_dec(v_x_639_);
lean_dec(v_a_638_);
v_r_641_ = lean_box(v_res_640_);
return v_r_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(lean_object* v_00_u03b2_642_, lean_object* v_data_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_data_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3(lean_object* v_00_u03b2_645_, lean_object* v_a_646_, lean_object* v_b_647_, lean_object* v_x_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_646_, v_b_647_, v_x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_650_, lean_object* v_i_651_, lean_object* v_source_652_, lean_object* v_target_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v_i_651_, v_source_652_, v_target_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_655_, lean_object* v_x_656_, lean_object* v_x_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_x_656_, v_x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object* v_ref_659_, lean_object* v_msg_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_toCold_664_; lean_object* v_currRecDepth_665_; lean_object* v_ref_666_; uint16_t v_optionFlags_667_; uint8_t v_suppressElabErrors_668_; uint8_t v_checkDeprecated_669_; uint8_t v_isRecordingDeps_670_; lean_object* v_ref_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_toCold_664_ = lean_ctor_get(v___y_661_, 0);
v_currRecDepth_665_ = lean_ctor_get(v___y_661_, 1);
v_ref_666_ = lean_ctor_get(v___y_661_, 2);
v_optionFlags_667_ = lean_ctor_get_uint16(v___y_661_, sizeof(void*)*3);
v_suppressElabErrors_668_ = lean_ctor_get_uint8(v___y_661_, sizeof(void*)*3 + 2);
v_checkDeprecated_669_ = lean_ctor_get_uint8(v___y_661_, sizeof(void*)*3 + 3);
v_isRecordingDeps_670_ = lean_ctor_get_uint8(v___y_661_, sizeof(void*)*3 + 4);
v_ref_671_ = l_Lean_replaceRef(v_ref_659_, v_ref_666_);
lean_inc(v_currRecDepth_665_);
lean_inc_ref(v_toCold_664_);
v___x_672_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_672_, 0, v_toCold_664_);
lean_ctor_set(v___x_672_, 1, v_currRecDepth_665_);
lean_ctor_set(v___x_672_, 2, v_ref_671_);
lean_ctor_set_uint16(v___x_672_, sizeof(void*)*3, v_optionFlags_667_);
lean_ctor_set_uint8(v___x_672_, sizeof(void*)*3 + 2, v_suppressElabErrors_668_);
lean_ctor_set_uint8(v___x_672_, sizeof(void*)*3 + 3, v_checkDeprecated_669_);
lean_ctor_set_uint8(v___x_672_, sizeof(void*)*3 + 4, v_isRecordingDeps_670_);
v___x_673_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_660_, v___x_672_, v___y_662_);
lean_dec_ref_known(v___x_672_, 3);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object* v_ref_674_, lean_object* v_msg_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_674_, v_msg_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v_ref_674_);
return v_res_679_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__3));
v___x_689_ = l_Lean_stringToMessageData(v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object* v_stx_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v___x_700_; lean_object* v___x_710_; uint8_t v___x_711_; 
lean_inc(v_stx_696_);
v___x_700_ = l_Lean_Syntax_getKind(v_stx_696_);
v___x_710_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_711_ = lean_name_eq(v___x_700_, v___x_710_);
if (v___x_711_ == 0)
{
goto v___jp_701_;
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = l_Lean_Syntax_getArg(v_stx_696_, v___x_712_);
v___x_714_ = l_Lean_Syntax_isNone(v___x_713_);
lean_dec(v___x_713_);
if (v___x_714_ == 0)
{
goto v___jp_701_;
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_715_ = lean_unsigned_to_nat(2u);
v___x_716_ = l_Lean_Syntax_getArg(v_stx_696_, v___x_715_);
v___x_717_ = l_Lean_Syntax_isNone(v___x_716_);
lean_dec(v___x_716_);
if (v___x_717_ == 0)
{
goto v___jp_701_;
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; 
lean_dec(v___x_700_);
lean_dec(v_stx_696_);
v___x_718_ = lean_box(0);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
}
}
v___jp_701_:
{
lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_702_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__2));
v___x_703_ = lean_name_eq(v___x_700_, v___x_702_);
lean_dec(v___x_700_);
if (v___x_703_ == 0)
{
if (lean_obj_tag(v_stx_696_) == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_box(0);
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
return v___x_705_;
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = lean_obj_once(&l_Lean_Attribute_Builtin_ensureNoArgs___closed__4, &l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once, _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4);
v___x_707_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_696_, v___x_706_, v_a_697_, v_a_698_);
lean_dec(v_stx_696_);
return v___x_707_;
}
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; 
lean_dec(v_stx_696_);
v___x_708_ = lean_box(0);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object* v_stx_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_720_, v_a_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object* v_00_u03b1_725_, lean_object* v_ref_726_, lean_object* v_msg_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_726_, v_msg_727_, v___y_728_, v___y_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object* v_00_u03b1_732_, lean_object* v_ref_733_, lean_object* v_msg_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(v_00_u03b1_732_, v_ref_733_, v_msg_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v_ref_733_);
return v_res_738_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__4));
v___x_753_ = l_Lean_stringToMessageData(v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object* v_stx_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
lean_inc(v_stx_754_);
v___x_766_ = l_Lean_Syntax_getKind(v_stx_754_);
v___x_767_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_768_ = lean_name_eq(v___x_766_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_769_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_770_ = lean_name_eq(v___x_766_, v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_771_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_772_ = lean_name_eq(v___x_766_, v___x_771_);
lean_dec(v___x_766_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_774_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_754_, v___x_773_, v_a_755_, v_a_756_);
lean_dec(v_stx_754_);
return v___x_774_;
}
else
{
goto v___jp_758_;
}
}
else
{
lean_dec(v___x_766_);
goto v___jp_758_;
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
lean_dec(v___x_766_);
v___x_775_ = lean_unsigned_to_nat(1u);
v___x_776_ = l_Lean_Syntax_getArg(v_stx_754_, v___x_775_);
lean_dec(v_stx_754_);
v___x_777_ = l_Lean_Syntax_isNone(v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = l_Lean_Syntax_getArg(v___x_776_, v___x_778_);
lean_dec(v___x_776_);
v___x_780_ = l_Lean_Syntax_isIdent(v___x_779_);
if (v___x_780_ == 0)
{
lean_dec(v___x_779_);
goto v___jp_763_;
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_779_);
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
}
else
{
lean_dec(v___x_776_);
goto v___jp_763_;
}
}
v___jp_758_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_759_ = lean_unsigned_to_nat(1u);
v___x_760_ = l_Lean_Syntax_getArg(v_stx_754_, v___x_759_);
lean_dec(v_stx_754_);
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
v___x_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
return v___x_762_;
}
v___jp_763_:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_box(0);
v___x_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object* v_stx_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_783_, v_a_784_, v_a_785_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
return v_res_787_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent___closed__1(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent___closed__0));
v___x_790_ = l_Lean_stringToMessageData(v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v___x_795_; 
lean_inc(v_stx_791_);
v___x_795_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_791_, v_a_792_, v_a_793_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_809_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_809_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_809_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_809_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
if (lean_obj_tag(v_a_796_) == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
lean_del_object(v___x_798_);
v___x_800_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent___closed__1, &l_Lean_Attribute_Builtin_getIdent___closed__1_once, _init_l_Lean_Attribute_Builtin_getIdent___closed__1);
lean_inc(v_stx_791_);
v___x_801_ = l_Lean_MessageData_ofSyntax(v_stx_791_);
v___x_802_ = l_Lean_indentD(v___x_801_);
v___x_803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_800_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_791_, v___x_803_, v_a_792_, v_a_793_);
lean_dec(v_stx_791_);
return v___x_804_;
}
else
{
lean_object* v_val_805_; lean_object* v___x_807_; 
lean_dec(v_stx_791_);
v_val_805_ = lean_ctor_get(v_a_796_, 0);
lean_inc(v_val_805_);
lean_dec_ref_known(v_a_796_, 1);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v_val_805_);
v___x_807_ = v___x_798_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_val_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec(v_stx_791_);
v_a_810_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_795_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_795_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Attribute_Builtin_getIdent(v_stx_818_, v_a_819_, v_a_820_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_823_, v_a_824_, v_a_825_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_848_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_848_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_848_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_848_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
if (lean_obj_tag(v_a_828_) == 0)
{
lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_832_ = lean_box(0);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_832_);
v___x_834_ = v___x_830_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
else
{
lean_object* v_val_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_847_; 
v_val_836_ = lean_ctor_get(v_a_828_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v_a_828_);
if (v_isSharedCheck_847_ == 0)
{
v___x_838_ = v_a_828_;
v_isShared_839_ = v_isSharedCheck_847_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_val_836_);
lean_dec(v_a_828_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_847_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_840_ = l_Lean_Syntax_getId(v_val_836_);
lean_dec(v_val_836_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_840_);
v___x_842_ = v___x_838_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_846_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_844_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_842_);
v___x_844_ = v___x_830_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
v_a_849_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_827_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_827_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_857_, v_a_858_, v_a_859_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_Attribute_Builtin_getIdent(v_stx_862_, v_a_863_, v_a_864_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_875_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_875_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_875_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_875_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_871_ = l_Lean_Syntax_getId(v_a_867_);
lean_dec(v_a_867_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_871_);
v___x_873_ = v___x_869_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
v_a_876_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_866_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_866_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_Attribute_Builtin_getId(v_stx_884_, v_a_885_, v_a_886_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
return v_res_888_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_891_ = l_Lean_stringToMessageData(v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
uint8_t v___x_896_; 
v___x_896_ = l_Lean_Syntax_isNone(v_optPrioStx_892_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = lean_unsigned_to_nat(0u);
v___x_898_ = l_Lean_Syntax_getArg(v_optPrioStx_892_, v___x_897_);
v___x_899_ = l_Lean_Syntax_isNatLit_x3f(v___x_898_);
lean_dec(v___x_898_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_900_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_892_);
v___x_901_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_892_);
v___x_902_ = l_Lean_indentD(v___x_901_);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_900_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_892_, v___x_903_, v_a_893_, v_a_894_);
lean_dec(v_optPrioStx_892_);
return v___x_904_;
}
else
{
lean_object* v_val_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec(v_optPrioStx_892_);
v_val_905_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_899_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_val_905_);
lean_dec(v___x_899_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set_tag(v___x_907_, 0);
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_val_905_);
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
else
{
lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec(v_optPrioStx_892_);
v___x_913_ = lean_unsigned_to_nat(1000u);
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object* v_optPrioStx_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_915_, v_a_916_, v_a_917_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
return v_res_919_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getPrio___closed__1(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = ((lean_object*)(l_Lean_Attribute_Builtin_getPrio___closed__0));
v___x_922_ = l_Lean_stringToMessageData(v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
lean_inc(v_stx_923_);
v___x_927_ = l_Lean_Syntax_getKind(v_stx_923_);
v___x_928_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_929_ = lean_name_eq(v___x_927_, v___x_928_);
lean_dec(v___x_927_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_930_ = lean_obj_once(&l_Lean_Attribute_Builtin_getPrio___closed__1, &l_Lean_Attribute_Builtin_getPrio___closed__1_once, _init_l_Lean_Attribute_Builtin_getPrio___closed__1);
lean_inc(v_stx_923_);
v___x_931_ = l_Lean_MessageData_ofSyntax(v_stx_923_);
v___x_932_ = l_Lean_indentD(v___x_931_);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_930_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_923_, v___x_933_, v_a_924_, v_a_925_);
lean_dec(v_stx_923_);
return v___x_934_;
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_935_ = lean_unsigned_to_nat(1u);
v___x_936_ = l_Lean_Syntax_getArg(v_stx_923_, v___x_935_);
lean_dec(v_stx_923_);
v___x_937_ = l_Lean_getAttrParamOptPrio(v___x_936_, v_a_924_, v_a_925_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Attribute_Builtin_getPrio(v_stx_938_, v_a_939_, v_a_940_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
return v_res_942_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_945_ = l_Lean_stringToMessageData(v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_948_ = l_Lean_stringToMessageData(v___x_947_);
return v___x_948_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_951_ = l_Lean_stringToMessageData(v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_952_, lean_object* v_inst_953_, lean_object* v_name_954_, uint8_t v_kind_955_){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___y_962_; 
v___x_956_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_957_ = l_Lean_MessageData_ofName(v_name_954_);
v___x_958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_956_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_958_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
switch(v_kind_955_)
{
case 0:
{
lean_object* v___x_969_; 
v___x_969_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_962_ = v___x_969_;
goto v___jp_961_;
}
case 1:
{
lean_object* v___x_970_; 
v___x_970_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_962_ = v___x_970_;
goto v___jp_961_;
}
default: 
{
lean_object* v___x_971_; 
v___x_971_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_962_ = v___x_971_;
goto v___jp_961_;
}
}
v___jp_961_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
lean_inc_ref(v___y_962_);
v___x_963_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_963_, 0, v___y_962_);
v___x_964_ = l_Lean_MessageData_ofFormat(v___x_963_);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_960_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = l_Lean_throwError___redArg(v_inst_952_, v_inst_953_, v___x_967_);
return v___x_968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_972_, lean_object* v_inst_973_, lean_object* v_name_974_, lean_object* v_kind_975_){
_start:
{
uint8_t v_kind_boxed_976_; lean_object* v_res_977_; 
v_kind_boxed_976_ = lean_unbox(v_kind_975_);
v_res_977_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_972_, v_inst_973_, v_name_974_, v_kind_boxed_976_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_978_, lean_object* v_inst_979_, lean_object* v_inst_980_, lean_object* v_00_u03b1_981_, lean_object* v_name_982_, uint8_t v_kind_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_979_, v_inst_980_, v_name_982_, v_kind_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_985_, lean_object* v_inst_986_, lean_object* v_inst_987_, lean_object* v_00_u03b1_988_, lean_object* v_name_989_, lean_object* v_kind_990_){
_start:
{
uint8_t v_kind_boxed_991_; lean_object* v_res_992_; 
v_kind_boxed_991_ = lean_unbox(v_kind_990_);
v_res_992_ = l_Lean_throwAttrMustBeGlobal(v_m_985_, v_inst_986_, v_inst_987_, v_00_u03b1_988_, v_name_989_, v_kind_boxed_991_);
return v_res_992_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_995_ = l_Lean_stringToMessageData(v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_998_ = l_Lean_stringToMessageData(v___x_997_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_1001_ = l_Lean_stringToMessageData(v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_1002_, lean_object* v_inst_1003_, lean_object* v_attrName_1004_, lean_object* v_declName_1005_){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1006_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1007_ = l_Lean_MessageData_ofName(v_attrName_1004_);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = 0;
v___x_1012_ = l_Lean_MessageData_ofConstName(v_declName_1005_, v___x_1011_);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1010_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = l_Lean_throwError___redArg(v_inst_1002_, v_inst_1003_, v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1017_, lean_object* v_inst_1018_, lean_object* v_inst_1019_, lean_object* v_00_u03b1_1020_, lean_object* v_attrName_1021_, lean_object* v_declName_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1018_, v_inst_1019_, v_attrName_1021_, v_declName_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1026_ = l_Lean_stringToMessageData(v___x_1025_);
return v___x_1026_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1029_ = l_Lean_stringToMessageData(v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1030_, lean_object* v_inst_1031_, lean_object* v_attrName_1032_, lean_object* v_declName_1033_, lean_object* v_asyncPrefix_x3f_1034_){
_start:
{
lean_object* v___y_1036_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1034_) == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_MessageData_nil;
v___y_1036_ = v___x_1049_;
goto v___jp_1035_;
}
else
{
lean_object* v_val_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_val_1050_ = lean_ctor_get(v_asyncPrefix_x3f_1034_, 0);
lean_inc(v_val_1050_);
lean_dec_ref_known(v_asyncPrefix_x3f_1034_, 1);
v___x_1051_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1052_ = l_Lean_MessageData_ofName(v_val_1050_);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___y_1036_ = v___x_1055_;
goto v___jp_1035_;
}
v___jp_1035_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1037_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1038_ = l_Lean_MessageData_ofName(v_attrName_1032_);
v___x_1039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = 0;
v___x_1043_ = l_Lean_MessageData_ofConstName(v_declName_1033_, v___x_1042_);
v___x_1044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1041_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v___y_1036_);
v___x_1048_ = l_Lean_throwError___redArg(v_inst_1030_, v_inst_1031_, v___x_1047_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1056_, lean_object* v_inst_1057_, lean_object* v_inst_1058_, lean_object* v_00_u03b1_1059_, lean_object* v_attrName_1060_, lean_object* v_declName_1061_, lean_object* v_asyncPrefix_x3f_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1057_, v_inst_1058_, v_attrName_1060_, v_declName_1061_, v_asyncPrefix_x3f_1062_);
return v___x_1063_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1066_ = l_Lean_stringToMessageData(v___x_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1069_ = l_Lean_stringToMessageData(v___x_1068_);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1072_ = l_Lean_stringToMessageData(v___x_1071_);
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1075_ = l_Lean_stringToMessageData(v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1076_, lean_object* v_inst_1077_, lean_object* v_attrName_1078_, lean_object* v_declName_1079_, lean_object* v_givenType_1080_, lean_object* v_expectedType_1081_){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1082_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1083_ = l_Lean_MessageData_ofName(v_attrName_1078_);
lean_inc_ref(v___x_1083_);
v___x_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = 0;
v___x_1088_ = l_Lean_MessageData_ofConstName(v_declName_1079_, v___x_1087_);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1086_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = l_Lean_indentExpr(v_givenType_1080_);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v___x_1083_);
v___x_1097_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = l_Lean_indentExpr(v_expectedType_1081_);
v___x_1100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = l_Lean_throwError___redArg(v_inst_1076_, v_inst_1077_, v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1102_, lean_object* v_inst_1103_, lean_object* v_inst_1104_, lean_object* v_00_u03b1_1105_, lean_object* v_attrName_1106_, lean_object* v_declName_1107_, lean_object* v_givenType_1108_, lean_object* v_expectedType_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1103_, v_inst_1104_, v_attrName_1106_, v_declName_1107_, v_givenType_1108_, v_expectedType_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1111_, uint8_t v_skipRealize_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; lean_object* v_env_1116_; uint8_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1115_ = lean_st_ref_get(v___y_1113_);
v_env_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc_ref(v_env_1116_);
lean_dec(v___x_1115_);
v___x_1117_ = l_Lean_Environment_contains(v_env_1116_, v_constName_1111_, v_skipRealize_1112_);
v___x_1118_ = lean_box(v___x_1117_);
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object* v_constName_1120_, lean_object* v_skipRealize_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
uint8_t v_skipRealize_boxed_1124_; lean_object* v_res_1125_; 
v_skipRealize_boxed_1124_ = lean_unbox(v_skipRealize_1121_);
v_res_1125_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1120_, v_skipRealize_boxed_1124_, v___y_1122_);
lean_dec(v___y_1122_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1126_, uint8_t v_skipRealize_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1126_, v_skipRealize_1127_, v___y_1129_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1132_, lean_object* v_skipRealize_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
uint8_t v_skipRealize_boxed_1137_; lean_object* v_res_1138_; 
v_skipRealize_boxed_1137_ = lean_unbox(v_skipRealize_1133_);
v_res_1138_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1132_, v_skipRealize_boxed_1137_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1139_, uint8_t v_isExporting_1140_, lean_object* v___x_1141_, lean_object* v_a_x3f_1142_){
_start:
{
lean_object* v___x_1144_; lean_object* v_env_1145_; lean_object* v_nextMacroScope_1146_; lean_object* v_ngen_1147_; lean_object* v_auxDeclNGen_1148_; lean_object* v_traceState_1149_; lean_object* v_recordedDeps_1150_; lean_object* v_messages_1151_; lean_object* v_infoState_1152_; lean_object* v_snapshotTasks_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1164_; 
v___x_1144_ = lean_st_ref_take(v___y_1139_);
v_env_1145_ = lean_ctor_get(v___x_1144_, 0);
v_nextMacroScope_1146_ = lean_ctor_get(v___x_1144_, 1);
v_ngen_1147_ = lean_ctor_get(v___x_1144_, 2);
v_auxDeclNGen_1148_ = lean_ctor_get(v___x_1144_, 3);
v_traceState_1149_ = lean_ctor_get(v___x_1144_, 4);
v_recordedDeps_1150_ = lean_ctor_get(v___x_1144_, 6);
v_messages_1151_ = lean_ctor_get(v___x_1144_, 7);
v_infoState_1152_ = lean_ctor_get(v___x_1144_, 8);
v_snapshotTasks_1153_ = lean_ctor_get(v___x_1144_, 9);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; 
v_unused_1165_ = lean_ctor_get(v___x_1144_, 5);
lean_dec(v_unused_1165_);
v___x_1155_ = v___x_1144_;
v_isShared_1156_ = v_isSharedCheck_1164_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_snapshotTasks_1153_);
lean_inc(v_infoState_1152_);
lean_inc(v_messages_1151_);
lean_inc(v_recordedDeps_1150_);
lean_inc(v_traceState_1149_);
lean_inc(v_auxDeclNGen_1148_);
lean_inc(v_ngen_1147_);
lean_inc(v_nextMacroScope_1146_);
lean_inc(v_env_1145_);
lean_dec(v___x_1144_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1164_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1157_ = lean_box(0);
v___x_1158_ = l_Lean_Environment_setExporting(v_env_1145_, v_isExporting_1140_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 5, v___x_1141_);
lean_ctor_set(v___x_1155_, 0, v___x_1158_);
v___x_1160_ = v___x_1155_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_nextMacroScope_1146_);
lean_ctor_set(v_reuseFailAlloc_1163_, 2, v_ngen_1147_);
lean_ctor_set(v_reuseFailAlloc_1163_, 3, v_auxDeclNGen_1148_);
lean_ctor_set(v_reuseFailAlloc_1163_, 4, v_traceState_1149_);
lean_ctor_set(v_reuseFailAlloc_1163_, 5, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1163_, 6, v_recordedDeps_1150_);
lean_ctor_set(v_reuseFailAlloc_1163_, 7, v_messages_1151_);
lean_ctor_set(v_reuseFailAlloc_1163_, 8, v_infoState_1152_);
lean_ctor_set(v_reuseFailAlloc_1163_, 9, v_snapshotTasks_1153_);
v___x_1160_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_st_ref_put(v___y_1139_, v___x_1160_);
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1157_);
return v___x_1162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1166_, lean_object* v_isExporting_1167_, lean_object* v___x_1168_, lean_object* v_a_x3f_1169_, lean_object* v___y_1170_){
_start:
{
uint8_t v_isExporting_boxed_1171_; lean_object* v_res_1172_; 
v_isExporting_boxed_1171_ = lean_unbox(v_isExporting_1167_);
v_res_1172_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1166_, v_isExporting_boxed_1171_, v___x_1168_, v_a_x3f_1169_);
lean_dec(v_a_x3f_1169_);
lean_dec(v___y_1166_);
return v_res_1172_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0);
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
return v___x_1174_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1177_, uint8_t v_isExporting_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1182_; lean_object* v_env_1183_; lean_object* v___x_1184_; uint8_t v_isModule_1185_; 
v___x_1182_ = lean_st_ref_get(v___y_1180_);
v_env_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc_ref(v_env_1183_);
lean_dec(v___x_1182_);
v___x_1184_ = l_Lean_Environment_header(v_env_1183_);
v_isModule_1185_ = lean_ctor_get_uint8(v___x_1184_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1184_);
if (v_isModule_1185_ == 0)
{
lean_object* v___x_1186_; 
lean_dec_ref(v_env_1183_);
lean_inc(v___y_1180_);
lean_inc_ref(v___y_1179_);
v___x_1186_ = lean_apply_3(v_x_1177_, v___y_1179_, v___y_1180_, lean_box(0));
return v___x_1186_;
}
else
{
uint8_t v_isExporting_1187_; 
v_isExporting_1187_ = lean_ctor_get_uint8(v_env_1183_, sizeof(void*)*13);
lean_dec_ref(v_env_1183_);
if (v_isExporting_1178_ == 0)
{
if (v_isExporting_1187_ == 0)
{
lean_object* v___x_1239_; 
lean_inc(v___y_1180_);
lean_inc_ref(v___y_1179_);
v___x_1239_ = lean_apply_3(v_x_1177_, v___y_1179_, v___y_1180_, lean_box(0));
return v___x_1239_;
}
else
{
goto v___jp_1188_;
}
}
else
{
if (v_isExporting_1187_ == 0)
{
goto v___jp_1188_;
}
else
{
lean_object* v___x_1240_; 
lean_inc(v___y_1180_);
lean_inc_ref(v___y_1179_);
v___x_1240_ = lean_apply_3(v_x_1177_, v___y_1179_, v___y_1180_, lean_box(0));
return v___x_1240_;
}
}
v___jp_1188_:
{
lean_object* v___x_1189_; lean_object* v_env_1190_; lean_object* v_nextMacroScope_1191_; lean_object* v_ngen_1192_; lean_object* v_auxDeclNGen_1193_; lean_object* v_traceState_1194_; lean_object* v_recordedDeps_1195_; lean_object* v_messages_1196_; lean_object* v_infoState_1197_; lean_object* v_snapshotTasks_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1237_; 
v___x_1189_ = lean_st_ref_take(v___y_1180_);
v_env_1190_ = lean_ctor_get(v___x_1189_, 0);
v_nextMacroScope_1191_ = lean_ctor_get(v___x_1189_, 1);
v_ngen_1192_ = lean_ctor_get(v___x_1189_, 2);
v_auxDeclNGen_1193_ = lean_ctor_get(v___x_1189_, 3);
v_traceState_1194_ = lean_ctor_get(v___x_1189_, 4);
v_recordedDeps_1195_ = lean_ctor_get(v___x_1189_, 6);
v_messages_1196_ = lean_ctor_get(v___x_1189_, 7);
v_infoState_1197_ = lean_ctor_get(v___x_1189_, 8);
v_snapshotTasks_1198_ = lean_ctor_get(v___x_1189_, 9);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; 
v_unused_1238_ = lean_ctor_get(v___x_1189_, 5);
lean_dec(v_unused_1238_);
v___x_1200_ = v___x_1189_;
v_isShared_1201_ = v_isSharedCheck_1237_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_snapshotTasks_1198_);
lean_inc(v_infoState_1197_);
lean_inc(v_messages_1196_);
lean_inc(v_recordedDeps_1195_);
lean_inc(v_traceState_1194_);
lean_inc(v_auxDeclNGen_1193_);
lean_inc(v_ngen_1192_);
lean_inc(v_nextMacroScope_1191_);
lean_inc(v_env_1190_);
lean_dec(v___x_1189_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1237_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1202_ = l_Lean_Environment_setExporting(v_env_1190_, v_isExporting_1178_);
v___x_1203_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 5, v___x_1203_);
lean_ctor_set(v___x_1200_, 0, v___x_1202_);
v___x_1205_ = v___x_1200_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_nextMacroScope_1191_);
lean_ctor_set(v_reuseFailAlloc_1236_, 2, v_ngen_1192_);
lean_ctor_set(v_reuseFailAlloc_1236_, 3, v_auxDeclNGen_1193_);
lean_ctor_set(v_reuseFailAlloc_1236_, 4, v_traceState_1194_);
lean_ctor_set(v_reuseFailAlloc_1236_, 5, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1236_, 6, v_recordedDeps_1195_);
lean_ctor_set(v_reuseFailAlloc_1236_, 7, v_messages_1196_);
lean_ctor_set(v_reuseFailAlloc_1236_, 8, v_infoState_1197_);
lean_ctor_set(v_reuseFailAlloc_1236_, 9, v_snapshotTasks_1198_);
v___x_1205_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; lean_object* v_r_1207_; 
v___x_1206_ = lean_st_ref_put(v___y_1180_, v___x_1205_);
lean_inc(v___y_1180_);
lean_inc_ref(v___y_1179_);
v_r_1207_ = lean_apply_3(v_x_1177_, v___y_1179_, v___y_1180_, lean_box(0));
if (lean_obj_tag(v_r_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1224_; 
v_a_1208_ = lean_ctor_get(v_r_1207_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_r_1207_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1210_ = v_r_1207_;
v_isShared_1211_ = v_isSharedCheck_1224_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v_r_1207_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1224_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
lean_inc(v_a_1208_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set_tag(v___x_1210_, 1);
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
v___x_1214_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1180_, v_isExporting_1187_, v___x_1203_, v___x_1213_);
lean_dec_ref(v___x_1213_);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; 
v_unused_1222_ = lean_ctor_get(v___x_1214_, 0);
lean_dec(v_unused_1222_);
v___x_1216_ = v___x_1214_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_dec(v___x_1214_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v_a_1208_);
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1208_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
v_a_1225_ = lean_ctor_get(v_r_1207_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v_r_1207_, 1);
v___x_1226_ = lean_box(0);
v___x_1227_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1180_, v_isExporting_1187_, v___x_1203_, v___x_1226_);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; 
v_unused_1235_ = lean_ctor_get(v___x_1227_, 0);
lean_dec(v_unused_1235_);
v___x_1229_ = v___x_1227_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_dec(v___x_1227_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set_tag(v___x_1229_, 1);
lean_ctor_set(v___x_1229_, 0, v_a_1225_);
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1225_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1241_, lean_object* v_isExporting_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
uint8_t v_isExporting_boxed_1246_; lean_object* v_res_1247_; 
v_isExporting_boxed_1246_ = lean_unbox(v_isExporting_1242_);
v_res_1247_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1241_, v_isExporting_boxed_1246_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1248_, lean_object* v_x_1249_, uint8_t v_isExporting_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1249_, v_isExporting_1250_, v___y_1251_, v___y_1252_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1255_, lean_object* v_x_1256_, lean_object* v_isExporting_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
uint8_t v_isExporting_boxed_1261_; lean_object* v_res_1262_; 
v_isExporting_boxed_1261_ = lean_unbox(v_isExporting_1257_);
v_res_1262_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1255_, v_x_1256_, v_isExporting_boxed_1261_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
return v_res_1262_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1263_, lean_object* v_opt_1264_){
_start:
{
lean_object* v_name_1265_; lean_object* v_defValue_1266_; lean_object* v_map_1267_; lean_object* v___x_1268_; 
v_name_1265_ = lean_ctor_get(v_opt_1264_, 0);
v_defValue_1266_ = lean_ctor_get(v_opt_1264_, 1);
v_map_1267_ = lean_ctor_get(v_opts_1263_, 0);
v___x_1268_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1267_, v_name_1265_);
if (lean_obj_tag(v___x_1268_) == 0)
{
uint8_t v___x_1269_; 
v___x_1269_ = lean_unbox(v_defValue_1266_);
return v___x_1269_;
}
else
{
lean_object* v_val_1270_; 
v_val_1270_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_val_1270_);
lean_dec_ref_known(v___x_1268_, 1);
if (lean_obj_tag(v_val_1270_) == 1)
{
uint8_t v_v_1271_; 
v_v_1271_ = lean_ctor_get_uint8(v_val_1270_, 0);
lean_dec_ref_known(v_val_1270_, 0);
return v_v_1271_;
}
else
{
uint8_t v___x_1272_; 
lean_dec(v_val_1270_);
v___x_1272_ = lean_unbox(v_defValue_1266_);
return v___x_1272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1273_, lean_object* v_opt_1274_){
_start:
{
uint8_t v_res_1275_; lean_object* v_r_1276_; 
v_res_1275_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1273_, v_opt_1274_);
lean_dec_ref(v_opt_1274_);
lean_dec_ref(v_opts_1273_);
v_r_1276_ = lean_box(v_res_1275_);
return v_r_1276_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_1284_, lean_object* v_x_1285_){
_start:
{
if (lean_obj_tag(v_x_1285_) == 1)
{
lean_object* v_pre_1286_; 
v_pre_1286_ = lean_ctor_get(v_x_1285_, 0);
switch(lean_obj_tag(v_pre_1286_))
{
case 1:
{
lean_object* v_pre_1287_; 
v_pre_1287_ = lean_ctor_get(v_pre_1286_, 0);
switch(lean_obj_tag(v_pre_1287_))
{
case 0:
{
lean_object* v_str_1288_; lean_object* v_str_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v_str_1288_ = lean_ctor_get(v_x_1285_, 1);
v_str_1289_ = lean_ctor_get(v_pre_1286_, 1);
v___x_1290_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1291_ = lean_string_dec_eq(v_str_1289_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1293_ = lean_string_dec_eq(v_str_1289_, v___x_1292_);
if (v___x_1293_ == 0)
{
return v___x_1293_;
}
else
{
lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1295_ = lean_string_dec_eq(v_str_1288_, v___x_1294_);
if (v___x_1295_ == 0)
{
return v___x_1295_;
}
else
{
return v_suppressElabErrors_1284_;
}
}
}
else
{
lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1296_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1297_ = lean_string_dec_eq(v_str_1288_, v___x_1296_);
if (v___x_1297_ == 0)
{
return v___x_1297_;
}
else
{
return v_suppressElabErrors_1284_;
}
}
}
case 1:
{
lean_object* v_pre_1298_; 
v_pre_1298_ = lean_ctor_get(v_pre_1287_, 0);
if (lean_obj_tag(v_pre_1298_) == 0)
{
lean_object* v_str_1299_; lean_object* v_str_1300_; lean_object* v_str_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v_str_1299_ = lean_ctor_get(v_x_1285_, 1);
v_str_1300_ = lean_ctor_get(v_pre_1286_, 1);
v_str_1301_ = lean_ctor_get(v_pre_1287_, 1);
v___x_1302_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1303_ = lean_string_dec_eq(v_str_1301_, v___x_1302_);
if (v___x_1303_ == 0)
{
return v___x_1303_;
}
else
{
lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1304_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1305_ = lean_string_dec_eq(v_str_1300_, v___x_1304_);
if (v___x_1305_ == 0)
{
return v___x_1305_;
}
else
{
lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1306_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1307_ = lean_string_dec_eq(v_str_1299_, v___x_1306_);
if (v___x_1307_ == 0)
{
return v___x_1307_;
}
else
{
return v_suppressElabErrors_1284_;
}
}
}
}
else
{
uint8_t v___x_1308_; 
v___x_1308_ = 0;
return v___x_1308_;
}
}
default: 
{
uint8_t v___x_1309_; 
v___x_1309_ = 0;
return v___x_1309_;
}
}
}
case 0:
{
lean_object* v_str_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_str_1310_ = lean_ctor_get(v_x_1285_, 1);
v___x_1311_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1312_ = lean_string_dec_eq(v_str_1310_, v___x_1311_);
if (v___x_1312_ == 0)
{
return v___x_1312_;
}
else
{
return v_suppressElabErrors_1284_;
}
}
default: 
{
uint8_t v___x_1313_; 
v___x_1313_ = 0;
return v___x_1313_;
}
}
}
else
{
uint8_t v___x_1314_; 
v___x_1314_ = 0;
return v___x_1314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_1315_, lean_object* v_x_1316_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1317_; uint8_t v_res_1318_; lean_object* v_r_1319_; 
v_suppressElabErrors_boxed_1317_ = lean_unbox(v_suppressElabErrors_1315_);
v_res_1318_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_1317_, v_x_1316_);
lean_dec(v_x_1316_);
v_r_1319_ = lean_box(v_res_1318_);
return v_r_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1320_, lean_object* v_msgData_1321_, uint8_t v_severity_1322_, uint8_t v_isSilent_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___y_1328_; uint8_t v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; uint8_t v___y_1334_; lean_object* v_toCold_1335_; lean_object* v___y_1336_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; uint8_t v___y_1368_; uint8_t v___y_1369_; uint8_t v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1392_; lean_object* v___y_1393_; uint8_t v___y_1394_; uint8_t v___y_1395_; lean_object* v___y_1396_; uint8_t v___y_1397_; lean_object* v___y_1398_; uint8_t v___y_1402_; uint8_t v___y_1403_; uint8_t v___x_1413_; uint8_t v___y_1415_; uint8_t v___x_1421_; 
v___x_1413_ = 2;
v___x_1421_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1322_, v___x_1413_);
if (v___x_1421_ == 0)
{
v___y_1415_ = v___x_1421_;
goto v___jp_1414_;
}
else
{
uint8_t v___x_1422_; 
lean_inc_ref(v_msgData_1321_);
v___x_1422_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1321_);
if (v___x_1422_ == 0)
{
v___y_1415_ = v___x_1422_;
goto v___jp_1414_;
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_dec_ref(v_msgData_1321_);
v___x_1423_ = lean_box(0);
v___x_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
return v___x_1424_;
}
}
v___jp_1327_:
{
lean_object* v_currNamespace_1337_; lean_object* v_openDecls_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v_env_1343_; lean_object* v_nextMacroScope_1344_; lean_object* v_ngen_1345_; lean_object* v_auxDeclNGen_1346_; lean_object* v_traceState_1347_; lean_object* v_cache_1348_; lean_object* v_recordedDeps_1349_; lean_object* v_messages_1350_; lean_object* v_infoState_1351_; lean_object* v_snapshotTasks_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1363_; 
v_currNamespace_1337_ = lean_ctor_get(v_toCold_1335_, 4);
v_openDecls_1338_ = lean_ctor_get(v_toCold_1335_, 5);
lean_inc(v_openDecls_1338_);
lean_inc(v_currNamespace_1337_);
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v_currNamespace_1337_);
lean_ctor_set(v___x_1339_, 1, v_openDecls_1338_);
v___x_1340_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
lean_ctor_set(v___x_1340_, 1, v___y_1330_);
lean_inc_ref(v___y_1333_);
lean_inc_ref(v___y_1332_);
v___x_1341_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1341_, 0, v___y_1332_);
lean_ctor_set(v___x_1341_, 1, v___y_1328_);
lean_ctor_set(v___x_1341_, 2, v___y_1331_);
lean_ctor_set(v___x_1341_, 3, v___y_1333_);
lean_ctor_set(v___x_1341_, 4, v___x_1340_);
lean_ctor_set_uint8(v___x_1341_, sizeof(void*)*5, v___y_1334_);
lean_ctor_set_uint8(v___x_1341_, sizeof(void*)*5 + 1, v___y_1329_);
lean_ctor_set_uint8(v___x_1341_, sizeof(void*)*5 + 2, v_isSilent_1323_);
v___x_1342_ = lean_st_ref_take(v___y_1336_);
v_env_1343_ = lean_ctor_get(v___x_1342_, 0);
v_nextMacroScope_1344_ = lean_ctor_get(v___x_1342_, 1);
v_ngen_1345_ = lean_ctor_get(v___x_1342_, 2);
v_auxDeclNGen_1346_ = lean_ctor_get(v___x_1342_, 3);
v_traceState_1347_ = lean_ctor_get(v___x_1342_, 4);
v_cache_1348_ = lean_ctor_get(v___x_1342_, 5);
v_recordedDeps_1349_ = lean_ctor_get(v___x_1342_, 6);
v_messages_1350_ = lean_ctor_get(v___x_1342_, 7);
v_infoState_1351_ = lean_ctor_get(v___x_1342_, 8);
v_snapshotTasks_1352_ = lean_ctor_get(v___x_1342_, 9);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1354_ = v___x_1342_;
v_isShared_1355_ = v_isSharedCheck_1363_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_snapshotTasks_1352_);
lean_inc(v_infoState_1351_);
lean_inc(v_messages_1350_);
lean_inc(v_recordedDeps_1349_);
lean_inc(v_cache_1348_);
lean_inc(v_traceState_1347_);
lean_inc(v_auxDeclNGen_1346_);
lean_inc(v_ngen_1345_);
lean_inc(v_nextMacroScope_1344_);
lean_inc(v_env_1343_);
lean_dec(v___x_1342_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1363_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1356_ = lean_box(0);
v___x_1357_ = l_Lean_MessageLog_add(v___x_1341_, v_messages_1350_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 7, v___x_1357_);
v___x_1359_ = v___x_1354_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_env_1343_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_nextMacroScope_1344_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v_ngen_1345_);
lean_ctor_set(v_reuseFailAlloc_1362_, 3, v_auxDeclNGen_1346_);
lean_ctor_set(v_reuseFailAlloc_1362_, 4, v_traceState_1347_);
lean_ctor_set(v_reuseFailAlloc_1362_, 5, v_cache_1348_);
lean_ctor_set(v_reuseFailAlloc_1362_, 6, v_recordedDeps_1349_);
lean_ctor_set(v_reuseFailAlloc_1362_, 7, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1362_, 8, v_infoState_1351_);
lean_ctor_set(v_reuseFailAlloc_1362_, 9, v_snapshotTasks_1352_);
v___x_1359_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_st_ref_put(v___y_1336_, v___x_1359_);
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1356_);
return v___x_1361_;
}
}
}
v___jp_1364_:
{
lean_object* v_fileName_1373_; lean_object* v_fileMap_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1390_; 
v_fileName_1373_ = lean_ctor_get(v___y_1367_, 0);
v_fileMap_1374_ = lean_ctor_get(v___y_1367_, 1);
v___x_1375_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1321_);
v___x_1376_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v___x_1375_, v___y_1324_, v___y_1325_);
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1390_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1390_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_inc_ref_n(v_fileMap_1374_, 2);
v___x_1381_ = l_Lean_FileMap_toPosition(v_fileMap_1374_, v___y_1371_);
lean_dec(v___y_1371_);
v___x_1382_ = l_Lean_FileMap_toPosition(v_fileMap_1374_, v___y_1372_);
lean_dec(v___y_1372_);
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
v___x_1384_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1369_ == 0)
{
lean_del_object(v___x_1379_);
lean_dec_ref(v___y_1366_);
v___y_1328_ = v___x_1381_;
v___y_1329_ = v___y_1368_;
v___y_1330_ = v_a_1377_;
v___y_1331_ = v___x_1383_;
v___y_1332_ = v_fileName_1373_;
v___y_1333_ = v___x_1384_;
v___y_1334_ = v___y_1370_;
v_toCold_1335_ = v___y_1365_;
v___y_1336_ = v___y_1325_;
goto v___jp_1327_;
}
else
{
uint8_t v___x_1385_; 
lean_inc(v_a_1377_);
v___x_1385_ = l_Lean_MessageData_hasTag(v___y_1366_, v_a_1377_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1388_; 
lean_dec_ref_known(v___x_1383_, 1);
lean_dec_ref(v___x_1381_);
lean_dec(v_a_1377_);
v___x_1386_ = lean_box(0);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1386_);
v___x_1388_ = v___x_1379_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
else
{
lean_del_object(v___x_1379_);
v___y_1328_ = v___x_1381_;
v___y_1329_ = v___y_1368_;
v___y_1330_ = v_a_1377_;
v___y_1331_ = v___x_1383_;
v___y_1332_ = v_fileName_1373_;
v___y_1333_ = v___x_1384_;
v___y_1334_ = v___y_1370_;
v_toCold_1335_ = v___y_1365_;
v___y_1336_ = v___y_1325_;
goto v___jp_1327_;
}
}
}
}
v___jp_1391_:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_Syntax_getTailPos_x3f(v___y_1396_, v___y_1397_);
lean_dec(v___y_1396_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_inc(v___y_1398_);
v___y_1365_ = v___y_1392_;
v___y_1366_ = v___y_1393_;
v___y_1367_ = v___y_1392_;
v___y_1368_ = v___y_1395_;
v___y_1369_ = v___y_1394_;
v___y_1370_ = v___y_1397_;
v___y_1371_ = v___y_1398_;
v___y_1372_ = v___y_1398_;
goto v___jp_1364_;
}
else
{
lean_object* v_val_1400_; 
v_val_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_val_1400_);
lean_dec_ref_known(v___x_1399_, 1);
v___y_1365_ = v___y_1392_;
v___y_1366_ = v___y_1393_;
v___y_1367_ = v___y_1392_;
v___y_1368_ = v___y_1395_;
v___y_1369_ = v___y_1394_;
v___y_1370_ = v___y_1397_;
v___y_1371_ = v___y_1398_;
v___y_1372_ = v_val_1400_;
goto v___jp_1364_;
}
}
v___jp_1401_:
{
lean_object* v_toCold_1404_; lean_object* v_ref_1405_; uint8_t v_suppressElabErrors_1406_; lean_object* v___x_1407_; lean_object* v___f_1408_; lean_object* v_ref_1409_; lean_object* v___x_1410_; 
v_toCold_1404_ = lean_ctor_get(v___y_1324_, 0);
v_ref_1405_ = lean_ctor_get(v___y_1324_, 2);
v_suppressElabErrors_1406_ = lean_ctor_get_uint8(v___y_1324_, sizeof(void*)*3 + 2);
v___x_1407_ = lean_box(v_suppressElabErrors_1406_);
v___f_1408_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1408_, 0, v___x_1407_);
v_ref_1409_ = l_Lean_replaceRef(v_ref_1320_, v_ref_1405_);
v___x_1410_ = l_Lean_Syntax_getPos_x3f(v_ref_1409_, v___y_1402_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v___x_1411_; 
v___x_1411_ = lean_unsigned_to_nat(0u);
v___y_1392_ = v_toCold_1404_;
v___y_1393_ = v___f_1408_;
v___y_1394_ = v_suppressElabErrors_1406_;
v___y_1395_ = v___y_1403_;
v___y_1396_ = v_ref_1409_;
v___y_1397_ = v___y_1402_;
v___y_1398_ = v___x_1411_;
goto v___jp_1391_;
}
else
{
lean_object* v_val_1412_; 
v_val_1412_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_val_1412_);
lean_dec_ref_known(v___x_1410_, 1);
v___y_1392_ = v_toCold_1404_;
v___y_1393_ = v___f_1408_;
v___y_1394_ = v_suppressElabErrors_1406_;
v___y_1395_ = v___y_1403_;
v___y_1396_ = v_ref_1409_;
v___y_1397_ = v___y_1402_;
v___y_1398_ = v_val_1412_;
goto v___jp_1391_;
}
}
v___jp_1414_:
{
uint8_t v___x_1416_; uint8_t v___x_1417_; 
v___x_1416_ = 1;
v___x_1417_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1322_, v___x_1416_);
if (v___x_1417_ == 0)
{
v___y_1402_ = v___y_1415_;
v___y_1403_ = v_severity_1322_;
goto v___jp_1401_;
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1418_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1324_);
v___x_1419_ = l_Lean_warningAsError;
v___x_1420_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v___x_1418_, v___x_1419_);
lean_dec_ref(v___x_1418_);
if (v___x_1420_ == 0)
{
v___y_1402_ = v___y_1415_;
v___y_1403_ = v_severity_1322_;
goto v___jp_1401_;
}
else
{
v___y_1402_ = v___y_1415_;
v___y_1403_ = v___x_1413_;
goto v___jp_1401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1425_, lean_object* v_msgData_1426_, lean_object* v_severity_1427_, lean_object* v_isSilent_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
uint8_t v_severity_boxed_1432_; uint8_t v_isSilent_boxed_1433_; lean_object* v_res_1434_; 
v_severity_boxed_1432_ = lean_unbox(v_severity_1427_);
v_isSilent_boxed_1433_ = lean_unbox(v_isSilent_1428_);
v_res_1434_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1425_, v_msgData_1426_, v_severity_boxed_1432_, v_isSilent_boxed_1433_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v_ref_1425_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1435_, uint8_t v_severity_1436_, uint8_t v_isSilent_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_ref_1441_; lean_object* v___x_1442_; 
v_ref_1441_ = lean_ctor_get(v___y_1438_, 2);
v___x_1442_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1441_, v_msgData_1435_, v_severity_1436_, v_isSilent_1437_, v___y_1438_, v___y_1439_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1443_, lean_object* v_severity_1444_, lean_object* v_isSilent_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
uint8_t v_severity_boxed_1449_; uint8_t v_isSilent_boxed_1450_; lean_object* v_res_1451_; 
v_severity_boxed_1449_ = lean_unbox(v_severity_1444_);
v_isSilent_boxed_1450_ = lean_unbox(v_isSilent_1445_);
v_res_1451_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1443_, v_severity_boxed_1449_, v_isSilent_boxed_1450_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
uint8_t v___x_1456_; uint8_t v___x_1457_; lean_object* v___x_1458_; 
v___x_1456_ = 1;
v___x_1457_ = 0;
v___x_1458_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1452_, v___x_1456_, v___x_1457_, v___y_1453_, v___y_1454_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1459_, v___y_1460_, v___y_1461_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v___x_1467_; uint8_t v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1467_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1465_);
v___x_1468_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v___x_1467_, v_opt_1464_);
lean_dec_ref(v___x_1467_);
v___x_1469_ = lean_box(v___x_1468_);
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1471_, v___y_1472_);
lean_dec_ref(v___y_1472_);
lean_dec_ref(v_opt_1471_);
return v_res_1474_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1477_ = l_Lean_stringToMessageData(v___x_1476_);
return v___x_1477_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1480_ = l_Lean_stringToMessageData(v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; lean_object* v_env_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1508_; 
v___x_1485_ = lean_st_ref_get(v___y_1483_);
v_env_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc_ref(v_env_1486_);
lean_dec(v___x_1485_);
v___x_1487_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1488_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1487_, v___y_1482_);
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1491_ = v___x_1488_;
v_isShared_1492_ = v_isSharedCheck_1508_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1488_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1508_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
uint8_t v_isExporting_1498_; 
v_isExporting_1498_ = lean_ctor_get_uint8(v_env_1486_, sizeof(void*)*13);
lean_dec_ref(v_env_1486_);
if (v_isExporting_1498_ == 0)
{
lean_dec(v_a_1489_);
lean_dec(v_id_1481_);
goto v___jp_1493_;
}
else
{
uint8_t v___x_1499_; 
v___x_1499_ = l_Lean_isPrivateName(v_id_1481_);
if (v___x_1499_ == 0)
{
lean_dec(v_a_1489_);
lean_dec(v_id_1481_);
goto v___jp_1493_;
}
else
{
uint8_t v___x_1500_; 
v___x_1500_ = lean_unbox(v_a_1489_);
lean_dec(v_a_1489_);
if (v___x_1500_ == 0)
{
lean_dec(v_id_1481_);
goto v___jp_1493_;
}
else
{
lean_object* v___x_1501_; uint8_t v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_del_object(v___x_1491_);
v___x_1501_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1502_ = 0;
v___x_1503_ = l_Lean_MessageData_ofConstName(v_id_1481_, v___x_1502_);
v___x_1504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1501_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
v___x_1505_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1504_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1506_, v___y_1482_, v___y_1483_);
return v___x_1507_;
}
}
}
v___jp_1493_:
{
lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1494_ = lean_box(0);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v___x_1494_);
v___x_1496_ = v___x_1491_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
return v_res_1513_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1516_ = l_Lean_stringToMessageData(v___x_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1517_, uint8_t v_isModule_1518_, lean_object* v_attrName_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v___x_1523_; 
lean_inc(v_declName_1517_);
v___x_1523_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1517_, v___y_1520_, v___y_1521_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v___x_1524_; lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1545_; 
lean_dec_ref_known(v___x_1523_, 1);
lean_inc(v_declName_1517_);
v___x_1524_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1517_, v_isModule_1518_, v___y_1521_);
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1545_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1545_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
uint8_t v___x_1529_; 
v___x_1529_ = lean_unbox(v_a_1525_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_del_object(v___x_1527_);
v___x_1530_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1531_ = l_Lean_MessageData_ofName(v_attrName_1519_);
v___x_1532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1530_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1532_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = lean_unbox(v_a_1525_);
lean_dec(v_a_1525_);
v___x_1536_ = l_Lean_MessageData_ofConstName(v_declName_1517_, v___x_1535_);
v___x_1537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1534_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1537_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1539_, v___y_1520_, v___y_1521_);
return v___x_1540_;
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1543_; 
lean_dec(v_a_1525_);
lean_dec(v_attrName_1519_);
lean_dec(v_declName_1517_);
v___x_1541_ = lean_box(0);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1541_);
v___x_1543_ = v___x_1527_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
else
{
lean_dec(v_attrName_1519_);
lean_dec(v_declName_1517_);
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1546_, lean_object* v_isModule_1547_, lean_object* v_attrName_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
uint8_t v_isModule_boxed_1552_; lean_object* v_res_1553_; 
v_isModule_boxed_1552_ = lean_unbox(v_isModule_1547_);
v_res_1553_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1546_, v_isModule_boxed_1552_, v_attrName_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1554_, lean_object* v_declName_1555_, uint8_t v_attrKind_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v___x_1560_; lean_object* v_env_1564_; lean_object* v___x_1565_; uint8_t v_isModule_1566_; 
v___x_1560_ = lean_st_ref_get(v_a_1558_);
v_env_1564_ = lean_ctor_get(v___x_1560_, 0);
lean_inc_ref(v_env_1564_);
lean_dec(v___x_1560_);
v___x_1565_ = l_Lean_Environment_header(v_env_1564_);
lean_dec_ref(v_env_1564_);
v_isModule_1566_ = lean_ctor_get_uint8(v___x_1565_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1565_);
if (v_isModule_1566_ == 0)
{
lean_dec(v_declName_1555_);
lean_dec(v_attrName_1554_);
goto v___jp_1561_;
}
else
{
uint8_t v___x_1567_; uint8_t v___x_1568_; 
v___x_1567_ = 1;
v___x_1568_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1556_, v___x_1567_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; lean_object* v___f_1570_; lean_object* v___x_1571_; 
v___x_1569_ = lean_box(v_isModule_1566_);
v___f_1570_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1570_, 0, v_declName_1555_);
lean_closure_set(v___f_1570_, 1, v___x_1569_);
lean_closure_set(v___f_1570_, 2, v_attrName_1554_);
v___x_1571_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1570_, v_isModule_1566_, v_a_1557_, v_a_1558_);
return v___x_1571_;
}
else
{
lean_dec(v_declName_1555_);
lean_dec(v_attrName_1554_);
goto v___jp_1561_;
}
}
v___jp_1561_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = lean_box(0);
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
return v___x_1563_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1572_, lean_object* v_declName_1573_, lean_object* v_attrKind_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
uint8_t v_attrKind_boxed_1578_; lean_object* v_res_1579_; 
v_attrKind_boxed_1578_ = lean_unbox(v_attrKind_1574_);
v_res_1579_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1572_, v_declName_1573_, v_attrKind_boxed_1578_, v_a_1575_, v_a_1576_);
lean_dec(v_a_1576_);
lean_dec_ref(v_a_1575_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1580_, v___y_1581_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec_ref(v_opt_1585_);
return v_res_1589_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1592_ = l_Lean_stringToMessageData(v___x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1593_, lean_object* v_declName_1594_, uint8_t v_attrKind_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v___x_1599_; lean_object* v_env_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v_isModule_1603_; 
v___x_1599_ = lean_st_ref_get(v_a_1597_);
v_env_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc_ref(v_env_1600_);
lean_dec(v___x_1599_);
v___x_1601_ = lean_st_ref_get(v_a_1597_);
v___x_1602_ = l_Lean_Environment_header(v_env_1600_);
lean_dec_ref(v_env_1600_);
v_isModule_1603_ = lean_ctor_get_uint8(v___x_1602_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1602_);
if (v_isModule_1603_ == 0)
{
lean_object* v___x_1604_; 
lean_dec(v___x_1601_);
v___x_1604_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1593_, v_declName_1594_, v_attrKind_1595_, v_a_1596_, v_a_1597_);
return v___x_1604_;
}
else
{
lean_object* v_env_1605_; uint8_t v___x_1606_; 
v_env_1605_ = lean_ctor_get(v___x_1601_, 0);
lean_inc_ref(v_env_1605_);
lean_dec(v___x_1601_);
lean_inc(v_declName_1594_);
v___x_1606_ = l_Lean_isMarkedMeta(v_env_1605_, v_declName_1594_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1607_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1608_ = l_Lean_MessageData_ofName(v_attrName_1593_);
v___x_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1607_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1609_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = l_Lean_MessageData_ofConstName(v_declName_1594_, v___x_1606_);
v___x_1613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1615_, v_a_1596_, v_a_1597_);
return v___x_1616_;
}
else
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1593_, v_declName_1594_, v_attrKind_1595_, v_a_1596_, v_a_1597_);
return v___x_1617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1618_, lean_object* v_declName_1619_, lean_object* v_attrKind_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_){
_start:
{
uint8_t v_attrKind_boxed_1624_; lean_object* v_res_1625_; 
v_attrKind_boxed_1624_ = lean_unbox(v_attrKind_1620_);
v_res_1625_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1618_, v_declName_1619_, v_attrKind_boxed_1624_, v_a_1621_, v_a_1622_);
lean_dec(v_a_1622_);
lean_dec_ref(v_a_1621_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1634_, v___y_1635_);
lean_dec_ref(v___y_1635_);
lean_dec_ref(v_x_1634_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1638_, lean_object* v_x_1639_){
_start:
{
lean_inc(v_s_1638_);
return v_s_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1640_, lean_object* v_x_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1640_, v_x_1641_);
lean_dec(v_x_1641_);
lean_dec(v_s_1640_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1647_, lean_object* v_x_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1650_, lean_object* v_x_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1650_, v_x_1651_);
lean_dec(v_x_1651_);
lean_dec_ref(v_x_1650_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_box(0);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1655_);
lean_dec(v_x_1655_);
return v_res_1656_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_1661_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1662_; lean_object* v___f_1663_; lean_object* v___f_1664_; lean_object* v___f_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___f_1662_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1663_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1664_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1665_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1666_ = lean_box(0);
v___x_1667_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1668_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
lean_ctor_set(v___x_1668_, 1, v___x_1666_);
lean_ctor_set(v___x_1668_, 2, v___f_1665_);
lean_ctor_set(v___x_1668_, 3, v___f_1664_);
lean_ctor_set(v___x_1668_, 4, v___f_1663_);
lean_ctor_set(v___x_1668_, 5, v___f_1662_);
return v___x_1668_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1670_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v___x_1669_);
return v___x_1671_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1672_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1673_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_registerTagAttribute___lam__0(v_x_1677_);
lean_dec(v_x_1677_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1679_, lean_object* v_x_1680_, lean_object* v_x_1681_){
_start:
{
if (lean_obj_tag(v_x_1681_) == 0)
{
return v_x_1680_;
}
else
{
lean_object* v_head_1682_; lean_object* v_tail_1683_; uint8_t v___x_1684_; 
v_head_1682_ = lean_ctor_get(v_x_1681_, 0);
lean_inc(v_head_1682_);
v_tail_1683_ = lean_ctor_get(v_x_1681_, 1);
lean_inc(v_tail_1683_);
lean_dec_ref_known(v_x_1681_, 2);
v___x_1684_ = l_Lean_NameSet_contains(v_newState_1679_, v_head_1682_);
if (v___x_1684_ == 0)
{
lean_dec(v_head_1682_);
v_x_1681_ = v_tail_1683_;
goto _start;
}
else
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Lean_NameSet_insert(v_x_1680_, v_head_1682_);
v_x_1680_ = v___x_1686_;
v_x_1681_ = v_tail_1683_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1688_, lean_object* v_x_1689_, lean_object* v_x_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1688_, v_x_1689_, v_x_1690_);
lean_dec(v_newState_1688_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1692_, lean_object* v_newState_1693_, lean_object* v_newConsts_1694_, lean_object* v_s_1695_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1693_, v_s_1695_, v_newConsts_1694_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1697_, lean_object* v_newState_1698_, lean_object* v_newConsts_1699_, lean_object* v_s_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_registerTagAttribute___lam__1(v_x_1697_, v_newState_1698_, v_newConsts_1699_, v_s_1700_);
lean_dec(v_newState_1698_);
lean_dec(v_x_1697_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1714_){
_start:
{
lean_object* v___x_1715_; lean_object* v___y_1717_; 
v___x_1715_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1714_) == 0)
{
lean_object* v_size_1721_; 
v_size_1721_ = lean_ctor_get(v_s_1714_, 0);
lean_inc(v_size_1721_);
lean_dec_ref_known(v_s_1714_, 5);
v___y_1717_ = v_size_1721_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_unsigned_to_nat(0u);
v___y_1717_ = v___x_1722_;
goto v___jp_1716_;
}
v___jp_1716_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = l_Nat_reprFast(v___y_1717_);
v___x_1719_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
v___x_1720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1715_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
return v___x_1720_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1723_, lean_object* v_pivot_1724_, lean_object* v_as_1725_, lean_object* v_i_1726_, lean_object* v_k_1727_){
_start:
{
uint8_t v___x_1728_; 
v___x_1728_ = lean_nat_dec_lt(v_k_1727_, v_hi_1723_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec(v_k_1727_);
v___x_1729_ = lean_array_fswap(v_as_1725_, v_i_1726_, v_hi_1723_);
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v_i_1726_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; uint8_t v___x_1732_; 
v___x_1731_ = lean_array_fget_borrowed(v_as_1725_, v_k_1727_);
v___x_1732_ = l_Lean_Name_quickLt(v___x_1731_, v_pivot_1724_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = lean_unsigned_to_nat(1u);
v___x_1734_ = lean_nat_add(v_k_1727_, v___x_1733_);
lean_dec(v_k_1727_);
v_k_1727_ = v___x_1734_;
goto _start;
}
else
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1736_ = lean_array_fswap(v_as_1725_, v_i_1726_, v_k_1727_);
v___x_1737_ = lean_unsigned_to_nat(1u);
v___x_1738_ = lean_nat_add(v_i_1726_, v___x_1737_);
lean_dec(v_i_1726_);
v___x_1739_ = lean_nat_add(v_k_1727_, v___x_1737_);
lean_dec(v_k_1727_);
v_as_1725_ = v___x_1736_;
v_i_1726_ = v___x_1738_;
v_k_1727_ = v___x_1739_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1741_, lean_object* v_pivot_1742_, lean_object* v_as_1743_, lean_object* v_i_1744_, lean_object* v_k_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1741_, v_pivot_1742_, v_as_1743_, v_i_1744_, v_k_1745_);
lean_dec(v_pivot_1742_);
lean_dec(v_hi_1741_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1747_, lean_object* v_as_1748_, lean_object* v_lo_1749_, lean_object* v_hi_1750_){
_start:
{
lean_object* v___y_1752_; uint8_t v___x_1762_; 
v___x_1762_ = lean_nat_dec_lt(v_lo_1749_, v_hi_1750_);
if (v___x_1762_ == 0)
{
lean_dec(v_lo_1749_);
return v_as_1748_;
}
else
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v_mid_1765_; lean_object* v___y_1767_; lean_object* v___y_1773_; lean_object* v___x_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1763_ = lean_nat_add(v_lo_1749_, v_hi_1750_);
v___x_1764_ = lean_unsigned_to_nat(1u);
v_mid_1765_ = lean_nat_shiftr(v___x_1763_, v___x_1764_);
lean_dec(v___x_1763_);
v___x_1778_ = lean_array_fget_borrowed(v_as_1748_, v_mid_1765_);
v___x_1779_ = lean_array_fget_borrowed(v_as_1748_, v_lo_1749_);
v___x_1780_ = l_Lean_Name_quickLt(v___x_1778_, v___x_1779_);
if (v___x_1780_ == 0)
{
v___y_1773_ = v_as_1748_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1781_; 
v___x_1781_ = lean_array_fswap(v_as_1748_, v_lo_1749_, v_mid_1765_);
v___y_1773_ = v___x_1781_;
goto v___jp_1772_;
}
v___jp_1766_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1768_ = lean_array_fget_borrowed(v___y_1767_, v_mid_1765_);
v___x_1769_ = lean_array_fget_borrowed(v___y_1767_, v_hi_1750_);
v___x_1770_ = l_Lean_Name_quickLt(v___x_1768_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_dec(v_mid_1765_);
v___y_1752_ = v___y_1767_;
goto v___jp_1751_;
}
else
{
lean_object* v___x_1771_; 
v___x_1771_ = lean_array_fswap(v___y_1767_, v_mid_1765_, v_hi_1750_);
lean_dec(v_mid_1765_);
v___y_1752_ = v___x_1771_;
goto v___jp_1751_;
}
}
v___jp_1772_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1774_ = lean_array_fget_borrowed(v___y_1773_, v_hi_1750_);
v___x_1775_ = lean_array_fget_borrowed(v___y_1773_, v_lo_1749_);
v___x_1776_ = l_Lean_Name_quickLt(v___x_1774_, v___x_1775_);
if (v___x_1776_ == 0)
{
v___y_1767_ = v___y_1773_;
goto v___jp_1766_;
}
else
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_array_fswap(v___y_1773_, v_lo_1749_, v_hi_1750_);
v___y_1767_ = v___x_1777_;
goto v___jp_1766_;
}
}
}
v___jp_1751_:
{
lean_object* v_pivot_1753_; lean_object* v___x_1754_; lean_object* v_fst_1755_; lean_object* v_snd_1756_; uint8_t v___x_1757_; 
v_pivot_1753_ = lean_array_fget(v___y_1752_, v_hi_1750_);
lean_inc_n(v_lo_1749_, 2);
v___x_1754_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1750_, v_pivot_1753_, v___y_1752_, v_lo_1749_, v_lo_1749_);
lean_dec(v_pivot_1753_);
v_fst_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_fst_1755_);
v_snd_1756_ = lean_ctor_get(v___x_1754_, 1);
lean_inc(v_snd_1756_);
lean_dec_ref(v___x_1754_);
v___x_1757_ = lean_nat_dec_le(v_hi_1750_, v_fst_1755_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1747_, v_snd_1756_, v_lo_1749_, v_fst_1755_);
v___x_1759_ = lean_unsigned_to_nat(1u);
v___x_1760_ = lean_nat_add(v_fst_1755_, v___x_1759_);
lean_dec(v_fst_1755_);
v_as_1748_ = v___x_1758_;
v_lo_1749_ = v___x_1760_;
goto _start;
}
else
{
lean_dec(v_fst_1755_);
lean_dec(v_lo_1749_);
return v_snd_1756_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1782_, lean_object* v_as_1783_, lean_object* v_lo_1784_, lean_object* v_hi_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1782_, v_as_1783_, v_lo_1784_, v_hi_1785_);
lean_dec(v_hi_1785_);
lean_dec(v_n_1782_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1787_, lean_object* v_as_1788_, size_t v_i_1789_, size_t v_stop_1790_, lean_object* v_b_1791_){
_start:
{
lean_object* v___y_1793_; uint8_t v___x_1797_; 
v___x_1797_ = lean_usize_dec_eq(v_i_1789_, v_stop_1790_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; uint8_t v___x_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1798_ = lean_array_uget_borrowed(v_as_1788_, v_i_1789_);
v___x_1799_ = 1;
lean_inc_ref(v_env_1787_);
v___x_1800_ = l_Lean_Environment_setExporting(v_env_1787_, v___x_1799_);
lean_inc(v___x_1798_);
v___x_1801_ = l_Lean_Environment_contains(v___x_1800_, v___x_1798_, v___x_1797_);
if (v___x_1801_ == 0)
{
v___y_1793_ = v_b_1791_;
goto v___jp_1792_;
}
else
{
lean_object* v___x_1802_; 
lean_inc(v___x_1798_);
v___x_1802_ = lean_array_push(v_b_1791_, v___x_1798_);
v___y_1793_ = v___x_1802_;
goto v___jp_1792_;
}
}
else
{
lean_dec_ref(v_env_1787_);
return v_b_1791_;
}
v___jp_1792_:
{
size_t v___x_1794_; size_t v___x_1795_; 
v___x_1794_ = ((size_t)1ULL);
v___x_1795_ = lean_usize_add(v_i_1789_, v___x_1794_);
v_i_1789_ = v___x_1795_;
v_b_1791_ = v___y_1793_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1803_, lean_object* v_as_1804_, lean_object* v_i_1805_, lean_object* v_stop_1806_, lean_object* v_b_1807_){
_start:
{
size_t v_i_boxed_1808_; size_t v_stop_boxed_1809_; lean_object* v_res_1810_; 
v_i_boxed_1808_ = lean_unbox_usize(v_i_1805_);
lean_dec(v_i_1805_);
v_stop_boxed_1809_ = lean_unbox_usize(v_stop_1806_);
lean_dec(v_stop_1806_);
v_res_1810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1803_, v_as_1804_, v_i_boxed_1808_, v_stop_boxed_1809_, v_b_1807_);
lean_dec_ref(v_as_1804_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1811_, lean_object* v_x_1812_){
_start:
{
if (lean_obj_tag(v_x_1812_) == 0)
{
lean_object* v_k_1813_; lean_object* v_l_1814_; lean_object* v_r_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v_k_1813_ = lean_ctor_get(v_x_1812_, 1);
lean_inc(v_k_1813_);
v_l_1814_ = lean_ctor_get(v_x_1812_, 3);
lean_inc(v_l_1814_);
v_r_1815_ = lean_ctor_get(v_x_1812_, 4);
lean_inc(v_r_1815_);
lean_dec_ref_known(v_x_1812_, 5);
v___x_1816_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1811_, v_l_1814_);
v___x_1817_ = lean_array_push(v___x_1816_, v_k_1813_);
v_init_1811_ = v___x_1817_;
v_x_1812_ = v_r_1815_;
goto _start;
}
else
{
return v_init_1811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1819_, lean_object* v_es_1820_){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___y_1824_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___y_1835_; lean_object* v___y_1836_; uint8_t v___x_1838_; 
v___x_1821_ = lean_unsigned_to_nat(0u);
v___x_1822_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1832_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1822_, v_es_1820_);
v___x_1833_ = lean_array_get_size(v___x_1832_);
v___x_1838_ = lean_nat_dec_eq(v___x_1833_, v___x_1821_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___y_1842_; uint8_t v___x_1844_; 
v___x_1839_ = lean_unsigned_to_nat(1u);
v___x_1840_ = lean_nat_sub(v___x_1833_, v___x_1839_);
v___x_1844_ = lean_nat_dec_le(v___x_1821_, v___x_1840_);
if (v___x_1844_ == 0)
{
lean_inc(v___x_1840_);
v___y_1842_ = v___x_1840_;
goto v___jp_1841_;
}
else
{
v___y_1842_ = v___x_1821_;
goto v___jp_1841_;
}
v___jp_1841_:
{
uint8_t v___x_1843_; 
v___x_1843_ = lean_nat_dec_le(v___y_1842_, v___x_1840_);
if (v___x_1843_ == 0)
{
lean_dec(v___x_1840_);
lean_inc(v___y_1842_);
v___y_1835_ = v___y_1842_;
v___y_1836_ = v___y_1842_;
goto v___jp_1834_;
}
else
{
v___y_1835_ = v___y_1842_;
v___y_1836_ = v___x_1840_;
goto v___jp_1834_;
}
}
}
else
{
v___y_1824_ = v___x_1832_;
goto v___jp_1823_;
}
v___jp_1823_:
{
lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = lean_array_get_size(v___y_1824_);
v___x_1826_ = lean_nat_dec_lt(v___x_1821_, v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; 
lean_dec_ref(v_env_1819_);
v___x_1827_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1822_);
lean_ctor_set(v___x_1827_, 1, v___x_1822_);
lean_ctor_set(v___x_1827_, 2, v___y_1824_);
return v___x_1827_;
}
else
{
size_t v___x_1828_; size_t v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1828_ = ((size_t)0ULL);
v___x_1829_ = lean_usize_of_nat(v___x_1825_);
v___x_1830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1819_, v___y_1824_, v___x_1828_, v___x_1829_, v___x_1822_);
lean_inc_ref(v___x_1830_);
v___x_1831_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
lean_ctor_set(v___x_1831_, 2, v___y_1824_);
return v___x_1831_;
}
}
v___jp_1834_:
{
lean_object* v___x_1837_; 
v___x_1837_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1833_, v___x_1832_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
v___y_1824_ = v___x_1837_;
goto v___jp_1823_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v_name_1845_, lean_object* v_decl_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1850_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1851_ = l_Lean_MessageData_ofName(v_name_1845_);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1852_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1854_, v___y_1847_, v___y_1848_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v_name_1856_, lean_object* v_decl_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_registerTagAttribute___lam__4(v_name_1856_, v_decl_1857_, v___y_1858_, v___y_1859_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v_decl_1857_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1862_, lean_object* v_x_1863_, lean_object* v_x_1864_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1862_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1867_, lean_object* v_x_1868_, lean_object* v_x_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_registerTagAttribute___lam__5(v___x_1867_, v_x_1868_, v_x_1869_);
lean_dec_ref(v_x_1869_);
lean_dec_ref(v_x_1868_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v___x_1872_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1872_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v___x_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_registerTagAttribute___lam__6(v___x_1875_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_a_1878_, lean_object* v_decl_1879_, lean_object* v_s_1880_){
_start:
{
lean_object* v_addEntryFn_1881_; lean_object* v_importedEntries_1882_; lean_object* v_state_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1891_; 
v_addEntryFn_1881_ = lean_ctor_get(v_a_1878_, 3);
lean_inc(v_addEntryFn_1881_);
lean_dec_ref(v_a_1878_);
v_importedEntries_1882_ = lean_ctor_get(v_s_1880_, 0);
v_state_1883_ = lean_ctor_get(v_s_1880_, 1);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_s_1880_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1885_ = v_s_1880_;
v_isShared_1886_ = v_isSharedCheck_1891_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_state_1883_);
lean_inc(v_importedEntries_1882_);
lean_dec(v_s_1880_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1891_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v_state_1887_; lean_object* v___x_1889_; 
v_state_1887_ = lean_apply_2(v_addEntryFn_1881_, v_state_1883_, v_decl_1879_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 1, v_state_1887_);
v___x_1889_ = v___x_1885_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_importedEntries_1882_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_state_1887_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1892_, lean_object* v_declName_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1897_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1898_ = l_Lean_MessageData_ofName(v_attrName_1892_);
v___x_1899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1897_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = 0;
v___x_1903_ = l_Lean_MessageData_ofConstName(v_declName_1893_, v___x_1902_);
v___x_1904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1901_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1904_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1906_, v___y_1894_, v___y_1895_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1908_, lean_object* v_declName_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1908_, v_declName_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1914_, lean_object* v_declName_1915_, lean_object* v_asyncPrefix_x3f_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v___y_1921_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1916_) == 0)
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_MessageData_nil;
v___y_1921_ = v___x_1934_;
goto v___jp_1920_;
}
else
{
lean_object* v_val_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v_val_1935_ = lean_ctor_get(v_asyncPrefix_x3f_1916_, 0);
lean_inc(v_val_1935_);
lean_dec_ref_known(v_asyncPrefix_x3f_1916_, 1);
v___x_1936_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1937_ = l_Lean_MessageData_ofName(v_val_1935_);
v___x_1938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1936_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1938_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___y_1921_ = v___x_1940_;
goto v___jp_1920_;
}
v___jp_1920_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1922_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1923_ = l_Lean_MessageData_ofName(v_attrName_1914_);
v___x_1924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = 0;
v___x_1928_ = l_Lean_MessageData_ofConstName(v_declName_1915_, v___x_1927_);
v___x_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1926_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
lean_ctor_set(v___x_1932_, 1, v___y_1921_);
v___x_1933_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1932_, v___y_1917_, v___y_1918_);
return v___x_1933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1941_, lean_object* v_declName_1942_, lean_object* v_asyncPrefix_x3f_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1941_, v_declName_1942_, v_asyncPrefix_x3f_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1948_, uint8_t v_kind_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___y_1959_; 
v___x_1953_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1954_ = l_Lean_MessageData_ofName(v_name_1948_);
v___x_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
switch(v_kind_1949_)
{
case 0:
{
lean_object* v___x_1966_; 
v___x_1966_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1959_ = v___x_1966_;
goto v___jp_1958_;
}
case 1:
{
lean_object* v___x_1967_; 
v___x_1967_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1959_ = v___x_1967_;
goto v___jp_1958_;
}
default: 
{
lean_object* v___x_1968_; 
v___x_1968_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1959_ = v___x_1968_;
goto v___jp_1958_;
}
}
v___jp_1958_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_inc_ref(v___y_1959_);
v___x_1960_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1960_, 0, v___y_1959_);
v___x_1961_ = l_Lean_MessageData_ofFormat(v___x_1960_);
v___x_1962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1957_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1964_, v___y_1950_, v___y_1951_);
return v___x_1965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_1969_, lean_object* v_kind_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
uint8_t v_kind_boxed_1974_; lean_object* v_res_1975_; 
v_kind_boxed_1974_ = lean_unbox(v_kind_1970_);
v_res_1975_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1969_, v_kind_boxed_1974_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__8(lean_object* v_a_1976_, lean_object* v_validate_1977_, lean_object* v_name_1978_, lean_object* v_decl_1979_, lean_object* v_stx_1980_, uint8_t v_kind_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v___y_1986_; lean_object* v_nextMacroScope_1987_; lean_object* v_ngen_1988_; lean_object* v_auxDeclNGen_1989_; lean_object* v_traceState_1990_; lean_object* v_recordedDeps_1991_; lean_object* v_messages_1992_; lean_object* v_infoState_1993_; lean_object* v_snapshotTasks_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___f_2001_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___x_2038_; 
lean_inc(v_decl_1979_);
lean_inc_ref(v_a_1976_);
v___f_2001_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7), 3, 2);
lean_closure_set(v___f_2001_, 0, v_a_1976_);
lean_closure_set(v___f_2001_, 1, v_decl_1979_);
v___x_2038_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1980_, v___y_1982_, v___y_1983_);
if (lean_obj_tag(v___x_2038_) == 0)
{
uint8_t v___x_2039_; uint8_t v___x_2040_; 
lean_dec_ref_known(v___x_2038_, 1);
v___x_2039_ = 0;
v___x_2040_ = l_Lean_instBEqAttributeKind_beq(v_kind_1981_, v___x_2039_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; 
lean_dec_ref(v___f_2001_);
lean_dec(v_decl_1979_);
lean_dec_ref(v_validate_1977_);
lean_dec_ref(v_a_1976_);
v___x_2041_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1978_, v_kind_1981_, v___y_1982_, v___y_1983_);
return v___x_2041_;
}
else
{
goto v___jp_2033_;
}
}
else
{
lean_dec_ref(v___f_2001_);
lean_dec(v_decl_1979_);
lean_dec(v_name_1978_);
lean_dec_ref(v_validate_1977_);
lean_dec_ref(v_a_1976_);
return v___x_2038_;
}
v___jp_1985_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1997_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_1998_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1998_, 0, v___y_1996_);
lean_ctor_set(v___x_1998_, 1, v_nextMacroScope_1987_);
lean_ctor_set(v___x_1998_, 2, v_ngen_1988_);
lean_ctor_set(v___x_1998_, 3, v_auxDeclNGen_1989_);
lean_ctor_set(v___x_1998_, 4, v_traceState_1990_);
lean_ctor_set(v___x_1998_, 5, v___x_1997_);
lean_ctor_set(v___x_1998_, 6, v_recordedDeps_1991_);
lean_ctor_set(v___x_1998_, 7, v_messages_1992_);
lean_ctor_set(v___x_1998_, 8, v_infoState_1993_);
lean_ctor_set(v___x_1998_, 9, v_snapshotTasks_1994_);
v___x_1999_ = lean_st_ref_put(v___y_1995_, v___x_1998_);
v___x_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2000_, 0, v___y_1986_);
return v___x_2000_;
}
v___jp_2002_:
{
lean_object* v___x_2005_; 
lean_inc(v___y_2004_);
lean_inc_ref(v___y_2003_);
lean_inc(v_decl_1979_);
v___x_2005_ = lean_apply_4(v_validate_1977_, v_decl_1979_, v___y_2003_, v___y_2004_, lean_box(0));
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v___x_2006_; lean_object* v_toEnvExtension_2007_; lean_object* v_env_2008_; lean_object* v_nextMacroScope_2009_; lean_object* v_ngen_2010_; lean_object* v_auxDeclNGen_2011_; lean_object* v_traceState_2012_; lean_object* v_recordedDeps_2013_; lean_object* v_messages_2014_; lean_object* v_infoState_2015_; lean_object* v_snapshotTasks_2016_; lean_object* v_asyncMode_2017_; uint8_t v_logWrites_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; 
lean_dec_ref_known(v___x_2005_, 1);
v___x_2006_ = lean_st_ref_take(v___y_2004_);
v_toEnvExtension_2007_ = lean_ctor_get(v_a_1976_, 0);
lean_inc_ref(v_toEnvExtension_2007_);
lean_dec_ref(v_a_1976_);
v_env_2008_ = lean_ctor_get(v___x_2006_, 0);
lean_inc_ref(v_env_2008_);
v_nextMacroScope_2009_ = lean_ctor_get(v___x_2006_, 1);
lean_inc(v_nextMacroScope_2009_);
v_ngen_2010_ = lean_ctor_get(v___x_2006_, 2);
lean_inc_ref(v_ngen_2010_);
v_auxDeclNGen_2011_ = lean_ctor_get(v___x_2006_, 3);
lean_inc_ref(v_auxDeclNGen_2011_);
v_traceState_2012_ = lean_ctor_get(v___x_2006_, 4);
lean_inc_ref(v_traceState_2012_);
v_recordedDeps_2013_ = lean_ctor_get(v___x_2006_, 6);
lean_inc_ref(v_recordedDeps_2013_);
v_messages_2014_ = lean_ctor_get(v___x_2006_, 7);
lean_inc_ref(v_messages_2014_);
v_infoState_2015_ = lean_ctor_get(v___x_2006_, 8);
lean_inc_ref(v_infoState_2015_);
v_snapshotTasks_2016_ = lean_ctor_get(v___x_2006_, 9);
lean_inc_ref(v_snapshotTasks_2016_);
lean_dec(v___x_2006_);
v_asyncMode_2017_ = lean_ctor_get(v_toEnvExtension_2007_, 2);
lean_inc(v_asyncMode_2017_);
v_logWrites_2018_ = lean_ctor_get_uint8(v_toEnvExtension_2007_, sizeof(void*)*6);
v___x_2019_ = lean_box(0);
v___x_2020_ = 1;
if (v_logWrites_2018_ == 0)
{
lean_object* v___x_2021_; 
v___x_2021_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2007_, v_env_2008_, v___f_2001_, v_asyncMode_2017_, v_decl_1979_, v___x_2020_);
lean_dec(v_asyncMode_2017_);
v___y_1986_ = v___x_2019_;
v_nextMacroScope_1987_ = v_nextMacroScope_2009_;
v_ngen_1988_ = v_ngen_2010_;
v_auxDeclNGen_1989_ = v_auxDeclNGen_2011_;
v_traceState_1990_ = v_traceState_2012_;
v_recordedDeps_1991_ = v_recordedDeps_2013_;
v_messages_1992_ = v_messages_2014_;
v_infoState_1993_ = v_infoState_2015_;
v_snapshotTasks_1994_ = v_snapshotTasks_2016_;
v___y_1995_ = v___y_2004_;
v___y_1996_ = v___x_2021_;
goto v___jp_1985_;
}
else
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_inc(v_decl_1979_);
v___x_2022_ = l_Lean_Environment_logDeclChange(v_env_2008_, v_decl_1979_);
v___x_2023_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2007_, v___x_2022_, v___f_2001_, v_asyncMode_2017_, v_decl_1979_, v___x_2020_);
lean_dec(v_asyncMode_2017_);
v___y_1986_ = v___x_2019_;
v_nextMacroScope_1987_ = v_nextMacroScope_2009_;
v_ngen_1988_ = v_ngen_2010_;
v_auxDeclNGen_1989_ = v_auxDeclNGen_2011_;
v_traceState_1990_ = v_traceState_2012_;
v_recordedDeps_1991_ = v_recordedDeps_2013_;
v_messages_1992_ = v_messages_2014_;
v_infoState_1993_ = v_infoState_2015_;
v_snapshotTasks_1994_ = v_snapshotTasks_2016_;
v___y_1995_ = v___y_2004_;
v___y_1996_ = v___x_2023_;
goto v___jp_1985_;
}
}
else
{
lean_dec_ref(v___f_2001_);
lean_dec(v_decl_1979_);
lean_dec_ref(v_a_1976_);
return v___x_2005_;
}
}
v___jp_2024_:
{
lean_object* v_toEnvExtension_2028_; lean_object* v_asyncMode_2029_; uint8_t v___x_2030_; 
v_toEnvExtension_2028_ = lean_ctor_get(v_a_1976_, 0);
v_asyncMode_2029_ = lean_ctor_get(v_toEnvExtension_2028_, 2);
lean_inc(v_decl_1979_);
lean_inc_ref(v___y_2025_);
v___x_2030_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2025_, v_decl_1979_, v_asyncMode_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
lean_dec_ref(v___f_2001_);
lean_dec_ref(v_validate_1977_);
lean_dec_ref(v_a_1976_);
v___x_2031_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2025_);
v___x_2032_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_1978_, v_decl_1979_, v___x_2031_, v___y_2026_, v___y_2027_);
return v___x_2032_;
}
else
{
lean_dec_ref(v___y_2025_);
lean_dec(v_name_1978_);
v___y_2003_ = v___y_2026_;
v___y_2004_ = v___y_2027_;
goto v___jp_2002_;
}
}
v___jp_2033_:
{
lean_object* v___x_2034_; lean_object* v_env_2035_; lean_object* v___x_2036_; 
v___x_2034_ = lean_st_ref_get(v___y_1983_);
v_env_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc_ref(v_env_2035_);
lean_dec(v___x_2034_);
v___x_2036_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2035_, v_decl_1979_);
if (lean_obj_tag(v___x_2036_) == 0)
{
v___y_2025_ = v_env_2035_;
v___y_2026_ = v___y_1982_;
v___y_2027_ = v___y_1983_;
goto v___jp_2024_;
}
else
{
lean_object* v___x_2037_; 
lean_dec_ref_known(v___x_2036_, 1);
lean_dec_ref(v_env_2035_);
lean_dec_ref(v___f_2001_);
lean_dec_ref(v_validate_1977_);
lean_dec_ref(v_a_1976_);
v___x_2037_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_1978_, v_decl_1979_, v___y_1982_, v___y_1983_);
return v___x_2037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__8___boxed(lean_object* v_a_2042_, lean_object* v_validate_2043_, lean_object* v_name_2044_, lean_object* v_decl_2045_, lean_object* v_stx_2046_, lean_object* v_kind_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
uint8_t v_kind_boxed_2051_; lean_object* v_res_2052_; 
v_kind_boxed_2051_ = lean_unbox(v_kind_2047_);
v_res_2052_ = l_Lean_registerTagAttribute___lam__8(v_a_2042_, v_validate_2043_, v_name_2044_, v_decl_2045_, v_stx_2046_, v_kind_boxed_2051_, v___y_2048_, v___y_2049_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
return v_res_2052_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2058_; lean_object* v___f_2059_; 
v___x_2058_ = l_Lean_NameSet_empty;
v___f_2059_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 4, 1);
lean_closure_set(v___f_2059_, 0, v___x_2058_);
return v___f_2059_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2060_; lean_object* v___f_2061_; 
v___x_2060_ = l_Lean_NameSet_empty;
v___f_2061_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 2, 1);
lean_closure_set(v___f_2061_, 0, v___x_2060_);
return v___f_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2064_, lean_object* v_descr_2065_, lean_object* v_validate_2066_, lean_object* v_ref_2067_, uint8_t v_applicationTime_2068_, lean_object* v_asyncMode_2069_, uint8_t v_logWrites_2070_){
_start:
{
lean_object* v___f_2072_; lean_object* v___f_2073_; lean_object* v___f_2074_; lean_object* v___f_2075_; lean_object* v___f_2076_; lean_object* v___f_2077_; lean_object* v___f_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___f_2072_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2073_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2074_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2075_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
lean_inc(v_name_2064_);
v___f_2076_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 5, 1);
lean_closure_set(v___f_2076_, 0, v_name_2064_);
v___f_2077_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2078_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2079_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
v___x_2080_ = 0;
lean_inc(v_ref_2067_);
v___x_2081_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2081_, 0, v_ref_2067_);
lean_ctor_set(v___x_2081_, 1, v___f_2078_);
lean_ctor_set(v___x_2081_, 2, v___f_2077_);
lean_ctor_set(v___x_2081_, 3, v___f_2075_);
lean_ctor_set(v___x_2081_, 4, v___f_2074_);
lean_ctor_set(v___x_2081_, 5, v___f_2073_);
lean_ctor_set(v___x_2081_, 6, v_asyncMode_2069_);
lean_ctor_set(v___x_2081_, 7, v___x_2079_);
lean_ctor_set_uint8(v___x_2081_, sizeof(void*)*8, v___x_2080_);
lean_ctor_set_uint8(v___x_2081_, sizeof(void*)*8 + 1, v_logWrites_2070_);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
lean_ctor_set(v___x_2082_, 1, v___f_2072_);
v___x_2083_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2082_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v___f_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc_n(v_a_2084_, 2);
lean_dec_ref_known(v___x_2083_, 1);
lean_inc(v_name_2064_);
v___f_2085_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__8___boxed), 9, 3);
lean_closure_set(v___f_2085_, 0, v_a_2084_);
lean_closure_set(v___f_2085_, 1, v_validate_2066_);
lean_closure_set(v___f_2085_, 2, v_name_2064_);
v___x_2086_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2086_, 0, v_ref_2067_);
lean_ctor_set(v___x_2086_, 1, v_name_2064_);
lean_ctor_set(v___x_2086_, 2, v_descr_2065_);
lean_ctor_set_uint8(v___x_2086_, sizeof(void*)*3, v_applicationTime_2068_);
v___x_2087_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
lean_ctor_set(v___x_2087_, 1, v___f_2085_);
lean_ctor_set(v___x_2087_, 2, v___f_2076_);
lean_inc_ref(v___x_2087_);
v___x_2088_ = l_Lean_registerBuiltinAttribute(v___x_2087_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2096_; 
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2096_ == 0)
{
lean_object* v_unused_2097_; 
v_unused_2097_ = lean_ctor_get(v___x_2088_, 0);
lean_dec(v_unused_2097_);
v___x_2090_ = v___x_2088_;
v_isShared_2091_ = v_isSharedCheck_2096_;
goto v_resetjp_2089_;
}
else
{
lean_dec(v___x_2088_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2096_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2092_; lean_object* v___x_2094_; 
v___x_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2087_);
lean_ctor_set(v___x_2092_, 1, v_a_2084_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2092_);
v___x_2094_ = v___x_2090_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec_ref_known(v___x_2087_, 3);
lean_dec(v_a_2084_);
v_a_2098_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2088_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2088_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec_ref(v___f_2076_);
lean_dec(v_ref_2067_);
lean_dec_ref(v_validate_2066_);
lean_dec_ref(v_descr_2065_);
lean_dec(v_name_2064_);
v_a_2106_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2083_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2083_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2114_, lean_object* v_descr_2115_, lean_object* v_validate_2116_, lean_object* v_ref_2117_, lean_object* v_applicationTime_2118_, lean_object* v_asyncMode_2119_, lean_object* v_logWrites_2120_, lean_object* v_a_2121_){
_start:
{
uint8_t v_applicationTime_boxed_2122_; uint8_t v_logWrites_boxed_2123_; lean_object* v_res_2124_; 
v_applicationTime_boxed_2122_ = lean_unbox(v_applicationTime_2118_);
v_logWrites_boxed_2123_ = lean_unbox(v_logWrites_2120_);
v_res_2124_ = l_Lean_registerTagAttribute(v_name_2114_, v_descr_2115_, v_validate_2116_, v_ref_2117_, v_applicationTime_boxed_2122_, v_asyncMode_2119_, v_logWrites_boxed_2123_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2125_, lean_object* v_t_2126_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2125_, v_t_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2128_, lean_object* v_as_2129_, lean_object* v_lo_2130_, lean_object* v_hi_2131_, lean_object* v_w_2132_, lean_object* v_hlo_2133_, lean_object* v_hhi_2134_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2128_, v_as_2129_, v_lo_2130_, v_hi_2131_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2136_, lean_object* v_as_2137_, lean_object* v_lo_2138_, lean_object* v_hi_2139_, lean_object* v_w_2140_, lean_object* v_hlo_2141_, lean_object* v_hhi_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2136_, v_as_2137_, v_lo_2138_, v_hi_2139_, v_w_2140_, v_hlo_2141_, v_hhi_2142_);
lean_dec(v_hi_2139_);
lean_dec(v_n_2136_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2144_, lean_object* v_attrName_2145_, lean_object* v_declName_2146_, lean_object* v_asyncPrefix_x3f_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2145_, v_declName_2146_, v_asyncPrefix_x3f_2147_, v___y_2148_, v___y_2149_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2152_, lean_object* v_attrName_2153_, lean_object* v_declName_2154_, lean_object* v_asyncPrefix_x3f_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2152_, v_attrName_2153_, v_declName_2154_, v_asyncPrefix_x3f_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2160_, lean_object* v_attrName_2161_, lean_object* v_declName_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2161_, v_declName_2162_, v___y_2163_, v___y_2164_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2167_, lean_object* v_attrName_2168_, lean_object* v_declName_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2167_, v_attrName_2168_, v_declName_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2174_, lean_object* v_name_2175_, uint8_t v_kind_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2175_, v_kind_2176_, v___y_2177_, v___y_2178_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2181_, lean_object* v_name_2182_, lean_object* v_kind_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
uint8_t v_kind_boxed_2187_; lean_object* v_res_2188_; 
v_kind_boxed_2187_ = lean_unbox(v_kind_2183_);
v_res_2188_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2181_, v_name_2182_, v_kind_boxed_2187_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2189_, lean_object* v_lo_2190_, lean_object* v_hi_2191_, lean_object* v_hhi_2192_, lean_object* v_pivot_2193_, lean_object* v_as_2194_, lean_object* v_i_2195_, lean_object* v_k_2196_, lean_object* v_ilo_2197_, lean_object* v_ik_2198_, lean_object* v_w_2199_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2191_, v_pivot_2193_, v_as_2194_, v_i_2195_, v_k_2196_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2201_, lean_object* v_lo_2202_, lean_object* v_hi_2203_, lean_object* v_hhi_2204_, lean_object* v_pivot_2205_, lean_object* v_as_2206_, lean_object* v_i_2207_, lean_object* v_k_2208_, lean_object* v_ilo_2209_, lean_object* v_ik_2210_, lean_object* v_w_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2201_, v_lo_2202_, v_hi_2203_, v_hhi_2204_, v_pivot_2205_, v_as_2206_, v_i_2207_, v_k_2208_, v_ilo_2209_, v_ik_2210_, v_w_2211_);
lean_dec(v_pivot_2205_);
lean_dec(v_hi_2203_);
lean_dec(v_lo_2202_);
lean_dec(v_n_2201_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_addEntryFn_2213_, lean_object* v_decl_2214_, lean_object* v_s_2215_){
_start:
{
lean_object* v_importedEntries_2216_; lean_object* v_state_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2225_; 
v_importedEntries_2216_ = lean_ctor_get(v_s_2215_, 0);
v_state_2217_ = lean_ctor_get(v_s_2215_, 1);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_s_2215_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2219_ = v_s_2215_;
v_isShared_2220_ = v_isSharedCheck_2225_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_state_2217_);
lean_inc(v_importedEntries_2216_);
lean_dec(v_s_2215_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2225_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v_state_2221_; lean_object* v___x_2223_; 
v_state_2221_ = lean_apply_2(v_addEntryFn_2213_, v_state_2217_, v_decl_2214_);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 1, v_state_2221_);
v___x_2223_ = v___x_2219_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_importedEntries_2216_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_state_2221_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_attr_2226_, lean_object* v_decl_2227_, lean_object* v_env_2228_){
_start:
{
lean_object* v_ext_2229_; lean_object* v_toEnvExtension_2230_; lean_object* v_addEntryFn_2231_; lean_object* v_asyncMode_2232_; uint8_t v_logWrites_2233_; lean_object* v___f_2234_; uint8_t v___x_2235_; 
v_ext_2229_ = lean_ctor_get(v_attr_2226_, 1);
lean_inc_ref(v_ext_2229_);
lean_dec_ref(v_attr_2226_);
v_toEnvExtension_2230_ = lean_ctor_get(v_ext_2229_, 0);
lean_inc_ref(v_toEnvExtension_2230_);
v_addEntryFn_2231_ = lean_ctor_get(v_ext_2229_, 3);
lean_inc(v_addEntryFn_2231_);
lean_dec_ref(v_ext_2229_);
v_asyncMode_2232_ = lean_ctor_get(v_toEnvExtension_2230_, 2);
lean_inc(v_asyncMode_2232_);
v_logWrites_2233_ = lean_ctor_get_uint8(v_toEnvExtension_2230_, sizeof(void*)*6);
lean_inc(v_decl_2227_);
v___f_2234_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2234_, 0, v_addEntryFn_2231_);
lean_closure_set(v___f_2234_, 1, v_decl_2227_);
v___x_2235_ = 1;
if (v_logWrites_2233_ == 0)
{
lean_object* v___x_2236_; 
v___x_2236_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2230_, v_env_2228_, v___f_2234_, v_asyncMode_2232_, v_decl_2227_, v___x_2235_);
lean_dec(v_asyncMode_2232_);
return v___x_2236_;
}
else
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
lean_inc_ref(v_toEnvExtension_2230_);
v___x_2237_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2230_, v_env_2228_);
lean_dec_ref(v_env_2228_);
v___x_2238_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2230_, v___x_2237_, v___f_2234_, v_asyncMode_2232_, v_decl_2227_, v___x_2235_);
lean_dec(v_asyncMode_2232_);
return v___x_2238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_modifyEnv_2239_, lean_object* v___f_2240_, lean_object* v_____r_2241_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = lean_apply_1(v_modifyEnv_2239_, v___f_2240_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v_attr_2243_, lean_object* v_env_2244_, lean_object* v_decl_2245_, lean_object* v_inst_2246_, lean_object* v_inst_2247_, lean_object* v_toBind_2248_, lean_object* v___f_2249_, lean_object* v_modifyEnv_2250_, lean_object* v___f_2251_, lean_object* v_____r_2252_){
_start:
{
lean_object* v_ext_2253_; lean_object* v_toEnvExtension_2254_; lean_object* v_attr_2255_; lean_object* v_asyncMode_2256_; uint8_t v___x_2257_; 
v_ext_2253_ = lean_ctor_get(v_attr_2243_, 1);
v_toEnvExtension_2254_ = lean_ctor_get(v_ext_2253_, 0);
lean_inc_ref(v_toEnvExtension_2254_);
v_attr_2255_ = lean_ctor_get(v_attr_2243_, 0);
lean_inc_ref(v_attr_2255_);
lean_dec_ref(v_attr_2243_);
v_asyncMode_2256_ = lean_ctor_get(v_toEnvExtension_2254_, 2);
lean_inc(v_asyncMode_2256_);
lean_dec_ref(v_toEnvExtension_2254_);
lean_inc(v_decl_2245_);
lean_inc_ref(v_env_2244_);
v___x_2257_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2244_, v_decl_2245_, v_asyncMode_2256_);
lean_dec(v_asyncMode_2256_);
if (v___x_2257_ == 0)
{
lean_object* v_toAttributeImplCore_2258_; lean_object* v_name_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_dec_ref(v___f_2251_);
lean_dec(v_modifyEnv_2250_);
v_toAttributeImplCore_2258_ = lean_ctor_get(v_attr_2255_, 0);
lean_inc_ref(v_toAttributeImplCore_2258_);
lean_dec_ref(v_attr_2255_);
v_name_2259_ = lean_ctor_get(v_toAttributeImplCore_2258_, 1);
lean_inc(v_name_2259_);
lean_dec_ref(v_toAttributeImplCore_2258_);
v___x_2260_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2244_);
v___x_2261_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2246_, v_inst_2247_, v_name_2259_, v_decl_2245_, v___x_2260_);
v___x_2262_ = lean_apply_4(v_toBind_2248_, lean_box(0), lean_box(0), v___x_2261_, v___f_2249_);
return v___x_2262_;
}
else
{
lean_object* v___x_2263_; 
lean_dec_ref(v_attr_2255_);
lean_dec(v___f_2249_);
lean_dec(v_toBind_2248_);
lean_dec_ref(v_inst_2247_);
lean_dec_ref(v_inst_2246_);
lean_dec(v_decl_2245_);
lean_dec_ref(v_env_2244_);
v___x_2263_ = lean_apply_1(v_modifyEnv_2250_, v___f_2251_);
return v___x_2263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v___f_2264_, lean_object* v_____r_2265_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = lean_apply_1(v___f_2264_, v_____r_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__5(lean_object* v_attr_2267_, lean_object* v_decl_2268_, lean_object* v_inst_2269_, lean_object* v_inst_2270_, lean_object* v_toBind_2271_, lean_object* v___f_2272_, lean_object* v_modifyEnv_2273_, lean_object* v___f_2274_, lean_object* v_env_2275_){
_start:
{
lean_object* v___f_2276_; lean_object* v___x_2277_; 
lean_inc_ref(v___f_2274_);
lean_inc(v_modifyEnv_2273_);
lean_inc(v___f_2272_);
lean_inc(v_toBind_2271_);
lean_inc_ref(v_inst_2270_);
lean_inc_ref(v_inst_2269_);
lean_inc(v_decl_2268_);
lean_inc_ref(v_env_2275_);
lean_inc_ref(v_attr_2267_);
v___f_2276_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 10, 9);
lean_closure_set(v___f_2276_, 0, v_attr_2267_);
lean_closure_set(v___f_2276_, 1, v_env_2275_);
lean_closure_set(v___f_2276_, 2, v_decl_2268_);
lean_closure_set(v___f_2276_, 3, v_inst_2269_);
lean_closure_set(v___f_2276_, 4, v_inst_2270_);
lean_closure_set(v___f_2276_, 5, v_toBind_2271_);
lean_closure_set(v___f_2276_, 6, v___f_2272_);
lean_closure_set(v___f_2276_, 7, v_modifyEnv_2273_);
lean_closure_set(v___f_2276_, 8, v___f_2274_);
v___x_2277_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2275_, v_decl_2268_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_dec_ref(v___f_2276_);
v___x_2278_ = lean_box(0);
v___x_2279_ = l_Lean_TagAttribute_setTag___redArg___lam__3(v_attr_2267_, v_env_2275_, v_decl_2268_, v_inst_2269_, v_inst_2270_, v_toBind_2271_, v___f_2272_, v_modifyEnv_2273_, v___f_2274_, v___x_2278_);
return v___x_2279_;
}
else
{
lean_object* v_attr_2280_; lean_object* v_toAttributeImplCore_2281_; lean_object* v_name_2282_; lean_object* v___f_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
lean_dec_ref_known(v___x_2277_, 1);
lean_dec_ref(v_env_2275_);
lean_dec_ref(v___f_2274_);
lean_dec(v_modifyEnv_2273_);
lean_dec(v___f_2272_);
v_attr_2280_ = lean_ctor_get(v_attr_2267_, 0);
lean_inc_ref(v_attr_2280_);
lean_dec_ref(v_attr_2267_);
v_toAttributeImplCore_2281_ = lean_ctor_get(v_attr_2280_, 0);
lean_inc_ref(v_toAttributeImplCore_2281_);
lean_dec_ref(v_attr_2280_);
v_name_2282_ = lean_ctor_get(v_toAttributeImplCore_2281_, 1);
lean_inc(v_name_2282_);
lean_dec_ref(v_toAttributeImplCore_2281_);
v___f_2283_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2283_, 0, v___f_2276_);
v___x_2284_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2269_, v_inst_2270_, v_name_2282_, v_decl_2268_);
v___x_2285_ = lean_apply_4(v_toBind_2271_, lean_box(0), lean_box(0), v___x_2284_, v___f_2283_);
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2286_, lean_object* v_inst_2287_, lean_object* v_inst_2288_, lean_object* v_attr_2289_, lean_object* v_decl_2290_){
_start:
{
lean_object* v_toBind_2291_; lean_object* v_getEnv_2292_; lean_object* v_modifyEnv_2293_; lean_object* v___f_2294_; lean_object* v___f_2295_; lean_object* v___f_2296_; lean_object* v___x_2297_; 
v_toBind_2291_ = lean_ctor_get(v_inst_2286_, 1);
lean_inc_n(v_toBind_2291_, 2);
v_getEnv_2292_ = lean_ctor_get(v_inst_2288_, 0);
lean_inc(v_getEnv_2292_);
v_modifyEnv_2293_ = lean_ctor_get(v_inst_2288_, 1);
lean_inc_n(v_modifyEnv_2293_, 2);
lean_dec_ref(v_inst_2288_);
lean_inc(v_decl_2290_);
lean_inc_ref(v_attr_2289_);
v___f_2294_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2294_, 0, v_attr_2289_);
lean_closure_set(v___f_2294_, 1, v_decl_2290_);
lean_inc_ref(v___f_2294_);
v___f_2295_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2295_, 0, v_modifyEnv_2293_);
lean_closure_set(v___f_2295_, 1, v___f_2294_);
v___f_2296_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__5), 9, 8);
lean_closure_set(v___f_2296_, 0, v_attr_2289_);
lean_closure_set(v___f_2296_, 1, v_decl_2290_);
lean_closure_set(v___f_2296_, 2, v_inst_2286_);
lean_closure_set(v___f_2296_, 3, v_inst_2287_);
lean_closure_set(v___f_2296_, 4, v_toBind_2291_);
lean_closure_set(v___f_2296_, 5, v___f_2295_);
lean_closure_set(v___f_2296_, 6, v_modifyEnv_2293_);
lean_closure_set(v___f_2296_, 7, v___f_2294_);
v___x_2297_ = lean_apply_4(v_toBind_2291_, lean_box(0), lean_box(0), v_getEnv_2292_, v___f_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2298_, lean_object* v_inst_2299_, lean_object* v_inst_2300_, lean_object* v_inst_2301_, lean_object* v_attr_2302_, lean_object* v_decl_2303_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2299_, v_inst_2300_, v_inst_2301_, v_attr_2302_, v_decl_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2305_, lean_object* v_env_2306_, lean_object* v_decl_2307_){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = lean_box(1);
v___x_2309_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2306_, v_decl_2307_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_ext_2310_; lean_object* v_toEnvExtension_2311_; lean_object* v_asyncMode_2312_; uint8_t v___x_2313_; lean_object* v___x_2314_; uint8_t v___x_2315_; 
v_ext_2310_ = lean_ctor_get(v_attr_2305_, 1);
v_toEnvExtension_2311_ = lean_ctor_get(v_ext_2310_, 0);
v_asyncMode_2312_ = lean_ctor_get(v_toEnvExtension_2311_, 2);
v___x_2313_ = 0;
lean_inc(v_decl_2307_);
v___x_2314_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2308_, v_ext_2310_, v_env_2306_, v_asyncMode_2312_, v_decl_2307_, v___x_2313_);
v___x_2315_ = l_Lean_NameSet_contains(v___x_2314_, v_decl_2307_);
lean_dec(v_decl_2307_);
lean_dec(v___x_2314_);
return v___x_2315_;
}
else
{
lean_object* v_val_2316_; lean_object* v_ext_2317_; uint8_t v___x_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; 
v_val_2316_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_val_2316_);
lean_dec_ref_known(v___x_2309_, 1);
v_ext_2317_ = lean_ctor_get(v_attr_2305_, 1);
v___x_2318_ = 0;
v___x_2319_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2308_, v_ext_2317_, v_env_2306_, v_val_2316_, v___x_2318_);
lean_dec(v_val_2316_);
lean_dec_ref(v_env_2306_);
v___x_2320_ = l_Lean_containsSortedName(v___x_2319_, v_decl_2307_);
lean_dec(v_decl_2307_);
lean_dec_ref(v___x_2319_);
return v___x_2320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2321_, lean_object* v_env_2322_, lean_object* v_decl_2323_){
_start:
{
uint8_t v_res_2324_; lean_object* v_r_2325_; 
v_res_2324_ = l_Lean_TagAttribute_hasTag(v_attr_2321_, v_env_2322_, v_decl_2323_);
lean_dec_ref(v_attr_2321_);
v_r_2325_ = lean_box(v_res_2324_);
return v_r_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(lean_object* v_x_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0___boxed(lean_object* v_x_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(v_x_2331_, v___y_2332_);
lean_dec_ref(v___y_2332_);
lean_dec_ref(v_x_2331_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(lean_object* v_s_2335_, lean_object* v_x_2336_){
_start:
{
lean_inc_ref(v_s_2335_);
return v_s_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1___boxed(lean_object* v_s_2337_, lean_object* v_x_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(v_s_2337_, v_x_2338_);
lean_dec_ref(v_x_2338_);
lean_dec_ref(v_s_2337_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(lean_object* v_x_2344_, lean_object* v_x_2345_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___boxed(lean_object* v_x_2347_, lean_object* v_x_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(v_x_2347_, v_x_2348_);
lean_dec_ref(v_x_2348_);
lean_dec_ref(v_x_2347_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(lean_object* v_x_2350_){
_start:
{
lean_object* v___x_2351_; 
v___x_2351_ = lean_box(0);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3___boxed(lean_object* v_x_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(v_x_2352_);
lean_dec_ref(v_x_2352_);
return v_res_2353_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4(void){
_start:
{
lean_object* v___f_2358_; lean_object* v___f_2359_; lean_object* v___f_2360_; lean_object* v___f_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___f_2358_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3));
v___f_2359_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2));
v___f_2360_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1));
v___f_2361_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0));
v___x_2362_ = lean_box(0);
v___x_2363_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_2364_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
lean_ctor_set(v___x_2364_, 1, v___x_2362_);
lean_ctor_set(v___x_2364_, 2, v___f_2361_);
lean_ctor_set(v___x_2364_, 3, v___f_2360_);
lean_ctor_set(v___x_2364_, 4, v___f_2359_);
lean_ctor_set(v___x_2364_, 5, v___f_2358_);
return v___x_2364_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5(void){
_start:
{
uint8_t v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2365_ = 0;
v___x_2366_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4);
v___x_2367_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2368_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
lean_ctor_set(v___x_2368_, 1, v___x_2366_);
lean_ctor_set_uint8(v___x_2368_, sizeof(void*)*2, v___x_2365_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg(){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___boxed(lean_object* v___dummy_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v_res_2372_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__0(void){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2374_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg(){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg___boxed(lean_object* v___dummy_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Lean_instInhabitedParametricAttribute___redArg();
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2380_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object* v_x_2382_, lean_object* v_p_2383_){
_start:
{
lean_object* v_fst_2384_; lean_object* v_snd_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2402_; 
v_fst_2384_ = lean_ctor_get(v_x_2382_, 0);
v_snd_2385_ = lean_ctor_get(v_x_2382_, 1);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_x_2382_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2387_ = v_x_2382_;
v_isShared_2388_ = v_isSharedCheck_2402_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_snd_2385_);
lean_inc(v_fst_2384_);
lean_dec(v_x_2382_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2402_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v_fst_2389_; lean_object* v_snd_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2401_; 
v_fst_2389_ = lean_ctor_get(v_p_2383_, 0);
v_snd_2390_ = lean_ctor_get(v_p_2383_, 1);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_p_2383_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2392_ = v_p_2383_;
v_isShared_2393_ = v_isSharedCheck_2401_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_snd_2390_);
lean_inc(v_fst_2389_);
lean_dec(v_p_2383_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2401_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
lean_inc(v_fst_2389_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set_tag(v___x_2387_, 1);
lean_ctor_set(v___x_2387_, 1, v_fst_2384_);
lean_ctor_set(v___x_2387_, 0, v_fst_2389_);
v___x_2395_ = v___x_2387_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_fst_2389_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_fst_2384_);
v___x_2395_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
lean_object* v___x_2396_; lean_object* v___x_2398_; 
v___x_2396_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2389_, v_snd_2390_, v_snd_2385_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 1, v___x_2396_);
lean_ctor_set(v___x_2392_, 0, v___x_2395_);
v___x_2398_ = v___x_2392_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2395_);
lean_ctor_set(v_reuseFailAlloc_2399_, 1, v___x_2396_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object* v_init_2403_, lean_object* v_x_2404_){
_start:
{
if (lean_obj_tag(v_x_2404_) == 0)
{
lean_object* v_k_2405_; lean_object* v_v_2406_; lean_object* v_l_2407_; lean_object* v_r_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_k_2405_ = lean_ctor_get(v_x_2404_, 1);
v_v_2406_ = lean_ctor_get(v_x_2404_, 2);
v_l_2407_ = lean_ctor_get(v_x_2404_, 3);
v_r_2408_ = lean_ctor_get(v_x_2404_, 4);
v___x_2409_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2403_, v_l_2407_);
lean_inc(v_v_2406_);
lean_inc(v_k_2405_);
v___x_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2410_, 0, v_k_2405_);
lean_ctor_set(v___x_2410_, 1, v_v_2406_);
v___x_2411_ = lean_array_push(v___x_2409_, v___x_2410_);
v_init_2403_ = v___x_2411_;
v_x_2404_ = v_r_2408_;
goto _start;
}
else
{
return v_init_2403_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object* v_init_2413_, lean_object* v_x_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2413_, v_x_2414_);
lean_dec(v_x_2414_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object* v_snd_2416_, lean_object* v_as_2417_, size_t v_i_2418_, size_t v_stop_2419_, lean_object* v_b_2420_){
_start:
{
lean_object* v___y_2422_; uint8_t v___x_2426_; 
v___x_2426_ = lean_usize_dec_eq(v_i_2418_, v_stop_2419_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = lean_array_uget_borrowed(v_as_2417_, v_i_2418_);
v___x_2428_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2416_, v___x_2427_);
if (lean_obj_tag(v___x_2428_) == 0)
{
v___y_2422_ = v_b_2420_;
goto v___jp_2421_;
}
else
{
lean_object* v_val_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v_val_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_val_2429_);
lean_dec_ref_known(v___x_2428_, 1);
lean_inc(v___x_2427_);
v___x_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2427_);
lean_ctor_set(v___x_2430_, 1, v_val_2429_);
v___x_2431_ = lean_array_push(v_b_2420_, v___x_2430_);
v___y_2422_ = v___x_2431_;
goto v___jp_2421_;
}
}
else
{
return v_b_2420_;
}
v___jp_2421_:
{
size_t v___x_2423_; size_t v___x_2424_; 
v___x_2423_ = ((size_t)1ULL);
v___x_2424_ = lean_usize_add(v_i_2418_, v___x_2423_);
v_i_2418_ = v___x_2424_;
v_b_2420_ = v___y_2422_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2432_, lean_object* v_as_2433_, lean_object* v_i_2434_, lean_object* v_stop_2435_, lean_object* v_b_2436_){
_start:
{
size_t v_i_boxed_2437_; size_t v_stop_boxed_2438_; lean_object* v_res_2439_; 
v_i_boxed_2437_ = lean_unbox_usize(v_i_2434_);
lean_dec(v_i_2434_);
v_stop_boxed_2438_ = lean_unbox_usize(v_stop_2435_);
lean_dec(v_stop_2435_);
v_res_2439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2432_, v_as_2433_, v_i_boxed_2437_, v_stop_boxed_2438_, v_b_2436_);
lean_dec_ref(v_as_2433_);
lean_dec(v_snd_2432_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object* v_snd_2440_, lean_object* v_as_2441_, lean_object* v_start_2442_, lean_object* v_stop_2443_){
_start:
{
lean_object* v___x_2444_; uint8_t v___x_2445_; 
v___x_2444_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2445_ = lean_nat_dec_lt(v_start_2442_, v_stop_2443_);
if (v___x_2445_ == 0)
{
return v___x_2444_;
}
else
{
lean_object* v___x_2446_; uint8_t v___x_2447_; 
v___x_2446_ = lean_array_get_size(v_as_2441_);
v___x_2447_ = lean_nat_dec_le(v_stop_2443_, v___x_2446_);
if (v___x_2447_ == 0)
{
uint8_t v___x_2448_; 
v___x_2448_ = lean_nat_dec_lt(v_start_2442_, v___x_2446_);
if (v___x_2448_ == 0)
{
return v___x_2444_;
}
else
{
size_t v___x_2449_; size_t v___x_2450_; lean_object* v___x_2451_; 
v___x_2449_ = lean_usize_of_nat(v_start_2442_);
v___x_2450_ = lean_usize_of_nat(v___x_2446_);
v___x_2451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2440_, v_as_2441_, v___x_2449_, v___x_2450_, v___x_2444_);
return v___x_2451_;
}
}
else
{
size_t v___x_2452_; size_t v___x_2453_; lean_object* v___x_2454_; 
v___x_2452_ = lean_usize_of_nat(v_start_2442_);
v___x_2453_ = lean_usize_of_nat(v_stop_2443_);
v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2440_, v_as_2441_, v___x_2452_, v___x_2453_, v___x_2444_);
return v___x_2454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object* v_snd_2455_, lean_object* v_as_2456_, lean_object* v_start_2457_, lean_object* v_stop_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2455_, v_as_2456_, v_start_2457_, v_stop_2458_);
lean_dec(v_stop_2458_);
lean_dec(v_start_2457_);
lean_dec_ref(v_as_2456_);
lean_dec(v_snd_2455_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object* v_hi_2460_, lean_object* v_pivot_2461_, lean_object* v_as_2462_, lean_object* v_i_2463_, lean_object* v_k_2464_){
_start:
{
uint8_t v___x_2465_; 
v___x_2465_ = lean_nat_dec_lt(v_k_2464_, v_hi_2460_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
lean_dec(v_k_2464_);
v___x_2466_ = lean_array_fswap(v_as_2462_, v_i_2463_, v_hi_2460_);
v___x_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2467_, 0, v_i_2463_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
return v___x_2467_;
}
else
{
lean_object* v___x_2468_; lean_object* v_fst_2469_; lean_object* v_fst_2470_; uint8_t v___x_2471_; 
v___x_2468_ = lean_array_fget_borrowed(v_as_2462_, v_k_2464_);
v_fst_2469_ = lean_ctor_get(v___x_2468_, 0);
v_fst_2470_ = lean_ctor_get(v_pivot_2461_, 0);
v___x_2471_ = l_Lean_Name_quickLt(v_fst_2469_, v_fst_2470_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2472_ = lean_unsigned_to_nat(1u);
v___x_2473_ = lean_nat_add(v_k_2464_, v___x_2472_);
lean_dec(v_k_2464_);
v_k_2464_ = v___x_2473_;
goto _start;
}
else
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2475_ = lean_array_fswap(v_as_2462_, v_i_2463_, v_k_2464_);
v___x_2476_ = lean_unsigned_to_nat(1u);
v___x_2477_ = lean_nat_add(v_i_2463_, v___x_2476_);
lean_dec(v_i_2463_);
v___x_2478_ = lean_nat_add(v_k_2464_, v___x_2476_);
lean_dec(v_k_2464_);
v_as_2462_ = v___x_2475_;
v_i_2463_ = v___x_2477_;
v_k_2464_ = v___x_2478_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2480_, lean_object* v_pivot_2481_, lean_object* v_as_2482_, lean_object* v_i_2483_, lean_object* v_k_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2480_, v_pivot_2481_, v_as_2482_, v_i_2483_, v_k_2484_);
lean_dec_ref(v_pivot_2481_);
lean_dec(v_hi_2480_);
return v_res_2485_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object* v_a_2486_, lean_object* v_b_2487_){
_start:
{
lean_object* v_fst_2488_; lean_object* v_fst_2489_; uint8_t v___x_2490_; 
v_fst_2488_ = lean_ctor_get(v_a_2486_, 0);
v_fst_2489_ = lean_ctor_get(v_b_2487_, 0);
v___x_2490_ = l_Lean_Name_quickLt(v_fst_2488_, v_fst_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object* v_a_2491_, lean_object* v_b_2492_){
_start:
{
uint8_t v_res_2493_; lean_object* v_r_2494_; 
v_res_2493_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2491_, v_b_2492_);
lean_dec_ref(v_b_2492_);
lean_dec_ref(v_a_2491_);
v_r_2494_ = lean_box(v_res_2493_);
return v_r_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object* v_n_2495_, lean_object* v_as_2496_, lean_object* v_lo_2497_, lean_object* v_hi_2498_){
_start:
{
lean_object* v___y_2500_; uint8_t v___x_2510_; 
v___x_2510_ = lean_nat_dec_lt(v_lo_2497_, v_hi_2498_);
if (v___x_2510_ == 0)
{
lean_dec(v_lo_2497_);
return v_as_2496_;
}
else
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v_mid_2513_; lean_object* v___y_2515_; lean_object* v___y_2521_; lean_object* v___x_2526_; lean_object* v___x_2527_; uint8_t v___x_2528_; 
v___x_2511_ = lean_nat_add(v_lo_2497_, v_hi_2498_);
v___x_2512_ = lean_unsigned_to_nat(1u);
v_mid_2513_ = lean_nat_shiftr(v___x_2511_, v___x_2512_);
lean_dec(v___x_2511_);
v___x_2526_ = lean_array_fget_borrowed(v_as_2496_, v_mid_2513_);
v___x_2527_ = lean_array_fget_borrowed(v_as_2496_, v_lo_2497_);
v___x_2528_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2526_, v___x_2527_);
if (v___x_2528_ == 0)
{
v___y_2521_ = v_as_2496_;
goto v___jp_2520_;
}
else
{
lean_object* v___x_2529_; 
v___x_2529_ = lean_array_fswap(v_as_2496_, v_lo_2497_, v_mid_2513_);
v___y_2521_ = v___x_2529_;
goto v___jp_2520_;
}
v___jp_2514_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2516_ = lean_array_fget_borrowed(v___y_2515_, v_mid_2513_);
v___x_2517_ = lean_array_fget_borrowed(v___y_2515_, v_hi_2498_);
v___x_2518_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2516_, v___x_2517_);
if (v___x_2518_ == 0)
{
lean_dec(v_mid_2513_);
v___y_2500_ = v___y_2515_;
goto v___jp_2499_;
}
else
{
lean_object* v___x_2519_; 
v___x_2519_ = lean_array_fswap(v___y_2515_, v_mid_2513_, v_hi_2498_);
lean_dec(v_mid_2513_);
v___y_2500_ = v___x_2519_;
goto v___jp_2499_;
}
}
v___jp_2520_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; 
v___x_2522_ = lean_array_fget_borrowed(v___y_2521_, v_hi_2498_);
v___x_2523_ = lean_array_fget_borrowed(v___y_2521_, v_lo_2497_);
v___x_2524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2522_, v___x_2523_);
if (v___x_2524_ == 0)
{
v___y_2515_ = v___y_2521_;
goto v___jp_2514_;
}
else
{
lean_object* v___x_2525_; 
v___x_2525_ = lean_array_fswap(v___y_2521_, v_lo_2497_, v_hi_2498_);
v___y_2515_ = v___x_2525_;
goto v___jp_2514_;
}
}
}
v___jp_2499_:
{
lean_object* v_pivot_2501_; lean_object* v___x_2502_; lean_object* v_fst_2503_; lean_object* v_snd_2504_; uint8_t v___x_2505_; 
v_pivot_2501_ = lean_array_fget(v___y_2500_, v_hi_2498_);
lean_inc_n(v_lo_2497_, 2);
v___x_2502_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2498_, v_pivot_2501_, v___y_2500_, v_lo_2497_, v_lo_2497_);
lean_dec(v_pivot_2501_);
v_fst_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_fst_2503_);
v_snd_2504_ = lean_ctor_get(v___x_2502_, 1);
lean_inc(v_snd_2504_);
lean_dec_ref(v___x_2502_);
v___x_2505_ = lean_nat_dec_le(v_hi_2498_, v_fst_2503_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2506_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2495_, v_snd_2504_, v_lo_2497_, v_fst_2503_);
v___x_2507_ = lean_unsigned_to_nat(1u);
v___x_2508_ = lean_nat_add(v_fst_2503_, v___x_2507_);
lean_dec(v_fst_2503_);
v_as_2496_ = v___x_2506_;
v_lo_2497_ = v___x_2508_;
goto _start;
}
else
{
lean_dec(v_fst_2503_);
lean_dec(v_lo_2497_);
return v_snd_2504_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object* v_n_2530_, lean_object* v_as_2531_, lean_object* v_lo_2532_, lean_object* v_hi_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2530_, v_as_2531_, v_lo_2532_, v_hi_2533_);
lean_dec(v_hi_2533_);
lean_dec(v_n_2530_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object* v_filterExport_2535_, lean_object* v_env_2536_, lean_object* v_as_2537_, size_t v_i_2538_, size_t v_stop_2539_, lean_object* v_b_2540_){
_start:
{
lean_object* v___y_2542_; uint8_t v___x_2546_; 
v___x_2546_ = lean_usize_dec_eq(v_i_2538_, v_stop_2539_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; lean_object* v_fst_2548_; lean_object* v_snd_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; 
v___x_2547_ = lean_array_uget_borrowed(v_as_2537_, v_i_2538_);
v_fst_2548_ = lean_ctor_get(v___x_2547_, 0);
v_snd_2549_ = lean_ctor_get(v___x_2547_, 1);
lean_inc_ref(v_filterExport_2535_);
lean_inc(v_snd_2549_);
lean_inc(v_fst_2548_);
lean_inc_ref(v_env_2536_);
v___x_2550_ = lean_apply_3(v_filterExport_2535_, v_env_2536_, v_fst_2548_, v_snd_2549_);
v___x_2551_ = lean_unbox(v___x_2550_);
if (v___x_2551_ == 0)
{
v___y_2542_ = v_b_2540_;
goto v___jp_2541_;
}
else
{
lean_object* v___x_2552_; 
lean_inc(v___x_2547_);
v___x_2552_ = lean_array_push(v_b_2540_, v___x_2547_);
v___y_2542_ = v___x_2552_;
goto v___jp_2541_;
}
}
else
{
lean_dec_ref(v_env_2536_);
lean_dec_ref(v_filterExport_2535_);
return v_b_2540_;
}
v___jp_2541_:
{
size_t v___x_2543_; size_t v___x_2544_; 
v___x_2543_ = ((size_t)1ULL);
v___x_2544_ = lean_usize_add(v_i_2538_, v___x_2543_);
v_i_2538_ = v___x_2544_;
v_b_2540_ = v___y_2542_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object* v_filterExport_2553_, lean_object* v_env_2554_, lean_object* v_as_2555_, lean_object* v_i_2556_, lean_object* v_stop_2557_, lean_object* v_b_2558_){
_start:
{
size_t v_i_boxed_2559_; size_t v_stop_boxed_2560_; lean_object* v_res_2561_; 
v_i_boxed_2559_ = lean_unbox_usize(v_i_2556_);
lean_dec(v_i_2556_);
v_stop_boxed_2560_ = lean_unbox_usize(v_stop_2557_);
lean_dec(v_stop_2557_);
v_res_2561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2553_, v_env_2554_, v_as_2555_, v_i_boxed_2559_, v_stop_boxed_2560_, v_b_2558_);
lean_dec_ref(v_as_2555_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object* v_filterExport_2562_, uint8_t v_preserveOrder_2563_, lean_object* v_env_2564_, lean_object* v_x_2565_){
_start:
{
lean_object* v___y_2567_; 
if (v_preserveOrder_2563_ == 0)
{
lean_object* v_snd_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v_r_2580_; lean_object* v___x_2581_; lean_object* v___y_2583_; lean_object* v___y_2584_; uint8_t v___x_2586_; 
v_snd_2577_ = lean_ctor_get(v_x_2565_, 1);
lean_inc(v_snd_2577_);
lean_dec_ref(v_x_2565_);
v___x_2578_ = lean_unsigned_to_nat(0u);
v___x_2579_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v_r_2580_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_2579_, v_snd_2577_);
lean_dec(v_snd_2577_);
v___x_2581_ = lean_array_get_size(v_r_2580_);
v___x_2586_ = lean_nat_dec_eq(v___x_2581_, v___x_2578_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___y_2590_; uint8_t v___x_2592_; 
v___x_2587_ = lean_unsigned_to_nat(1u);
v___x_2588_ = lean_nat_sub(v___x_2581_, v___x_2587_);
v___x_2592_ = lean_nat_dec_le(v___x_2578_, v___x_2588_);
if (v___x_2592_ == 0)
{
lean_inc(v___x_2588_);
v___y_2590_ = v___x_2588_;
goto v___jp_2589_;
}
else
{
v___y_2590_ = v___x_2578_;
goto v___jp_2589_;
}
v___jp_2589_:
{
uint8_t v___x_2591_; 
v___x_2591_ = lean_nat_dec_le(v___y_2590_, v___x_2588_);
if (v___x_2591_ == 0)
{
lean_dec(v___x_2588_);
lean_inc(v___y_2590_);
v___y_2583_ = v___y_2590_;
v___y_2584_ = v___y_2590_;
goto v___jp_2582_;
}
else
{
v___y_2583_ = v___y_2590_;
v___y_2584_ = v___x_2588_;
goto v___jp_2582_;
}
}
}
else
{
v___y_2567_ = v_r_2580_;
goto v___jp_2566_;
}
v___jp_2582_:
{
lean_object* v___x_2585_; 
v___x_2585_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_2581_, v_r_2580_, v___y_2583_, v___y_2584_);
lean_dec(v___y_2584_);
v___y_2567_ = v___x_2585_;
goto v___jp_2566_;
}
}
else
{
lean_object* v_fst_2593_; lean_object* v_snd_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v_fst_2593_ = lean_ctor_get(v_x_2565_, 0);
lean_inc(v_fst_2593_);
v_snd_2594_ = lean_ctor_get(v_x_2565_, 1);
lean_inc(v_snd_2594_);
lean_dec_ref(v_x_2565_);
v___x_2595_ = lean_array_mk(v_fst_2593_);
v___x_2596_ = l_Array_reverse___redArg(v___x_2595_);
v___x_2597_ = lean_unsigned_to_nat(0u);
v___x_2598_ = lean_array_get_size(v___x_2596_);
v___x_2599_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2594_, v___x_2596_, v___x_2597_, v___x_2598_);
lean_dec_ref(v___x_2596_);
lean_dec(v_snd_2594_);
v___y_2567_ = v___x_2599_;
goto v___jp_2566_;
}
v___jp_2566_:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v___x_2568_ = lean_unsigned_to_nat(0u);
v___x_2569_ = lean_array_get_size(v___y_2567_);
v___x_2570_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2571_ = lean_nat_dec_lt(v___x_2568_, v___x_2569_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; 
lean_dec_ref(v_env_2564_);
lean_dec_ref(v_filterExport_2562_);
v___x_2572_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2570_);
lean_ctor_set(v___x_2572_, 1, v___x_2570_);
lean_ctor_set(v___x_2572_, 2, v___y_2567_);
return v___x_2572_;
}
else
{
size_t v___x_2573_; size_t v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2573_ = ((size_t)0ULL);
v___x_2574_ = lean_usize_of_nat(v___x_2569_);
v___x_2575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2562_, v_env_2564_, v___y_2567_, v___x_2573_, v___x_2574_, v___x_2570_);
lean_inc_ref(v___x_2575_);
v___x_2576_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
lean_ctor_set(v___x_2576_, 2, v___y_2567_);
return v___x_2576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object* v_filterExport_2600_, lean_object* v_preserveOrder_2601_, lean_object* v_env_2602_, lean_object* v_x_2603_){
_start:
{
uint8_t v_preserveOrder_boxed_2604_; lean_object* v_res_2605_; 
v_preserveOrder_boxed_2604_ = lean_unbox(v_preserveOrder_2601_);
v_res_2605_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2600_, v_preserveOrder_boxed_2604_, v_env_2602_, v_x_2603_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object* v_x_2615_){
_start:
{
lean_object* v_snd_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2630_; 
v_snd_2616_ = lean_ctor_get(v_x_2615_, 1);
v_isSharedCheck_2630_ = !lean_is_exclusive(v_x_2615_);
if (v_isSharedCheck_2630_ == 0)
{
lean_object* v_unused_2631_; 
v_unused_2631_ = lean_ctor_get(v_x_2615_, 0);
lean_dec(v_unused_2631_);
v___x_2618_ = v_x_2615_;
v_isShared_2619_ = v_isSharedCheck_2630_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_snd_2616_);
lean_dec(v_x_2615_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2630_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2620_; lean_object* v___y_2622_; 
v___x_2620_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2616_) == 0)
{
lean_object* v_size_2628_; 
v_size_2628_ = lean_ctor_get(v_snd_2616_, 0);
lean_inc(v_size_2628_);
lean_dec_ref_known(v_snd_2616_, 5);
v___y_2622_ = v_size_2628_;
goto v___jp_2621_;
}
else
{
lean_object* v___x_2629_; 
v___x_2629_ = lean_unsigned_to_nat(0u);
v___y_2622_ = v___x_2629_;
goto v___jp_2621_;
}
v___jp_2621_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2623_ = l_Nat_reprFast(v___y_2622_);
v___x_2624_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
if (v_isShared_2619_ == 0)
{
lean_ctor_set_tag(v___x_2618_, 5);
lean_ctor_set(v___x_2618_, 1, v___x_2624_);
lean_ctor_set(v___x_2618_, 0, v___x_2620_);
v___x_2626_ = v___x_2618_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object* v_x_2632_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object* v_x_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Lean_registerParametricAttributeExt___redArg___lam__3(v_x_2634_);
lean_dec_ref(v_x_2634_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object* v___x_2636_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2636_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object* v___x_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2639_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object* v___x_2642_, lean_object* v_x_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2642_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object* v___x_2647_, lean_object* v_x_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2647_, v_x_2648_, v___y_2649_);
lean_dec_ref(v___y_2649_);
lean_dec_ref(v_x_2648_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object* v_ref_2662_, uint8_t v_preserveOrder_2663_, lean_object* v_filterExport_2664_, uint8_t v_logWrites_2665_){
_start:
{
lean_object* v___f_2667_; lean_object* v___x_2668_; lean_object* v___f_2669_; lean_object* v___f_2670_; lean_object* v___f_2671_; lean_object* v___f_2672_; lean_object* v___f_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___f_2667_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__0));
v___x_2668_ = lean_box(v_preserveOrder_2663_);
v___f_2669_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2669_, 0, v_filterExport_2664_);
lean_closure_set(v___f_2669_, 1, v___x_2668_);
v___f_2670_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__1));
v___f_2671_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__2));
v___f_2672_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__4));
v___f_2673_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__5));
v___x_2674_ = lean_box(2);
v___x_2675_ = lean_box(0);
v___x_2676_ = 0;
v___x_2677_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2677_, 0, v_ref_2662_);
lean_ctor_set(v___x_2677_, 1, v___f_2672_);
lean_ctor_set(v___x_2677_, 2, v___f_2673_);
lean_ctor_set(v___x_2677_, 3, v___f_2667_);
lean_ctor_set(v___x_2677_, 4, v___f_2669_);
lean_ctor_set(v___x_2677_, 5, v___f_2670_);
lean_ctor_set(v___x_2677_, 6, v___x_2674_);
lean_ctor_set(v___x_2677_, 7, v___x_2675_);
lean_ctor_set_uint8(v___x_2677_, sizeof(void*)*8, v___x_2676_);
lean_ctor_set_uint8(v___x_2677_, sizeof(void*)*8 + 1, v_logWrites_2665_);
v___x_2678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
lean_ctor_set(v___x_2678_, 1, v___f_2671_);
v___x_2679_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2678_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object* v_ref_2680_, lean_object* v_preserveOrder_2681_, lean_object* v_filterExport_2682_, lean_object* v_logWrites_2683_, lean_object* v_a_2684_){
_start:
{
uint8_t v_preserveOrder_boxed_2685_; uint8_t v_logWrites_boxed_2686_; lean_object* v_res_2687_; 
v_preserveOrder_boxed_2685_ = lean_unbox(v_preserveOrder_2681_);
v_logWrites_boxed_2686_ = lean_unbox(v_logWrites_2683_);
v_res_2687_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2680_, v_preserveOrder_boxed_2685_, v_filterExport_2682_, v_logWrites_boxed_2686_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object* v_00_u03b1_2688_, lean_object* v_ref_2689_, uint8_t v_preserveOrder_2690_, lean_object* v_filterExport_2691_, uint8_t v_logWrites_2692_){
_start:
{
lean_object* v___x_2694_; 
v___x_2694_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2689_, v_preserveOrder_2690_, v_filterExport_2691_, v_logWrites_2692_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object* v_00_u03b1_2695_, lean_object* v_ref_2696_, lean_object* v_preserveOrder_2697_, lean_object* v_filterExport_2698_, lean_object* v_logWrites_2699_, lean_object* v_a_2700_){
_start:
{
uint8_t v_preserveOrder_boxed_2701_; uint8_t v_logWrites_boxed_2702_; lean_object* v_res_2703_; 
v_preserveOrder_boxed_2701_ = lean_unbox(v_preserveOrder_2697_);
v_logWrites_boxed_2702_ = lean_unbox(v_logWrites_2699_);
v_res_2703_ = l_Lean_registerParametricAttributeExt(v_00_u03b1_2695_, v_ref_2696_, v_preserveOrder_boxed_2701_, v_filterExport_2698_, v_logWrites_boxed_2702_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object* v_00_u03b1_2704_, lean_object* v_filterExport_2705_, lean_object* v_env_2706_, lean_object* v_as_2707_, size_t v_i_2708_, size_t v_stop_2709_, lean_object* v_b_2710_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2705_, v_env_2706_, v_as_2707_, v_i_2708_, v_stop_2709_, v_b_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object* v_00_u03b1_2712_, lean_object* v_filterExport_2713_, lean_object* v_env_2714_, lean_object* v_as_2715_, lean_object* v_i_2716_, lean_object* v_stop_2717_, lean_object* v_b_2718_){
_start:
{
size_t v_i_boxed_2719_; size_t v_stop_boxed_2720_; lean_object* v_res_2721_; 
v_i_boxed_2719_ = lean_unbox_usize(v_i_2716_);
lean_dec(v_i_2716_);
v_stop_boxed_2720_ = lean_unbox_usize(v_stop_2717_);
lean_dec(v_stop_2717_);
v_res_2721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(v_00_u03b1_2712_, v_filterExport_2713_, v_env_2714_, v_as_2715_, v_i_boxed_2719_, v_stop_boxed_2720_, v_b_2718_);
lean_dec_ref(v_as_2715_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object* v_init_2722_, lean_object* v_t_2723_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2722_, v_t_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object* v_init_2725_, lean_object* v_t_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(v_init_2725_, v_t_2726_);
lean_dec(v_t_2726_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object* v_00_u03b1_2728_, lean_object* v_init_2729_, lean_object* v_t_2730_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2729_, v_t_2730_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object* v_00_u03b1_2732_, lean_object* v_init_2733_, lean_object* v_t_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(v_00_u03b1_2732_, v_init_2733_, v_t_2734_);
lean_dec(v_t_2734_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object* v_00_u03b1_2736_, lean_object* v_n_2737_, lean_object* v_as_2738_, lean_object* v_lo_2739_, lean_object* v_hi_2740_, lean_object* v_w_2741_, lean_object* v_hlo_2742_, lean_object* v_hhi_2743_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2737_, v_as_2738_, v_lo_2739_, v_hi_2740_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object* v_00_u03b1_2745_, lean_object* v_n_2746_, lean_object* v_as_2747_, lean_object* v_lo_2748_, lean_object* v_hi_2749_, lean_object* v_w_2750_, lean_object* v_hlo_2751_, lean_object* v_hhi_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(v_00_u03b1_2745_, v_n_2746_, v_as_2747_, v_lo_2748_, v_hi_2749_, v_w_2750_, v_hlo_2751_, v_hhi_2752_);
lean_dec(v_hi_2749_);
lean_dec(v_n_2746_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object* v_00_u03b1_2754_, lean_object* v_snd_2755_, lean_object* v_as_2756_, lean_object* v_start_2757_, lean_object* v_stop_2758_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2755_, v_as_2756_, v_start_2757_, v_stop_2758_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object* v_00_u03b1_2760_, lean_object* v_snd_2761_, lean_object* v_as_2762_, lean_object* v_start_2763_, lean_object* v_stop_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(v_00_u03b1_2760_, v_snd_2761_, v_as_2762_, v_start_2763_, v_stop_2764_);
lean_dec(v_stop_2764_);
lean_dec(v_start_2763_);
lean_dec_ref(v_as_2762_);
lean_dec(v_snd_2761_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object* v_00_u03b1_2766_, lean_object* v_init_2767_, lean_object* v_x_2768_){
_start:
{
lean_object* v___x_2769_; 
v___x_2769_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2767_, v_x_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2770_, lean_object* v_init_2771_, lean_object* v_x_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(v_00_u03b1_2770_, v_init_2771_, v_x_2772_);
lean_dec(v_x_2772_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object* v_00_u03b1_2774_, lean_object* v_n_2775_, lean_object* v_lo_2776_, lean_object* v_hi_2777_, lean_object* v_hhi_2778_, lean_object* v_pivot_2779_, lean_object* v_as_2780_, lean_object* v_i_2781_, lean_object* v_k_2782_, lean_object* v_ilo_2783_, lean_object* v_ik_2784_, lean_object* v_w_2785_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2777_, v_pivot_2779_, v_as_2780_, v_i_2781_, v_k_2782_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2787_, lean_object* v_n_2788_, lean_object* v_lo_2789_, lean_object* v_hi_2790_, lean_object* v_hhi_2791_, lean_object* v_pivot_2792_, lean_object* v_as_2793_, lean_object* v_i_2794_, lean_object* v_k_2795_, lean_object* v_ilo_2796_, lean_object* v_ik_2797_, lean_object* v_w_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(v_00_u03b1_2787_, v_n_2788_, v_lo_2789_, v_hi_2790_, v_hhi_2791_, v_pivot_2792_, v_as_2793_, v_i_2794_, v_k_2795_, v_ilo_2796_, v_ik_2797_, v_w_2798_);
lean_dec_ref(v_pivot_2792_);
lean_dec(v_hi_2790_);
lean_dec(v_lo_2789_);
lean_dec(v_n_2788_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object* v_00_u03b1_2800_, lean_object* v_snd_2801_, lean_object* v_as_2802_, size_t v_i_2803_, size_t v_stop_2804_, lean_object* v_b_2805_){
_start:
{
lean_object* v___x_2806_; 
v___x_2806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2801_, v_as_2802_, v_i_2803_, v_stop_2804_, v_b_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2807_, lean_object* v_snd_2808_, lean_object* v_as_2809_, lean_object* v_i_2810_, lean_object* v_stop_2811_, lean_object* v_b_2812_){
_start:
{
size_t v_i_boxed_2813_; size_t v_stop_boxed_2814_; lean_object* v_res_2815_; 
v_i_boxed_2813_ = lean_unbox_usize(v_i_2810_);
lean_dec(v_i_2810_);
v_stop_boxed_2814_ = lean_unbox_usize(v_stop_2811_);
lean_dec(v_stop_2811_);
v_res_2815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(v_00_u03b1_2807_, v_snd_2808_, v_as_2809_, v_i_boxed_2813_, v_stop_boxed_2814_, v_b_2812_);
lean_dec_ref(v_as_2809_);
lean_dec(v_snd_2808_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object* v_env_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v___x_2819_; lean_object* v_nextMacroScope_2820_; lean_object* v_ngen_2821_; lean_object* v_auxDeclNGen_2822_; lean_object* v_traceState_2823_; lean_object* v_recordedDeps_2824_; lean_object* v_messages_2825_; lean_object* v_infoState_2826_; lean_object* v_snapshotTasks_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2838_; 
v___x_2819_ = lean_st_ref_take(v___y_2817_);
v_nextMacroScope_2820_ = lean_ctor_get(v___x_2819_, 1);
v_ngen_2821_ = lean_ctor_get(v___x_2819_, 2);
v_auxDeclNGen_2822_ = lean_ctor_get(v___x_2819_, 3);
v_traceState_2823_ = lean_ctor_get(v___x_2819_, 4);
v_recordedDeps_2824_ = lean_ctor_get(v___x_2819_, 6);
v_messages_2825_ = lean_ctor_get(v___x_2819_, 7);
v_infoState_2826_ = lean_ctor_get(v___x_2819_, 8);
v_snapshotTasks_2827_ = lean_ctor_get(v___x_2819_, 9);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2838_ == 0)
{
lean_object* v_unused_2839_; lean_object* v_unused_2840_; 
v_unused_2839_ = lean_ctor_get(v___x_2819_, 5);
lean_dec(v_unused_2839_);
v_unused_2840_ = lean_ctor_get(v___x_2819_, 0);
lean_dec(v_unused_2840_);
v___x_2829_ = v___x_2819_;
v_isShared_2830_ = v_isSharedCheck_2838_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_snapshotTasks_2827_);
lean_inc(v_infoState_2826_);
lean_inc(v_messages_2825_);
lean_inc(v_recordedDeps_2824_);
lean_inc(v_traceState_2823_);
lean_inc(v_auxDeclNGen_2822_);
lean_inc(v_ngen_2821_);
lean_inc(v_nextMacroScope_2820_);
lean_dec(v___x_2819_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2838_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2834_; 
v___x_2831_ = lean_box(0);
v___x_2832_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 5, v___x_2832_);
lean_ctor_set(v___x_2829_, 0, v_env_2816_);
v___x_2834_ = v___x_2829_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_env_2816_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_nextMacroScope_2820_);
lean_ctor_set(v_reuseFailAlloc_2837_, 2, v_ngen_2821_);
lean_ctor_set(v_reuseFailAlloc_2837_, 3, v_auxDeclNGen_2822_);
lean_ctor_set(v_reuseFailAlloc_2837_, 4, v_traceState_2823_);
lean_ctor_set(v_reuseFailAlloc_2837_, 5, v___x_2832_);
lean_ctor_set(v_reuseFailAlloc_2837_, 6, v_recordedDeps_2824_);
lean_ctor_set(v_reuseFailAlloc_2837_, 7, v_messages_2825_);
lean_ctor_set(v_reuseFailAlloc_2837_, 8, v_infoState_2826_);
lean_ctor_set(v_reuseFailAlloc_2837_, 9, v_snapshotTasks_2827_);
v___x_2834_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = lean_st_ref_put(v___y_2817_, v___x_2834_);
v___x_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2831_);
return v___x_2836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object* v_env_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2841_, v___y_2842_);
lean_dec(v___y_2842_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object* v_env_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2845_, v___y_2847_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object* v_env_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(v_env_2850_, v___y_2851_, v___y_2852_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object* v_addEntryFn_2855_, lean_object* v___x_2856_, lean_object* v_s_2857_){
_start:
{
lean_object* v_importedEntries_2858_; lean_object* v_state_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2867_; 
v_importedEntries_2858_ = lean_ctor_get(v_s_2857_, 0);
v_state_2859_ = lean_ctor_get(v_s_2857_, 1);
v_isSharedCheck_2867_ = !lean_is_exclusive(v_s_2857_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2861_ = v_s_2857_;
v_isShared_2862_ = v_isSharedCheck_2867_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_state_2859_);
lean_inc(v_importedEntries_2858_);
lean_dec(v_s_2857_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2867_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v_state_2863_; lean_object* v___x_2865_; 
v_state_2863_ = lean_apply_2(v_addEntryFn_2855_, v_state_2859_, v___x_2856_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 1, v_state_2863_);
v___x_2865_ = v___x_2861_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_importedEntries_2858_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v_state_2863_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object* v_afterSet_2868_, lean_object* v_getParam_2869_, lean_object* v_ext_2870_, lean_object* v_toAttributeImplCore_2871_, lean_object* v_decl_2872_, lean_object* v_stx_2873_, uint8_t v_kind_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_nextMacroScope_2879_; lean_object* v_ngen_2880_; lean_object* v_auxDeclNGen_2881_; lean_object* v_traceState_2882_; lean_object* v_recordedDeps_2883_; lean_object* v_messages_2884_; lean_object* v_infoState_2885_; lean_object* v_snapshotTasks_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; uint8_t v___x_2940_; uint8_t v___x_2941_; 
v___x_2940_ = 0;
v___x_2941_ = l_Lean_instBEqAttributeKind_beq(v_kind_2874_, v___x_2940_);
if (v___x_2941_ == 0)
{
lean_object* v_name_2942_; lean_object* v___x_2943_; 
lean_dec(v_stx_2873_);
lean_dec(v_decl_2872_);
lean_dec_ref(v_ext_2870_);
lean_dec_ref(v_getParam_2869_);
lean_dec_ref(v_afterSet_2868_);
v_name_2942_ = lean_ctor_get(v_toAttributeImplCore_2871_, 1);
lean_inc(v_name_2942_);
lean_dec_ref(v_toAttributeImplCore_2871_);
v___x_2943_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2942_, v_kind_2874_, v___y_2875_, v___y_2876_);
return v___x_2943_;
}
else
{
goto v___jp_2934_;
}
v___jp_2878_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2892_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_2893_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2893_, 0, v___y_2891_);
lean_ctor_set(v___x_2893_, 1, v_nextMacroScope_2879_);
lean_ctor_set(v___x_2893_, 2, v_ngen_2880_);
lean_ctor_set(v___x_2893_, 3, v_auxDeclNGen_2881_);
lean_ctor_set(v___x_2893_, 4, v_traceState_2882_);
lean_ctor_set(v___x_2893_, 5, v___x_2892_);
lean_ctor_set(v___x_2893_, 6, v_recordedDeps_2883_);
lean_ctor_set(v___x_2893_, 7, v_messages_2884_);
lean_ctor_set(v___x_2893_, 8, v_infoState_2885_);
lean_ctor_set(v___x_2893_, 9, v_snapshotTasks_2886_);
v___x_2894_ = lean_st_ref_put(v___y_2890_, v___x_2893_);
lean_inc(v___y_2890_);
lean_inc_ref(v___y_2888_);
v___x_2895_ = lean_apply_5(v_afterSet_2868_, v_decl_2872_, v___y_2889_, v___y_2888_, v___y_2890_, lean_box(0));
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_dec_ref(v___y_2887_);
return v___x_2895_;
}
else
{
lean_object* v_a_2896_; uint8_t v___x_2897_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_a_2896_);
v___x_2897_ = l_Lean_Exception_isInterrupt(v_a_2896_);
if (v___x_2897_ == 0)
{
uint8_t v___x_2898_; 
v___x_2898_ = l_Lean_Exception_isRuntime(v_a_2896_);
if (v___x_2898_ == 0)
{
lean_object* v___x_2899_; 
lean_dec_ref_known(v___x_2895_, 1);
v___x_2899_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v___y_2887_, v___y_2890_);
return v___x_2899_;
}
else
{
lean_dec_ref(v___y_2887_);
return v___x_2895_;
}
}
else
{
lean_dec(v_a_2896_);
lean_dec_ref(v___y_2887_);
return v___x_2895_;
}
}
}
v___jp_2900_:
{
lean_object* v___x_2904_; 
lean_inc(v___y_2903_);
lean_inc_ref(v___y_2902_);
lean_inc(v_decl_2872_);
v___x_2904_ = lean_apply_5(v_getParam_2869_, v_decl_2872_, v_stx_2873_, v___y_2902_, v___y_2903_, lean_box(0));
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v___x_2906_; lean_object* v_toEnvExtension_2907_; lean_object* v_env_2908_; lean_object* v_nextMacroScope_2909_; lean_object* v_ngen_2910_; lean_object* v_auxDeclNGen_2911_; lean_object* v_traceState_2912_; lean_object* v_recordedDeps_2913_; lean_object* v_messages_2914_; lean_object* v_infoState_2915_; lean_object* v_snapshotTasks_2916_; lean_object* v_addEntryFn_2917_; lean_object* v_asyncMode_2918_; uint8_t v_logWrites_2919_; lean_object* v___x_2920_; lean_object* v___f_2921_; uint8_t v___x_2922_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc_n(v_a_2905_, 2);
lean_dec_ref_known(v___x_2904_, 1);
v___x_2906_ = lean_st_ref_take(v___y_2903_);
v_toEnvExtension_2907_ = lean_ctor_get(v_ext_2870_, 0);
lean_inc_ref(v_toEnvExtension_2907_);
v_env_2908_ = lean_ctor_get(v___x_2906_, 0);
lean_inc_ref(v_env_2908_);
v_nextMacroScope_2909_ = lean_ctor_get(v___x_2906_, 1);
lean_inc(v_nextMacroScope_2909_);
v_ngen_2910_ = lean_ctor_get(v___x_2906_, 2);
lean_inc_ref(v_ngen_2910_);
v_auxDeclNGen_2911_ = lean_ctor_get(v___x_2906_, 3);
lean_inc_ref(v_auxDeclNGen_2911_);
v_traceState_2912_ = lean_ctor_get(v___x_2906_, 4);
lean_inc_ref(v_traceState_2912_);
v_recordedDeps_2913_ = lean_ctor_get(v___x_2906_, 6);
lean_inc_ref(v_recordedDeps_2913_);
v_messages_2914_ = lean_ctor_get(v___x_2906_, 7);
lean_inc_ref(v_messages_2914_);
v_infoState_2915_ = lean_ctor_get(v___x_2906_, 8);
lean_inc_ref(v_infoState_2915_);
v_snapshotTasks_2916_ = lean_ctor_get(v___x_2906_, 9);
lean_inc_ref(v_snapshotTasks_2916_);
lean_dec(v___x_2906_);
v_addEntryFn_2917_ = lean_ctor_get(v_ext_2870_, 3);
lean_inc(v_addEntryFn_2917_);
lean_dec_ref(v_ext_2870_);
v_asyncMode_2918_ = lean_ctor_get(v_toEnvExtension_2907_, 2);
lean_inc(v_asyncMode_2918_);
v_logWrites_2919_ = lean_ctor_get_uint8(v_toEnvExtension_2907_, sizeof(void*)*6);
lean_inc(v_decl_2872_);
v___x_2920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2920_, 0, v_decl_2872_);
lean_ctor_set(v___x_2920_, 1, v_a_2905_);
v___f_2921_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2921_, 0, v_addEntryFn_2917_);
lean_closure_set(v___f_2921_, 1, v___x_2920_);
v___x_2922_ = 1;
if (v_logWrites_2919_ == 0)
{
lean_object* v___x_2923_; 
lean_inc(v_decl_2872_);
v___x_2923_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2907_, v_env_2908_, v___f_2921_, v_asyncMode_2918_, v_decl_2872_, v___x_2922_);
lean_dec(v_asyncMode_2918_);
v_nextMacroScope_2879_ = v_nextMacroScope_2909_;
v_ngen_2880_ = v_ngen_2910_;
v_auxDeclNGen_2881_ = v_auxDeclNGen_2911_;
v_traceState_2882_ = v_traceState_2912_;
v_recordedDeps_2883_ = v_recordedDeps_2913_;
v_messages_2884_ = v_messages_2914_;
v_infoState_2885_ = v_infoState_2915_;
v_snapshotTasks_2886_ = v_snapshotTasks_2916_;
v___y_2887_ = v___y_2901_;
v___y_2888_ = v___y_2902_;
v___y_2889_ = v_a_2905_;
v___y_2890_ = v___y_2903_;
v___y_2891_ = v___x_2923_;
goto v___jp_2878_;
}
else
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
lean_inc_n(v_decl_2872_, 2);
v___x_2924_ = l_Lean_Environment_logDeclChange(v_env_2908_, v_decl_2872_);
v___x_2925_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2907_, v___x_2924_, v___f_2921_, v_asyncMode_2918_, v_decl_2872_, v___x_2922_);
lean_dec(v_asyncMode_2918_);
v_nextMacroScope_2879_ = v_nextMacroScope_2909_;
v_ngen_2880_ = v_ngen_2910_;
v_auxDeclNGen_2881_ = v_auxDeclNGen_2911_;
v_traceState_2882_ = v_traceState_2912_;
v_recordedDeps_2883_ = v_recordedDeps_2913_;
v_messages_2884_ = v_messages_2914_;
v_infoState_2885_ = v_infoState_2915_;
v_snapshotTasks_2886_ = v_snapshotTasks_2916_;
v___y_2887_ = v___y_2901_;
v___y_2888_ = v___y_2902_;
v___y_2889_ = v_a_2905_;
v___y_2890_ = v___y_2903_;
v___y_2891_ = v___x_2925_;
goto v___jp_2878_;
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec_ref(v___y_2901_);
lean_dec(v_decl_2872_);
lean_dec_ref(v_ext_2870_);
lean_dec_ref(v_afterSet_2868_);
v_a_2926_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2904_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2904_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
v___jp_2934_:
{
lean_object* v___x_2935_; lean_object* v_env_2936_; lean_object* v___x_2937_; 
v___x_2935_ = lean_st_ref_get(v___y_2876_);
v_env_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc_ref(v_env_2936_);
lean_dec(v___x_2935_);
v___x_2937_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2936_, v_decl_2872_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_dec_ref(v_toAttributeImplCore_2871_);
v___y_2901_ = v_env_2936_;
v___y_2902_ = v___y_2875_;
v___y_2903_ = v___y_2876_;
goto v___jp_2900_;
}
else
{
lean_object* v_name_2938_; lean_object* v___x_2939_; 
lean_dec_ref_known(v___x_2937_, 1);
lean_dec_ref(v_env_2936_);
lean_dec(v_stx_2873_);
lean_dec_ref(v_ext_2870_);
lean_dec_ref(v_getParam_2869_);
lean_dec_ref(v_afterSet_2868_);
v_name_2938_ = lean_ctor_get(v_toAttributeImplCore_2871_, 1);
lean_inc(v_name_2938_);
lean_dec_ref(v_toAttributeImplCore_2871_);
v___x_2939_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2938_, v_decl_2872_, v___y_2875_, v___y_2876_);
return v___x_2939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object* v_afterSet_2944_, lean_object* v_getParam_2945_, lean_object* v_ext_2946_, lean_object* v_toAttributeImplCore_2947_, lean_object* v_decl_2948_, lean_object* v_stx_2949_, lean_object* v_kind_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
uint8_t v_kind_boxed_2954_; lean_object* v_res_2955_; 
v_kind_boxed_2954_ = lean_unbox(v_kind_2950_);
v_res_2955_ = l_Lean_registerParametricAttributeForExt___redArg___lam__1(v_afterSet_2944_, v_getParam_2945_, v_ext_2946_, v_toAttributeImplCore_2947_, v_decl_2948_, v_stx_2949_, v_kind_boxed_2954_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__2(lean_object* v_toAttributeImplCore_2956_, lean_object* v_decl_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v_name_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v_name_2961_ = lean_ctor_get(v_toAttributeImplCore_2956_, 1);
lean_inc(v_name_2961_);
lean_dec_ref(v_toAttributeImplCore_2956_);
v___x_2962_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_2963_ = l_Lean_MessageData_ofName(v_name_2961_);
v___x_2964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2962_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
v___x_2965_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_2966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2964_);
lean_ctor_set(v___x_2966_, 1, v___x_2965_);
v___x_2967_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2966_, v___y_2958_, v___y_2959_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__2___boxed(lean_object* v_toAttributeImplCore_2968_, lean_object* v_decl_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_registerParametricAttributeForExt___redArg___lam__2(v_toAttributeImplCore_2968_, v_decl_2969_, v___y_2970_, v___y_2971_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v_decl_2969_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object* v_impl_2974_, lean_object* v_ext_2975_){
_start:
{
lean_object* v_toAttributeImplCore_2977_; lean_object* v_getParam_2978_; lean_object* v_afterSet_2979_; uint8_t v_preserveOrder_2980_; lean_object* v___f_2981_; lean_object* v___f_2982_; lean_object* v_attrImpl_2983_; lean_object* v___x_2984_; 
v_toAttributeImplCore_2977_ = lean_ctor_get(v_impl_2974_, 0);
lean_inc_ref_n(v_toAttributeImplCore_2977_, 3);
v_getParam_2978_ = lean_ctor_get(v_impl_2974_, 1);
lean_inc_ref(v_getParam_2978_);
v_afterSet_2979_ = lean_ctor_get(v_impl_2974_, 2);
lean_inc_ref(v_afterSet_2979_);
v_preserveOrder_2980_ = lean_ctor_get_uint8(v_impl_2974_, sizeof(void*)*4);
lean_dec_ref(v_impl_2974_);
lean_inc_ref(v_ext_2975_);
v___f_2981_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_2981_, 0, v_afterSet_2979_);
lean_closure_set(v___f_2981_, 1, v_getParam_2978_);
lean_closure_set(v___f_2981_, 2, v_ext_2975_);
lean_closure_set(v___f_2981_, 3, v_toAttributeImplCore_2977_);
v___f_2982_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__2___boxed), 5, 1);
lean_closure_set(v___f_2982_, 0, v_toAttributeImplCore_2977_);
v_attrImpl_2983_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_attrImpl_2983_, 0, v_toAttributeImplCore_2977_);
lean_ctor_set(v_attrImpl_2983_, 1, v___f_2981_);
lean_ctor_set(v_attrImpl_2983_, 2, v___f_2982_);
lean_inc_ref(v_attrImpl_2983_);
v___x_2984_ = l_Lean_registerBuiltinAttribute(v_attrImpl_2983_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2992_; 
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_2992_ == 0)
{
lean_object* v_unused_2993_; 
v_unused_2993_ = lean_ctor_get(v___x_2984_, 0);
lean_dec(v_unused_2993_);
v___x_2986_ = v___x_2984_;
v_isShared_2987_ = v_isSharedCheck_2992_;
goto v_resetjp_2985_;
}
else
{
lean_dec(v___x_2984_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2992_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2988_; lean_object* v___x_2990_; 
v___x_2988_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2988_, 0, v_attrImpl_2983_);
lean_ctor_set(v___x_2988_, 1, v_ext_2975_);
lean_ctor_set_uint8(v___x_2988_, sizeof(void*)*2, v_preserveOrder_2980_);
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 0, v___x_2988_);
v___x_2990_ = v___x_2986_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2988_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
lean_dec_ref_known(v_attrImpl_2983_, 3);
lean_dec_ref(v_ext_2975_);
v_a_2994_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2984_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2984_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object* v_impl_3002_, lean_object* v_ext_3003_, lean_object* v_a_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3002_, v_ext_3003_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object* v_00_u03b1_3006_, lean_object* v_impl_3007_, lean_object* v_ext_3008_){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3007_, v_ext_3008_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object* v_00_u03b1_3011_, lean_object* v_impl_3012_, lean_object* v_ext_3013_, lean_object* v_a_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l_Lean_registerParametricAttributeForExt(v_00_u03b1_3011_, v_impl_3012_, v_ext_3013_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_3016_){
_start:
{
lean_object* v_toAttributeImplCore_3018_; uint8_t v_preserveOrder_3019_; lean_object* v_filterExport_3020_; lean_object* v_ref_3021_; uint8_t v___x_3022_; lean_object* v___x_3023_; 
v_toAttributeImplCore_3018_ = lean_ctor_get(v_impl_3016_, 0);
v_preserveOrder_3019_ = lean_ctor_get_uint8(v_impl_3016_, sizeof(void*)*4);
v_filterExport_3020_ = lean_ctor_get(v_impl_3016_, 3);
v_ref_3021_ = lean_ctor_get(v_toAttributeImplCore_3018_, 0);
v___x_3022_ = 0;
lean_inc_ref(v_filterExport_3020_);
lean_inc(v_ref_3021_);
v___x_3023_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_3021_, v_preserveOrder_3019_, v_filterExport_3020_, v___x_3022_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3025_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_a_3024_);
lean_dec_ref_known(v___x_3023_, 1);
v___x_3025_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3016_, v_a_3024_);
return v___x_3025_;
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec_ref(v_impl_3016_);
v_a_3026_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3023_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3023_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_Lean_registerParametricAttribute___redArg(v_impl_3034_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_3037_, lean_object* v_impl_3038_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_Lean_registerParametricAttribute___redArg(v_impl_3038_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_3041_, lean_object* v_impl_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_registerParametricAttribute(v_00_u03b1_3041_, v_impl_3042_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object* v_inst_3050_, lean_object* v_ext_3051_, uint8_t v_preserveOrder_3052_, lean_object* v_env_3053_, lean_object* v_decl_3054_){
_start:
{
lean_object* v___y_3056_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3068_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3053_, v_decl_3054_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_toEnvExtension_3069_; lean_object* v_asyncMode_3070_; lean_object* v___x_3071_; uint8_t v___x_3072_; lean_object* v___x_3073_; lean_object* v_snd_3074_; lean_object* v___x_3075_; 
lean_dec(v_inst_3050_);
v_toEnvExtension_3069_ = lean_ctor_get(v_ext_3051_, 0);
v_asyncMode_3070_ = lean_ctor_get(v_toEnvExtension_3069_, 2);
v___x_3071_ = lean_box(0);
v___x_3072_ = 0;
v___x_3073_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3067_, v_ext_3051_, v_env_3053_, v_asyncMode_3070_, v___x_3071_, v___x_3072_);
v_snd_3074_ = lean_ctor_get(v___x_3073_, 1);
lean_inc(v_snd_3074_);
lean_dec(v___x_3073_);
v___x_3075_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3074_, v_decl_3054_);
lean_dec(v_decl_3054_);
lean_dec(v_snd_3074_);
return v___x_3075_;
}
else
{
if (v_preserveOrder_3052_ == 0)
{
lean_object* v_val_3076_; uint8_t v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; 
v_val_3076_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_val_3076_);
lean_dec_ref_known(v___x_3068_, 1);
v___x_3077_ = 0;
v___x_3078_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3067_, v_ext_3051_, v_env_3053_, v_val_3076_, v___x_3077_);
lean_dec(v_val_3076_);
lean_dec_ref(v_env_3053_);
v___x_3079_ = lean_unsigned_to_nat(0u);
v___x_3080_ = lean_array_get_size(v___x_3078_);
v___x_3081_ = lean_nat_dec_lt(v___x_3079_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; 
lean_dec_ref(v___x_3078_);
lean_dec(v_decl_3054_);
lean_dec(v_inst_3050_);
v___x_3082_ = lean_box(0);
return v___x_3082_;
}
else
{
lean_object* v___x_3083_; lean_object* v___x_3084_; uint8_t v___x_3085_; 
v___x_3083_ = lean_unsigned_to_nat(1u);
v___x_3084_ = lean_nat_sub(v___x_3080_, v___x_3083_);
v___x_3085_ = lean_nat_dec_le(v___x_3079_, v___x_3084_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; 
lean_dec(v___x_3084_);
lean_dec_ref(v___x_3078_);
lean_dec(v_decl_3054_);
lean_dec(v_inst_3050_);
v___x_3086_ = lean_box(0);
return v___x_3086_;
}
else
{
lean_object* v___f_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___f_3087_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
v___x_3088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3088_, 0, v_decl_3054_);
lean_ctor_set(v___x_3088_, 1, v_inst_3050_);
v___x_3089_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3090_ = l_Array_binSearchAux___redArg(v___f_3087_, v___x_3089_, v___x_3078_, v___x_3088_, v___x_3079_, v___x_3084_);
lean_dec_ref(v___x_3078_);
v___y_3056_ = v___x_3090_;
goto v___jp_3055_;
}
}
}
else
{
lean_object* v_val_3091_; uint8_t v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
lean_dec(v_inst_3050_);
v_val_3091_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_val_3091_);
lean_dec_ref_known(v___x_3068_, 1);
v___x_3092_ = 0;
v___x_3093_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3067_, v_ext_3051_, v_env_3053_, v_val_3091_, v___x_3092_);
lean_dec(v_val_3091_);
lean_dec_ref(v_env_3053_);
v___x_3094_ = l_Lean_findByName_x3f___redArg(v___x_3093_, v_decl_3054_);
lean_dec(v_decl_3054_);
lean_dec_ref(v___x_3093_);
v___y_3056_ = v___x_3094_;
goto v___jp_3055_;
}
}
v___jp_3055_:
{
if (lean_obj_tag(v___y_3056_) == 0)
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_box(0);
return v___x_3057_;
}
else
{
lean_object* v_val_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3066_; 
v_val_3058_ = lean_ctor_get(v___y_3056_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___y_3056_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3060_ = v___y_3056_;
v_isShared_3061_ = v_isSharedCheck_3066_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_val_3058_);
lean_dec(v___y_3056_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3066_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v_snd_3062_; lean_object* v___x_3064_; 
v_snd_3062_ = lean_ctor_get(v_val_3058_, 1);
lean_inc(v_snd_3062_);
lean_dec(v_val_3058_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v_snd_3062_);
v___x_3064_ = v___x_3060_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_snd_3062_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object* v_inst_3095_, lean_object* v_ext_3096_, lean_object* v_preserveOrder_3097_, lean_object* v_env_3098_, lean_object* v_decl_3099_){
_start:
{
uint8_t v_preserveOrder_boxed_3100_; lean_object* v_res_3101_; 
v_preserveOrder_boxed_3100_ = lean_unbox(v_preserveOrder_3097_);
v_res_3101_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3095_, v_ext_3096_, v_preserveOrder_boxed_3100_, v_env_3098_, v_decl_3099_);
lean_dec_ref(v_ext_3096_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object* v_00_u03b1_3102_, lean_object* v_inst_3103_, lean_object* v_ext_3104_, uint8_t v_preserveOrder_3105_, lean_object* v_env_3106_, lean_object* v_decl_3107_){
_start:
{
lean_object* v___x_3108_; 
v___x_3108_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3103_, v_ext_3104_, v_preserveOrder_3105_, v_env_3106_, v_decl_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object* v_00_u03b1_3109_, lean_object* v_inst_3110_, lean_object* v_ext_3111_, lean_object* v_preserveOrder_3112_, lean_object* v_env_3113_, lean_object* v_decl_3114_){
_start:
{
uint8_t v_preserveOrder_boxed_3115_; lean_object* v_res_3116_; 
v_preserveOrder_boxed_3115_ = lean_unbox(v_preserveOrder_3112_);
v_res_3116_ = l_Lean_ParametricAttribute_getParamFromExt_x3f(v_00_u03b1_3109_, v_inst_3110_, v_ext_3111_, v_preserveOrder_boxed_3115_, v_env_3113_, v_decl_3114_);
lean_dec_ref(v_ext_3111_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3117_, lean_object* v_attr_3118_, lean_object* v_env_3119_, lean_object* v_decl_3120_){
_start:
{
lean_object* v_ext_3121_; uint8_t v_preserveOrder_3122_; lean_object* v___x_3123_; 
v_ext_3121_ = lean_ctor_get(v_attr_3118_, 1);
v_preserveOrder_3122_ = lean_ctor_get_uint8(v_attr_3118_, sizeof(void*)*2);
v___x_3123_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3117_, v_ext_3121_, v_preserveOrder_3122_, v_env_3119_, v_decl_3120_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3124_, lean_object* v_attr_3125_, lean_object* v_env_3126_, lean_object* v_decl_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3124_, v_attr_3125_, v_env_3126_, v_decl_3127_);
lean_dec_ref(v_attr_3125_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3129_, lean_object* v_inst_3130_, lean_object* v_attr_3131_, lean_object* v_env_3132_, lean_object* v_decl_3133_){
_start:
{
lean_object* v___x_3134_; 
v___x_3134_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3130_, v_attr_3131_, v_env_3132_, v_decl_3133_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3135_, lean_object* v_inst_3136_, lean_object* v_attr_3137_, lean_object* v_env_3138_, lean_object* v_decl_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3135_, v_inst_3136_, v_attr_3137_, v_env_3138_, v_decl_3139_);
lean_dec_ref(v_attr_3137_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object* v_ext_3145_, lean_object* v_attr_3146_, lean_object* v_env_3147_, lean_object* v_decl_3148_, lean_object* v_param_3149_){
_start:
{
lean_object* v___x_3150_; 
v___x_3150_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3147_, v_decl_3148_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_toEnvExtension_3151_; lean_object* v_addEntryFn_3152_; lean_object* v_asyncMode_3153_; uint8_t v_logWrites_3154_; uint8_t v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v_snd_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3194_; 
v_toEnvExtension_3151_ = lean_ctor_get(v_ext_3145_, 0);
lean_inc_ref(v_toEnvExtension_3151_);
v_addEntryFn_3152_ = lean_ctor_get(v_ext_3145_, 3);
lean_inc(v_addEntryFn_3152_);
v_asyncMode_3153_ = lean_ctor_get(v_toEnvExtension_3151_, 2);
lean_inc(v_asyncMode_3153_);
v_logWrites_3154_ = lean_ctor_get_uint8(v_toEnvExtension_3151_, sizeof(void*)*6);
v___x_3155_ = 0;
v___x_3156_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3157_ = lean_box(0);
lean_inc_ref(v_env_3147_);
v___x_3158_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3156_, v_ext_3145_, v_env_3147_, v_asyncMode_3153_, v___x_3157_, v___x_3155_);
lean_dec_ref(v_ext_3145_);
v_snd_3159_ = lean_ctor_get(v___x_3158_, 1);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3194_ == 0)
{
lean_object* v_unused_3195_; 
v_unused_3195_ = lean_ctor_get(v___x_3158_, 0);
lean_dec(v_unused_3195_);
v___x_3161_ = v___x_3158_;
v_isShared_3162_ = v_isSharedCheck_3194_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_snd_3159_);
lean_dec(v___x_3158_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3194_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3163_; 
v___x_3163_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3159_, v_decl_3148_);
lean_dec(v_snd_3159_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v___x_3165_; 
lean_dec_ref(v_attr_3146_);
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 1, v_param_3149_);
lean_ctor_set(v___x_3161_, 0, v_decl_3148_);
v___x_3165_ = v___x_3161_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_decl_3148_);
lean_ctor_set(v_reuseFailAlloc_3173_, 1, v_param_3149_);
v___x_3165_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
lean_object* v___f_3166_; uint8_t v___x_3167_; 
v___f_3166_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3166_, 0, v_addEntryFn_3152_);
lean_closure_set(v___f_3166_, 1, v___x_3165_);
v___x_3167_ = 1;
if (v_logWrites_3154_ == 0)
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3168_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3151_, v_env_3147_, v___f_3166_, v_asyncMode_3153_, v___x_3157_, v___x_3167_);
lean_dec(v_asyncMode_3153_);
v___x_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3168_);
return v___x_3169_;
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
lean_inc_ref(v_toEnvExtension_3151_);
v___x_3170_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3151_, v_env_3147_);
lean_dec_ref(v_env_3147_);
v___x_3171_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3151_, v___x_3170_, v___f_3166_, v_asyncMode_3153_, v___x_3157_, v___x_3167_);
lean_dec(v_asyncMode_3153_);
v___x_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
return v___x_3172_;
}
}
}
else
{
lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3192_; 
lean_del_object(v___x_3161_);
lean_dec(v_asyncMode_3153_);
lean_dec(v_addEntryFn_3152_);
lean_dec_ref(v_toEnvExtension_3151_);
lean_dec(v_param_3149_);
lean_dec_ref(v_env_3147_);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3192_ == 0)
{
lean_object* v_unused_3193_; 
v_unused_3193_ = lean_ctor_get(v___x_3163_, 0);
lean_dec(v_unused_3193_);
v___x_3175_ = v___x_3163_;
v_isShared_3176_ = v_isSharedCheck_3192_;
goto v_resetjp_3174_;
}
else
{
lean_dec(v___x_3163_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3192_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v_toAttributeImplCore_3177_; lean_object* v_name_3178_; uint8_t v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3190_; 
v_toAttributeImplCore_3177_ = lean_ctor_get(v_attr_3146_, 0);
lean_inc_ref(v_toAttributeImplCore_3177_);
lean_dec_ref(v_attr_3146_);
v_name_3178_ = lean_ctor_get(v_toAttributeImplCore_3177_, 1);
lean_inc(v_name_3178_);
lean_dec_ref(v_toAttributeImplCore_3177_);
v___x_3179_ = 1;
v___x_3180_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3181_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3178_, v___x_3179_);
v___x_3182_ = lean_string_append(v___x_3180_, v___x_3181_);
lean_dec_ref(v___x_3181_);
v___x_3183_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3184_ = lean_string_append(v___x_3182_, v___x_3183_);
v___x_3185_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3148_, v___x_3179_);
v___x_3186_ = lean_string_append(v___x_3184_, v___x_3185_);
lean_dec_ref(v___x_3185_);
v___x_3187_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2));
v___x_3188_ = lean_string_append(v___x_3186_, v___x_3187_);
if (v_isShared_3176_ == 0)
{
lean_ctor_set_tag(v___x_3175_, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3188_);
v___x_3190_ = v___x_3175_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3188_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
}
else
{
lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3214_; 
lean_dec(v_param_3149_);
lean_dec_ref(v_env_3147_);
lean_dec_ref(v_ext_3145_);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3214_ == 0)
{
lean_object* v_unused_3215_; 
v_unused_3215_ = lean_ctor_get(v___x_3150_, 0);
lean_dec(v_unused_3215_);
v___x_3197_ = v___x_3150_;
v_isShared_3198_ = v_isSharedCheck_3214_;
goto v_resetjp_3196_;
}
else
{
lean_dec(v___x_3150_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3214_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v_toAttributeImplCore_3199_; lean_object* v_name_3200_; uint8_t v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3212_; 
v_toAttributeImplCore_3199_ = lean_ctor_get(v_attr_3146_, 0);
lean_inc_ref(v_toAttributeImplCore_3199_);
lean_dec_ref(v_attr_3146_);
v_name_3200_ = lean_ctor_get(v_toAttributeImplCore_3199_, 1);
lean_inc(v_name_3200_);
lean_dec_ref(v_toAttributeImplCore_3199_);
v___x_3201_ = 1;
v___x_3202_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3203_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3200_, v___x_3201_);
v___x_3204_ = lean_string_append(v___x_3202_, v___x_3203_);
lean_dec_ref(v___x_3203_);
v___x_3205_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3206_ = lean_string_append(v___x_3204_, v___x_3205_);
v___x_3207_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3148_, v___x_3201_);
v___x_3208_ = lean_string_append(v___x_3206_, v___x_3207_);
lean_dec_ref(v___x_3207_);
v___x_3209_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3));
v___x_3210_ = lean_string_append(v___x_3208_, v___x_3209_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set_tag(v___x_3197_, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3210_);
v___x_3212_ = v___x_3197_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3210_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object* v_00_u03b1_3216_, lean_object* v_ext_3217_, lean_object* v_attr_3218_, lean_object* v_env_3219_, lean_object* v_decl_3220_, lean_object* v_param_3221_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3217_, v_attr_3218_, v_env_3219_, v_decl_3220_, v_param_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3223_, lean_object* v_env_3224_, lean_object* v_decl_3225_, lean_object* v_param_3226_){
_start:
{
lean_object* v_attr_3227_; lean_object* v_ext_3228_; lean_object* v___x_3229_; 
v_attr_3227_ = lean_ctor_get(v_attr_3223_, 0);
lean_inc_ref(v_attr_3227_);
v_ext_3228_ = lean_ctor_get(v_attr_3223_, 1);
lean_inc_ref(v_ext_3228_);
lean_dec_ref(v_attr_3223_);
v___x_3229_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3228_, v_attr_3227_, v_env_3224_, v_decl_3225_, v_param_3226_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3230_, lean_object* v_attr_3231_, lean_object* v_env_3232_, lean_object* v_decl_3233_, lean_object* v_param_3234_){
_start:
{
lean_object* v___x_3235_; 
v___x_3235_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3231_, v_env_3232_, v_decl_3233_, v_param_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(lean_object* v_x_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3239_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0___boxed(lean_object* v_x_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(v_x_3241_, v___y_3242_);
lean_dec_ref(v___y_3242_);
lean_dec_ref(v_x_3241_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(lean_object* v_s_3245_, lean_object* v_x_3246_){
_start:
{
lean_inc(v_s_3245_);
return v_s_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1___boxed(lean_object* v_s_3247_, lean_object* v_x_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(v_s_3247_, v_x_3248_);
lean_dec_ref(v_x_3248_);
lean_dec(v_s_3247_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(lean_object* v_x_3250_, lean_object* v_x_3251_){
_start:
{
lean_object* v___x_3252_; 
v___x_3252_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2___boxed(lean_object* v_x_3253_, lean_object* v_x_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(v_x_3253_, v_x_3254_);
lean_dec(v_x_3254_);
lean_dec_ref(v_x_3253_);
return v_res_3255_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3(void){
_start:
{
lean_object* v___f_3259_; lean_object* v___f_3260_; lean_object* v___f_3261_; lean_object* v___f_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___f_3259_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3260_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2));
v___f_3261_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1));
v___f_3262_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0));
v___x_3263_ = lean_box(0);
v___x_3264_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_3265_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
lean_ctor_set(v___x_3265_, 1, v___x_3263_);
lean_ctor_set(v___x_3265_, 2, v___f_3262_);
lean_ctor_set(v___x_3265_, 3, v___f_3261_);
lean_ctor_set(v___x_3265_, 4, v___f_3260_);
lean_ctor_set(v___x_3265_, 5, v___f_3259_);
return v___x_3265_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3266_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3);
v___x_3267_ = lean_box(0);
v___x_3268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3267_);
lean_ctor_set(v___x_3268_, 1, v___x_3266_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg(){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___boxed(lean_object* v___dummy_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v_res_3272_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__0(void){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3274_){
_start:
{
lean_object* v___x_3275_; 
v___x_3275_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg(){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg___boxed(lean_object* v___dummy_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l_Lean_instInhabitedEnumAttributes___redArg();
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3280_){
_start:
{
lean_object* v___x_3281_; 
v___x_3281_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3281_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3282_; 
v___x_3282_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3283_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3285_);
lean_dec(v_x_3285_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3287_, lean_object* v_x_3288_, lean_object* v_x_3289_){
_start:
{
if (lean_obj_tag(v_x_3289_) == 0)
{
return v_x_3288_;
}
else
{
lean_object* v_head_3290_; lean_object* v_tail_3291_; lean_object* v___x_3292_; 
v_head_3290_ = lean_ctor_get(v_x_3289_, 0);
lean_inc(v_head_3290_);
v_tail_3291_ = lean_ctor_get(v_x_3289_, 1);
lean_inc(v_tail_3291_);
lean_dec_ref_known(v_x_3289_, 2);
v___x_3292_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3287_, v_head_3290_);
if (lean_obj_tag(v___x_3292_) == 1)
{
lean_object* v_val_3293_; lean_object* v___x_3294_; 
v_val_3293_ = lean_ctor_get(v___x_3292_, 0);
lean_inc(v_val_3293_);
lean_dec_ref_known(v___x_3292_, 1);
v___x_3294_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3290_, v_val_3293_, v_x_3288_);
v_x_3288_ = v___x_3294_;
v_x_3289_ = v_tail_3291_;
goto _start;
}
else
{
lean_dec(v___x_3292_);
lean_dec(v_head_3290_);
v_x_3289_ = v_tail_3291_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3297_, lean_object* v_x_3298_, lean_object* v_x_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3297_, v_x_3298_, v_x_3299_);
lean_dec(v_newState_3297_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3301_, lean_object* v_newState_3302_, lean_object* v_consts_3303_, lean_object* v_st_3304_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3302_, v_st_3304_, v_consts_3303_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3306_, lean_object* v_newState_3307_, lean_object* v_consts_3308_, lean_object* v_st_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3306_, v_newState_3307_, v_consts_3308_, v_st_3309_);
lean_dec(v_newState_3307_);
lean_dec(v_x_3306_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3320_){
_start:
{
lean_object* v___x_3321_; lean_object* v___y_3323_; 
v___x_3321_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3320_) == 0)
{
lean_object* v_size_3327_; 
v_size_3327_ = lean_ctor_get(v_s_3320_, 0);
lean_inc(v_size_3327_);
lean_dec_ref_known(v_s_3320_, 5);
v___y_3323_ = v_size_3327_;
goto v___jp_3322_;
}
else
{
lean_object* v___x_3328_; 
v___x_3328_ = lean_unsigned_to_nat(0u);
v___y_3323_ = v___x_3328_;
goto v___jp_3322_;
}
v___jp_3322_:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3324_ = l_Nat_reprFast(v___y_3323_);
v___x_3325_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
v___x_3326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3321_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
return v___x_3326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3329_, lean_object* v_as_3330_, size_t v_i_3331_, size_t v_stop_3332_, lean_object* v_b_3333_){
_start:
{
lean_object* v___y_3335_; uint8_t v___x_3339_; 
v___x_3339_ = lean_usize_dec_eq(v_i_3331_, v_stop_3332_);
if (v___x_3339_ == 0)
{
lean_object* v___x_3340_; lean_object* v_fst_3341_; uint8_t v___x_3342_; lean_object* v___x_3343_; uint8_t v___x_3344_; 
v___x_3340_ = lean_array_uget_borrowed(v_as_3330_, v_i_3331_);
v_fst_3341_ = lean_ctor_get(v___x_3340_, 0);
v___x_3342_ = 1;
lean_inc_ref(v_env_3329_);
v___x_3343_ = l_Lean_Environment_setExporting(v_env_3329_, v___x_3342_);
lean_inc(v_fst_3341_);
v___x_3344_ = l_Lean_Environment_contains(v___x_3343_, v_fst_3341_, v___x_3339_);
if (v___x_3344_ == 0)
{
v___y_3335_ = v_b_3333_;
goto v___jp_3334_;
}
else
{
lean_object* v___x_3345_; 
lean_inc(v___x_3340_);
v___x_3345_ = lean_array_push(v_b_3333_, v___x_3340_);
v___y_3335_ = v___x_3345_;
goto v___jp_3334_;
}
}
else
{
lean_dec_ref(v_env_3329_);
return v_b_3333_;
}
v___jp_3334_:
{
size_t v___x_3336_; size_t v___x_3337_; 
v___x_3336_ = ((size_t)1ULL);
v___x_3337_ = lean_usize_add(v_i_3331_, v___x_3336_);
v_i_3331_ = v___x_3337_;
v_b_3333_ = v___y_3335_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3346_, lean_object* v_as_3347_, lean_object* v_i_3348_, lean_object* v_stop_3349_, lean_object* v_b_3350_){
_start:
{
size_t v_i_boxed_3351_; size_t v_stop_boxed_3352_; lean_object* v_res_3353_; 
v_i_boxed_3351_ = lean_unbox_usize(v_i_3348_);
lean_dec(v_i_3348_);
v_stop_boxed_3352_ = lean_unbox_usize(v_stop_3349_);
lean_dec(v_stop_3349_);
v_res_3353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3346_, v_as_3347_, v_i_boxed_3351_, v_stop_boxed_3352_, v_b_3350_);
lean_dec_ref(v_as_3347_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3354_, lean_object* v_m_3355_){
_start:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___y_3359_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___y_3370_; lean_object* v___y_3371_; uint8_t v___x_3373_; 
v___x_3356_ = lean_unsigned_to_nat(0u);
v___x_3357_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_3367_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_3357_, v_m_3355_);
v___x_3368_ = lean_array_get_size(v___x_3367_);
v___x_3373_ = lean_nat_dec_eq(v___x_3368_, v___x_3356_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___y_3377_; uint8_t v___x_3379_; 
v___x_3374_ = lean_unsigned_to_nat(1u);
v___x_3375_ = lean_nat_sub(v___x_3368_, v___x_3374_);
v___x_3379_ = lean_nat_dec_le(v___x_3356_, v___x_3375_);
if (v___x_3379_ == 0)
{
lean_inc(v___x_3375_);
v___y_3377_ = v___x_3375_;
goto v___jp_3376_;
}
else
{
v___y_3377_ = v___x_3356_;
goto v___jp_3376_;
}
v___jp_3376_:
{
uint8_t v___x_3378_; 
v___x_3378_ = lean_nat_dec_le(v___y_3377_, v___x_3375_);
if (v___x_3378_ == 0)
{
lean_dec(v___x_3375_);
lean_inc(v___y_3377_);
v___y_3370_ = v___y_3377_;
v___y_3371_ = v___y_3377_;
goto v___jp_3369_;
}
else
{
v___y_3370_ = v___y_3377_;
v___y_3371_ = v___x_3375_;
goto v___jp_3369_;
}
}
}
else
{
v___y_3359_ = v___x_3367_;
goto v___jp_3358_;
}
v___jp_3358_:
{
lean_object* v___x_3360_; uint8_t v___x_3361_; 
v___x_3360_ = lean_array_get_size(v___y_3359_);
v___x_3361_ = lean_nat_dec_lt(v___x_3356_, v___x_3360_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3362_; 
lean_dec_ref(v_env_3354_);
v___x_3362_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3357_);
lean_ctor_set(v___x_3362_, 1, v___x_3357_);
lean_ctor_set(v___x_3362_, 2, v___y_3359_);
return v___x_3362_;
}
else
{
size_t v___x_3363_; size_t v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3363_ = ((size_t)0ULL);
v___x_3364_ = lean_usize_of_nat(v___x_3360_);
v___x_3365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3354_, v___y_3359_, v___x_3363_, v___x_3364_, v___x_3357_);
lean_inc_ref(v___x_3365_);
v___x_3366_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
lean_ctor_set(v___x_3366_, 2, v___y_3359_);
return v___x_3366_;
}
}
v___jp_3369_:
{
lean_object* v___x_3372_; 
v___x_3372_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_3368_, v___x_3367_, v___y_3370_, v___y_3371_);
lean_dec(v___y_3371_);
v___y_3359_ = v___x_3372_;
goto v___jp_3358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3380_, lean_object* v_m_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3380_, v_m_3381_);
lean_dec(v_m_3381_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3383_, lean_object* v_p_3384_){
_start:
{
lean_object* v_fst_3385_; lean_object* v_snd_3386_; lean_object* v___x_3387_; 
v_fst_3385_ = lean_ctor_get(v_p_3384_, 0);
lean_inc(v_fst_3385_);
v_snd_3386_ = lean_ctor_get(v_p_3384_, 1);
lean_inc(v_snd_3386_);
lean_dec_ref(v_p_3384_);
v___x_3387_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3385_, v_snd_3386_, v_s_3383_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3388_, lean_object* v_x_3389_, lean_object* v_x_3390_){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3388_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3393_, lean_object* v_x_3394_, lean_object* v_x_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3393_, v_x_3394_, v_x_3395_);
lean_dec_ref(v_x_3395_);
lean_dec_ref(v_x_3394_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3398_){
_start:
{
if (lean_obj_tag(v_as_3398_) == 0)
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = lean_box(0);
v___x_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
return v___x_3401_;
}
else
{
lean_object* v_head_3402_; lean_object* v_tail_3403_; lean_object* v___x_3404_; 
v_head_3402_ = lean_ctor_get(v_as_3398_, 0);
lean_inc(v_head_3402_);
v_tail_3403_ = lean_ctor_get(v_as_3398_, 1);
lean_inc(v_tail_3403_);
lean_dec_ref_known(v_as_3398_, 2);
v___x_3404_ = l_Lean_registerBuiltinAttribute(v_head_3402_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_dec_ref_known(v___x_3404_, 1);
v_as_3398_ = v_tail_3403_;
goto _start;
}
else
{
lean_dec(v_tail_3403_);
return v___x_3404_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3406_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_addEntryFn_3409_, lean_object* v___x_3410_, lean_object* v_s_3411_){
_start:
{
lean_object* v_importedEntries_3412_; lean_object* v_state_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3421_; 
v_importedEntries_3412_ = lean_ctor_get(v_s_3411_, 0);
v_state_3413_ = lean_ctor_get(v_s_3411_, 1);
v_isSharedCheck_3421_ = !lean_is_exclusive(v_s_3411_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3415_ = v_s_3411_;
v_isShared_3416_ = v_isSharedCheck_3421_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_state_3413_);
lean_inc(v_importedEntries_3412_);
lean_dec(v_s_3411_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3421_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v_state_3417_; lean_object* v___x_3419_; 
v_state_3417_ = lean_apply_2(v_addEntryFn_3409_, v_state_3413_, v___x_3410_);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 1, v_state_3417_);
v___x_3419_ = v___x_3415_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_importedEntries_3412_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v_state_3417_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2(lean_object* v_validate_3422_, lean_object* v_snd_3423_, lean_object* v_a_3424_, lean_object* v_fst_3425_, lean_object* v_decl_3426_, lean_object* v_stx_3427_, uint8_t v_kind_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v___y_3433_; lean_object* v_nextMacroScope_3434_; lean_object* v_ngen_3435_; lean_object* v_auxDeclNGen_3436_; lean_object* v_traceState_3437_; lean_object* v_recordedDeps_3438_; lean_object* v_messages_3439_; lean_object* v_infoState_3440_; lean_object* v_snapshotTasks_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___x_3478_; 
v___x_3478_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3427_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3478_) == 0)
{
uint8_t v___x_3479_; uint8_t v___x_3480_; 
lean_dec_ref_known(v___x_3478_, 1);
v___x_3479_ = 0;
v___x_3480_ = l_Lean_instBEqAttributeKind_beq(v_kind_3428_, v___x_3479_);
if (v___x_3480_ == 0)
{
lean_object* v___x_3481_; 
lean_dec(v_decl_3426_);
lean_dec_ref(v_a_3424_);
lean_dec(v_snd_3423_);
lean_dec_ref(v_validate_3422_);
v___x_3481_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3425_, v_kind_3428_, v___y_3429_, v___y_3430_);
return v___x_3481_;
}
else
{
goto v___jp_3473_;
}
}
else
{
lean_dec(v_decl_3426_);
lean_dec(v_fst_3425_);
lean_dec_ref(v_a_3424_);
lean_dec(v_snd_3423_);
lean_dec_ref(v_validate_3422_);
return v___x_3478_;
}
v___jp_3432_:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3444_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_3445_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3445_, 0, v___y_3443_);
lean_ctor_set(v___x_3445_, 1, v_nextMacroScope_3434_);
lean_ctor_set(v___x_3445_, 2, v_ngen_3435_);
lean_ctor_set(v___x_3445_, 3, v_auxDeclNGen_3436_);
lean_ctor_set(v___x_3445_, 4, v_traceState_3437_);
lean_ctor_set(v___x_3445_, 5, v___x_3444_);
lean_ctor_set(v___x_3445_, 6, v_recordedDeps_3438_);
lean_ctor_set(v___x_3445_, 7, v_messages_3439_);
lean_ctor_set(v___x_3445_, 8, v_infoState_3440_);
lean_ctor_set(v___x_3445_, 9, v_snapshotTasks_3441_);
v___x_3446_ = lean_st_ref_put(v___y_3442_, v___x_3445_);
v___x_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3447_, 0, v___y_3433_);
return v___x_3447_;
}
v___jp_3448_:
{
lean_object* v___x_3451_; 
lean_inc(v___y_3450_);
lean_inc_ref(v___y_3449_);
lean_inc(v_snd_3423_);
lean_inc(v_decl_3426_);
v___x_3451_ = lean_apply_5(v_validate_3422_, v_decl_3426_, v_snd_3423_, v___y_3449_, v___y_3450_, lean_box(0));
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v___x_3452_; lean_object* v_toEnvExtension_3453_; lean_object* v_env_3454_; lean_object* v_nextMacroScope_3455_; lean_object* v_ngen_3456_; lean_object* v_auxDeclNGen_3457_; lean_object* v_traceState_3458_; lean_object* v_recordedDeps_3459_; lean_object* v_messages_3460_; lean_object* v_infoState_3461_; lean_object* v_snapshotTasks_3462_; lean_object* v_addEntryFn_3463_; lean_object* v_asyncMode_3464_; uint8_t v_logWrites_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___f_3468_; uint8_t v___x_3469_; 
lean_dec_ref_known(v___x_3451_, 1);
v___x_3452_ = lean_st_ref_take(v___y_3450_);
v_toEnvExtension_3453_ = lean_ctor_get(v_a_3424_, 0);
lean_inc_ref(v_toEnvExtension_3453_);
v_env_3454_ = lean_ctor_get(v___x_3452_, 0);
lean_inc_ref(v_env_3454_);
v_nextMacroScope_3455_ = lean_ctor_get(v___x_3452_, 1);
lean_inc(v_nextMacroScope_3455_);
v_ngen_3456_ = lean_ctor_get(v___x_3452_, 2);
lean_inc_ref(v_ngen_3456_);
v_auxDeclNGen_3457_ = lean_ctor_get(v___x_3452_, 3);
lean_inc_ref(v_auxDeclNGen_3457_);
v_traceState_3458_ = lean_ctor_get(v___x_3452_, 4);
lean_inc_ref(v_traceState_3458_);
v_recordedDeps_3459_ = lean_ctor_get(v___x_3452_, 6);
lean_inc_ref(v_recordedDeps_3459_);
v_messages_3460_ = lean_ctor_get(v___x_3452_, 7);
lean_inc_ref(v_messages_3460_);
v_infoState_3461_ = lean_ctor_get(v___x_3452_, 8);
lean_inc_ref(v_infoState_3461_);
v_snapshotTasks_3462_ = lean_ctor_get(v___x_3452_, 9);
lean_inc_ref(v_snapshotTasks_3462_);
lean_dec(v___x_3452_);
v_addEntryFn_3463_ = lean_ctor_get(v_a_3424_, 3);
lean_inc(v_addEntryFn_3463_);
lean_dec_ref(v_a_3424_);
v_asyncMode_3464_ = lean_ctor_get(v_toEnvExtension_3453_, 2);
lean_inc(v_asyncMode_3464_);
v_logWrites_3465_ = lean_ctor_get_uint8(v_toEnvExtension_3453_, sizeof(void*)*6);
v___x_3466_ = lean_box(0);
lean_inc(v_decl_3426_);
v___x_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3467_, 0, v_decl_3426_);
lean_ctor_set(v___x_3467_, 1, v_snd_3423_);
v___f_3468_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3468_, 0, v_addEntryFn_3463_);
lean_closure_set(v___f_3468_, 1, v___x_3467_);
v___x_3469_ = 1;
if (v_logWrites_3465_ == 0)
{
lean_object* v___x_3470_; 
v___x_3470_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3453_, v_env_3454_, v___f_3468_, v_asyncMode_3464_, v_decl_3426_, v___x_3469_);
lean_dec(v_asyncMode_3464_);
v___y_3433_ = v___x_3466_;
v_nextMacroScope_3434_ = v_nextMacroScope_3455_;
v_ngen_3435_ = v_ngen_3456_;
v_auxDeclNGen_3436_ = v_auxDeclNGen_3457_;
v_traceState_3437_ = v_traceState_3458_;
v_recordedDeps_3438_ = v_recordedDeps_3459_;
v_messages_3439_ = v_messages_3460_;
v_infoState_3440_ = v_infoState_3461_;
v_snapshotTasks_3441_ = v_snapshotTasks_3462_;
v___y_3442_ = v___y_3450_;
v___y_3443_ = v___x_3470_;
goto v___jp_3432_;
}
else
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
lean_inc_ref(v_toEnvExtension_3453_);
v___x_3471_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3453_, v_env_3454_);
lean_dec_ref(v_env_3454_);
v___x_3472_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3453_, v___x_3471_, v___f_3468_, v_asyncMode_3464_, v_decl_3426_, v___x_3469_);
lean_dec(v_asyncMode_3464_);
v___y_3433_ = v___x_3466_;
v_nextMacroScope_3434_ = v_nextMacroScope_3455_;
v_ngen_3435_ = v_ngen_3456_;
v_auxDeclNGen_3436_ = v_auxDeclNGen_3457_;
v_traceState_3437_ = v_traceState_3458_;
v_recordedDeps_3438_ = v_recordedDeps_3459_;
v_messages_3439_ = v_messages_3460_;
v_infoState_3440_ = v_infoState_3461_;
v_snapshotTasks_3441_ = v_snapshotTasks_3462_;
v___y_3442_ = v___y_3450_;
v___y_3443_ = v___x_3472_;
goto v___jp_3432_;
}
}
else
{
lean_dec(v_decl_3426_);
lean_dec_ref(v_a_3424_);
lean_dec(v_snd_3423_);
return v___x_3451_;
}
}
v___jp_3473_:
{
lean_object* v___x_3474_; lean_object* v_env_3475_; lean_object* v___x_3476_; 
v___x_3474_ = lean_st_ref_get(v___y_3430_);
v_env_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc_ref(v_env_3475_);
lean_dec(v___x_3474_);
v___x_3476_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3475_, v_decl_3426_);
lean_dec_ref(v_env_3475_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_dec(v_fst_3425_);
v___y_3449_ = v___y_3429_;
v___y_3450_ = v___y_3430_;
goto v___jp_3448_;
}
else
{
lean_object* v___x_3477_; 
lean_dec_ref_known(v___x_3476_, 1);
lean_dec_ref(v_a_3424_);
lean_dec(v_snd_3423_);
lean_dec_ref(v_validate_3422_);
v___x_3477_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3425_, v_decl_3426_, v___y_3429_, v___y_3430_);
return v___x_3477_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2___boxed(lean_object* v_validate_3482_, lean_object* v_snd_3483_, lean_object* v_a_3484_, lean_object* v_fst_3485_, lean_object* v_decl_3486_, lean_object* v_stx_3487_, lean_object* v_kind_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
uint8_t v_kind_boxed_3492_; lean_object* v_res_3493_; 
v_kind_boxed_3492_ = lean_unbox(v_kind_3488_);
v_res_3493_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2(v_validate_3482_, v_snd_3483_, v_a_3484_, v_fst_3485_, v_decl_3486_, v_stx_3487_, v_kind_boxed_3492_, v___y_3489_, v___y_3490_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3494_, lean_object* v_decl_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3499_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3500_ = l_Lean_MessageData_ofName(v_fst_3494_);
v___x_3501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3499_);
lean_ctor_set(v___x_3501_, 1, v___x_3500_);
v___x_3502_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3501_);
lean_ctor_set(v___x_3503_, 1, v___x_3502_);
v___x_3504_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3503_, v___y_3496_, v___y_3497_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3505_, lean_object* v_decl_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3505_, v_decl_3506_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v_decl_3506_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3511_, lean_object* v_a_3512_, lean_object* v_ref_3513_, uint8_t v_applicationTime_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_){
_start:
{
if (lean_obj_tag(v_a_3515_) == 0)
{
lean_object* v___x_3517_; 
lean_dec(v_ref_3513_);
lean_dec_ref(v_a_3512_);
lean_dec_ref(v_validate_3511_);
v___x_3517_ = l_List_reverse___redArg(v_a_3516_);
return v___x_3517_;
}
else
{
lean_object* v_head_3518_; lean_object* v_snd_3519_; lean_object* v_tail_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3535_; 
v_head_3518_ = lean_ctor_get(v_a_3515_, 0);
lean_inc(v_head_3518_);
v_snd_3519_ = lean_ctor_get(v_head_3518_, 1);
lean_inc(v_snd_3519_);
v_tail_3520_ = lean_ctor_get(v_a_3515_, 1);
v_isSharedCheck_3535_ = !lean_is_exclusive(v_a_3515_);
if (v_isSharedCheck_3535_ == 0)
{
lean_object* v_unused_3536_; 
v_unused_3536_ = lean_ctor_get(v_a_3515_, 0);
lean_dec(v_unused_3536_);
v___x_3522_ = v_a_3515_;
v_isShared_3523_ = v_isSharedCheck_3535_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_tail_3520_);
lean_dec(v_a_3515_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3535_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v_fst_3524_; lean_object* v_fst_3525_; lean_object* v_snd_3526_; lean_object* v___f_3527_; lean_object* v___f_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3532_; 
v_fst_3524_ = lean_ctor_get(v_head_3518_, 0);
lean_inc_n(v_fst_3524_, 3);
lean_dec(v_head_3518_);
v_fst_3525_ = lean_ctor_get(v_snd_3519_, 0);
lean_inc(v_fst_3525_);
v_snd_3526_ = lean_ctor_get(v_snd_3519_, 1);
lean_inc(v_snd_3526_);
lean_dec(v_snd_3519_);
v___f_3527_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3527_, 0, v_fst_3524_);
lean_inc_ref(v_a_3512_);
lean_inc_ref(v_validate_3511_);
v___f_3528_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2___boxed), 10, 4);
lean_closure_set(v___f_3528_, 0, v_validate_3511_);
lean_closure_set(v___f_3528_, 1, v_snd_3526_);
lean_closure_set(v___f_3528_, 2, v_a_3512_);
lean_closure_set(v___f_3528_, 3, v_fst_3524_);
lean_inc(v_ref_3513_);
v___x_3529_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3529_, 0, v_ref_3513_);
lean_ctor_set(v___x_3529_, 1, v_fst_3524_);
lean_ctor_set(v___x_3529_, 2, v_fst_3525_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3, v_applicationTime_3514_);
v___x_3530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
lean_ctor_set(v___x_3530_, 1, v___f_3528_);
lean_ctor_set(v___x_3530_, 2, v___f_3527_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 1, v_a_3516_);
lean_ctor_set(v___x_3522_, 0, v___x_3530_);
v___x_3532_ = v___x_3522_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3530_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_a_3516_);
v___x_3532_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
v_a_3515_ = v_tail_3520_;
v_a_3516_ = v___x_3532_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3537_, lean_object* v_a_3538_, lean_object* v_ref_3539_, lean_object* v_applicationTime_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_){
_start:
{
uint8_t v_applicationTime_boxed_3543_; lean_object* v_res_3544_; 
v_applicationTime_boxed_3543_ = lean_unbox(v_applicationTime_3540_);
v_res_3544_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3537_, v_a_3538_, v_ref_3539_, v_applicationTime_boxed_3543_, v_a_3541_, v_a_3542_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3558_, lean_object* v_validate_3559_, uint8_t v_applicationTime_3560_, lean_object* v_ref_3561_){
_start:
{
lean_object* v___f_3563_; lean_object* v___f_3564_; lean_object* v___f_3565_; lean_object* v___f_3566_; lean_object* v___f_3567_; lean_object* v___f_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___f_3563_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3564_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3565_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3566_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3567_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3568_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3569_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3570_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
v___x_3571_ = 0;
lean_inc(v_ref_3561_);
v___x_3572_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_3572_, 0, v_ref_3561_);
lean_ctor_set(v___x_3572_, 1, v___f_3567_);
lean_ctor_set(v___x_3572_, 2, v___f_3568_);
lean_ctor_set(v___x_3572_, 3, v___f_3566_);
lean_ctor_set(v___x_3572_, 4, v___f_3565_);
lean_ctor_set(v___x_3572_, 5, v___f_3564_);
lean_ctor_set(v___x_3572_, 6, v___x_3569_);
lean_ctor_set(v___x_3572_, 7, v___x_3570_);
lean_ctor_set_uint8(v___x_3572_, sizeof(void*)*8, v___x_3571_);
lean_ctor_set_uint8(v___x_3572_, sizeof(void*)*8 + 1, v___x_3571_);
v___x_3573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
lean_ctor_set(v___x_3573_, 1, v___f_3563_);
v___x_3574_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3573_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc_n(v_a_3575_, 2);
lean_dec_ref_known(v___x_3574_, 1);
v___x_3576_ = lean_box(0);
v___x_3577_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3559_, v_a_3575_, v_ref_3561_, v_applicationTime_3560_, v_attrDescrs_3558_, v___x_3576_);
lean_inc(v___x_3577_);
v___x_3578_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3577_);
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3586_; 
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3586_ == 0)
{
lean_object* v_unused_3587_; 
v_unused_3587_ = lean_ctor_get(v___x_3578_, 0);
lean_dec(v_unused_3587_);
v___x_3580_ = v___x_3578_;
v_isShared_3581_ = v_isSharedCheck_3586_;
goto v_resetjp_3579_;
}
else
{
lean_dec(v___x_3578_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3586_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3582_; lean_object* v___x_3584_; 
v___x_3582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3577_);
lean_ctor_set(v___x_3582_, 1, v_a_3575_);
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 0, v___x_3582_);
v___x_3584_ = v___x_3580_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3582_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec(v___x_3577_);
lean_dec(v_a_3575_);
v_a_3588_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3578_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3578_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
else
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
lean_dec(v_ref_3561_);
lean_dec_ref(v_validate_3559_);
lean_dec(v_attrDescrs_3558_);
v_a_3596_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3598_ = v___x_3574_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3574_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3604_, lean_object* v_validate_3605_, lean_object* v_applicationTime_3606_, lean_object* v_ref_3607_, lean_object* v_a_3608_){
_start:
{
uint8_t v_applicationTime_boxed_3609_; lean_object* v_res_3610_; 
v_applicationTime_boxed_3609_ = lean_unbox(v_applicationTime_3606_);
v_res_3610_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3604_, v_validate_3605_, v_applicationTime_boxed_3609_, v_ref_3607_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3611_, lean_object* v_attrDescrs_3612_, lean_object* v_validate_3613_, uint8_t v_applicationTime_3614_, lean_object* v_ref_3615_){
_start:
{
lean_object* v___x_3617_; 
v___x_3617_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3612_, v_validate_3613_, v_applicationTime_3614_, v_ref_3615_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3618_, lean_object* v_attrDescrs_3619_, lean_object* v_validate_3620_, lean_object* v_applicationTime_3621_, lean_object* v_ref_3622_, lean_object* v_a_3623_){
_start:
{
uint8_t v_applicationTime_boxed_3624_; lean_object* v_res_3625_; 
v_applicationTime_boxed_3624_ = lean_unbox(v_applicationTime_3621_);
v_res_3625_ = l_Lean_registerEnumAttributes(v_00_u03b1_3618_, v_attrDescrs_3619_, v_validate_3620_, v_applicationTime_boxed_3624_, v_ref_3622_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3626_, lean_object* v_env_3627_, lean_object* v_as_3628_, size_t v_i_3629_, size_t v_stop_3630_, lean_object* v_b_3631_){
_start:
{
lean_object* v___x_3632_; 
v___x_3632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3627_, v_as_3628_, v_i_3629_, v_stop_3630_, v_b_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3633_, lean_object* v_env_3634_, lean_object* v_as_3635_, lean_object* v_i_3636_, lean_object* v_stop_3637_, lean_object* v_b_3638_){
_start:
{
size_t v_i_boxed_3639_; size_t v_stop_boxed_3640_; lean_object* v_res_3641_; 
v_i_boxed_3639_ = lean_unbox_usize(v_i_3636_);
lean_dec(v_i_3636_);
v_stop_boxed_3640_ = lean_unbox_usize(v_stop_3637_);
lean_dec(v_stop_3637_);
v_res_3641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3633_, v_env_3634_, v_as_3635_, v_i_boxed_3639_, v_stop_boxed_3640_, v_b_3638_);
lean_dec_ref(v_as_3635_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3642_, lean_object* v_newState_3643_, lean_object* v_x_3644_, lean_object* v_x_3645_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3643_, v_x_3644_, v_x_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3647_, lean_object* v_newState_3648_, lean_object* v_x_3649_, lean_object* v_x_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3647_, v_newState_3648_, v_x_3649_, v_x_3650_);
lean_dec(v_newState_3648_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3652_, lean_object* v_validate_3653_, lean_object* v_a_3654_, lean_object* v_ref_3655_, uint8_t v_applicationTime_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_){
_start:
{
lean_object* v___x_3659_; 
v___x_3659_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3653_, v_a_3654_, v_ref_3655_, v_applicationTime_3656_, v_a_3657_, v_a_3658_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3660_, lean_object* v_validate_3661_, lean_object* v_a_3662_, lean_object* v_ref_3663_, lean_object* v_applicationTime_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
uint8_t v_applicationTime_boxed_3667_; lean_object* v_res_3668_; 
v_applicationTime_boxed_3667_ = lean_unbox(v_applicationTime_3664_);
v_res_3668_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3660_, v_validate_3661_, v_a_3662_, v_ref_3663_, v_applicationTime_boxed_3667_, v_a_3665_, v_a_3666_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3669_, lean_object* v_attr_3670_, lean_object* v_env_3671_, lean_object* v_decl_3672_){
_start:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3673_ = lean_box(1);
v___x_3674_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3671_, v_decl_3672_);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_object* v_ext_3675_; lean_object* v_toEnvExtension_3676_; lean_object* v_asyncMode_3677_; uint8_t v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; 
lean_dec(v_inst_3669_);
v_ext_3675_ = lean_ctor_get(v_attr_3670_, 1);
lean_inc_ref(v_ext_3675_);
lean_dec_ref(v_attr_3670_);
v_toEnvExtension_3676_ = lean_ctor_get(v_ext_3675_, 0);
v_asyncMode_3677_ = lean_ctor_get(v_toEnvExtension_3676_, 2);
lean_inc(v_asyncMode_3677_);
v___x_3678_ = 0;
lean_inc(v_decl_3672_);
v___x_3679_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3673_, v_ext_3675_, v_env_3671_, v_asyncMode_3677_, v_decl_3672_, v___x_3678_);
lean_dec(v_asyncMode_3677_);
lean_dec_ref(v_ext_3675_);
v___x_3680_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3679_, v_decl_3672_);
lean_dec(v_decl_3672_);
lean_dec(v___x_3679_);
return v___x_3680_;
}
else
{
lean_object* v_val_3681_; lean_object* v_ext_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3712_; 
v_val_3681_ = lean_ctor_get(v___x_3674_, 0);
lean_inc(v_val_3681_);
lean_dec_ref_known(v___x_3674_, 1);
v_ext_3682_ = lean_ctor_get(v_attr_3670_, 1);
v_isSharedCheck_3712_ = !lean_is_exclusive(v_attr_3670_);
if (v_isSharedCheck_3712_ == 0)
{
lean_object* v_unused_3713_; 
v_unused_3713_ = lean_ctor_get(v_attr_3670_, 0);
lean_dec(v_unused_3713_);
v___x_3684_ = v_attr_3670_;
v_isShared_3685_ = v_isSharedCheck_3712_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_ext_3682_);
lean_dec(v_attr_3670_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3712_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
uint8_t v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; uint8_t v___x_3690_; 
v___x_3686_ = 0;
v___x_3687_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3673_, v_ext_3682_, v_env_3671_, v_val_3681_, v___x_3686_);
lean_dec(v_val_3681_);
lean_dec_ref(v_env_3671_);
lean_dec_ref(v_ext_3682_);
v___x_3688_ = lean_unsigned_to_nat(0u);
v___x_3689_ = lean_array_get_size(v___x_3687_);
v___x_3690_ = lean_nat_dec_lt(v___x_3688_, v___x_3689_);
if (v___x_3690_ == 0)
{
lean_object* v___x_3691_; 
lean_dec_ref(v___x_3687_);
lean_del_object(v___x_3684_);
lean_dec(v_decl_3672_);
lean_dec(v_inst_3669_);
v___x_3691_ = lean_box(0);
return v___x_3691_;
}
else
{
lean_object* v___x_3692_; lean_object* v___x_3693_; uint8_t v___x_3694_; 
v___x_3692_ = lean_unsigned_to_nat(1u);
v___x_3693_ = lean_nat_sub(v___x_3689_, v___x_3692_);
v___x_3694_ = lean_nat_dec_le(v___x_3688_, v___x_3693_);
if (v___x_3694_ == 0)
{
lean_object* v___x_3695_; 
lean_dec(v___x_3693_);
lean_dec_ref(v___x_3687_);
lean_del_object(v___x_3684_);
lean_dec(v_decl_3672_);
lean_dec(v_inst_3669_);
v___x_3695_ = lean_box(0);
return v___x_3695_;
}
else
{
lean_object* v___f_3696_; lean_object* v___x_3698_; 
v___f_3696_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 1, v_inst_3669_);
lean_ctor_set(v___x_3684_, 0, v_decl_3672_);
v___x_3698_ = v___x_3684_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_decl_3672_);
lean_ctor_set(v_reuseFailAlloc_3711_, 1, v_inst_3669_);
v___x_3698_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3699_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3700_ = l_Array_binSearchAux___redArg(v___f_3696_, v___x_3699_, v___x_3687_, v___x_3698_, v___x_3688_, v___x_3693_);
lean_dec_ref(v___x_3687_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v___x_3701_; 
v___x_3701_ = lean_box(0);
return v___x_3701_;
}
else
{
lean_object* v_val_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3710_; 
v_val_3702_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3704_ = v___x_3700_;
v_isShared_3705_ = v_isSharedCheck_3710_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_val_3702_);
lean_dec(v___x_3700_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3710_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v_snd_3706_; lean_object* v___x_3708_; 
v_snd_3706_ = lean_ctor_get(v_val_3702_, 1);
lean_inc(v_snd_3706_);
lean_dec(v_val_3702_);
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 0, v_snd_3706_);
v___x_3708_ = v___x_3704_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_snd_3706_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3714_, lean_object* v_inst_3715_, lean_object* v_attr_3716_, lean_object* v_env_3717_, lean_object* v_decl_3718_){
_start:
{
lean_object* v___x_3719_; 
v___x_3719_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3715_, v_attr_3716_, v_env_3717_, v_decl_3718_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3728_, lean_object* v_env_3729_, lean_object* v_decl_3730_, lean_object* v_val_3731_){
_start:
{
lean_object* v_ext_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3802_; 
v_ext_3732_ = lean_ctor_get(v_attrs_3728_, 1);
v_isSharedCheck_3802_ = !lean_is_exclusive(v_attrs_3728_);
if (v_isSharedCheck_3802_ == 0)
{
lean_object* v_unused_3803_; 
v_unused_3803_ = lean_ctor_get(v_attrs_3728_, 0);
lean_dec(v_unused_3803_);
v___x_3734_ = v_attrs_3728_;
v_isShared_3735_ = v_isSharedCheck_3802_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_ext_3732_);
lean_dec(v_attrs_3728_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3802_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v_toEnvExtension_3736_; lean_object* v_name_3737_; lean_object* v_addEntryFn_3738_; lean_object* v___x_3739_; uint8_t v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v_pfx_3748_; lean_object* v___x_3749_; 
v_toEnvExtension_3736_ = lean_ctor_get(v_ext_3732_, 0);
lean_inc_ref(v_toEnvExtension_3736_);
v_name_3737_ = lean_ctor_get(v_ext_3732_, 1);
v_addEntryFn_3738_ = lean_ctor_get(v_ext_3732_, 3);
lean_inc(v_addEntryFn_3738_);
v___x_3739_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3740_ = 1;
lean_inc(v_name_3737_);
v___x_3741_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3737_, v___x_3740_);
v___x_3742_ = lean_string_append(v___x_3739_, v___x_3741_);
lean_dec_ref(v___x_3741_);
v___x_3743_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3744_ = lean_string_append(v___x_3742_, v___x_3743_);
lean_inc(v_decl_3730_);
v___x_3745_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3730_, v___x_3740_);
v___x_3746_ = lean_string_append(v___x_3744_, v___x_3745_);
lean_dec_ref(v___x_3745_);
v___x_3747_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3748_ = lean_string_append(v___x_3746_, v___x_3747_);
v___x_3749_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3729_, v_decl_3730_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v_asyncMode_3750_; uint8_t v_logWrites_3751_; uint8_t v___x_3752_; 
v_asyncMode_3750_ = lean_ctor_get(v_toEnvExtension_3736_, 2);
lean_inc(v_asyncMode_3750_);
v_logWrites_3751_ = lean_ctor_get_uint8(v_toEnvExtension_3736_, sizeof(void*)*6);
lean_inc(v_decl_3730_);
lean_inc_ref(v_env_3729_);
v___x_3752_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3729_, v_decl_3730_, v_asyncMode_3750_);
if (v___x_3752_ == 0)
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___y_3756_; lean_object* v___x_3760_; 
lean_dec(v_asyncMode_3750_);
lean_dec(v_addEntryFn_3738_);
lean_dec_ref(v_toEnvExtension_3736_);
lean_del_object(v___x_3734_);
lean_dec_ref(v_ext_3732_);
lean_dec(v_val_3731_);
lean_dec(v_decl_3730_);
v___x_3753_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3754_ = lean_string_append(v_pfx_3748_, v___x_3753_);
v___x_3760_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3729_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v___x_3761_; 
v___x_3761_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3756_ = v___x_3761_;
goto v___jp_3755_;
}
else
{
lean_object* v_val_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
v_val_3762_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_val_3762_);
lean_dec_ref_known(v___x_3760_, 1);
v___x_3763_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3764_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3762_, v___x_3740_);
v___x_3765_ = l_addParenHeuristic(v___x_3764_);
v___x_3766_ = lean_string_append(v___x_3763_, v___x_3765_);
lean_dec_ref(v___x_3765_);
v___x_3767_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3768_ = lean_string_append(v___x_3766_, v___x_3767_);
v___y_3756_ = v___x_3768_;
goto v___jp_3755_;
}
v___jp_3755_:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3757_ = lean_string_append(v___x_3754_, v___y_3756_);
lean_dec_ref(v___y_3756_);
v___x_3758_ = lean_string_append(v___x_3757_, v___x_3747_);
v___x_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3758_);
return v___x_3759_;
}
}
else
{
lean_object* v___x_3769_; uint8_t v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3769_ = lean_box(1);
v___x_3770_ = 0;
lean_inc(v_decl_3730_);
lean_inc_ref(v_env_3729_);
v___x_3771_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3769_, v_ext_3732_, v_env_3729_, v_asyncMode_3750_, v_decl_3730_, v___x_3770_);
lean_dec_ref(v_ext_3732_);
v___x_3772_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3771_, v_decl_3730_);
lean_dec(v___x_3771_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v___x_3774_; 
lean_dec_ref(v_pfx_3748_);
lean_inc(v_decl_3730_);
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 1, v_val_3731_);
lean_ctor_set(v___x_3734_, 0, v_decl_3730_);
v___x_3774_ = v___x_3734_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_decl_3730_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_val_3731_);
v___x_3774_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
lean_object* v___f_3775_; 
v___f_3775_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3775_, 0, v_addEntryFn_3738_);
lean_closure_set(v___f_3775_, 1, v___x_3774_);
if (v_logWrites_3751_ == 0)
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3776_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3736_, v_env_3729_, v___f_3775_, v_asyncMode_3750_, v_decl_3730_, v___x_3752_);
lean_dec(v_asyncMode_3750_);
v___x_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3776_);
return v___x_3777_;
}
else
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
lean_inc_ref(v_toEnvExtension_3736_);
v___x_3778_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3736_, v_env_3729_);
lean_dec_ref(v_env_3729_);
v___x_3779_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3736_, v___x_3778_, v___f_3775_, v_asyncMode_3750_, v_decl_3730_, v___x_3752_);
lean_dec(v_asyncMode_3750_);
v___x_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3779_);
return v___x_3780_;
}
}
}
else
{
lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3790_; 
lean_dec(v_asyncMode_3750_);
lean_dec(v_addEntryFn_3738_);
lean_dec_ref(v_toEnvExtension_3736_);
lean_del_object(v___x_3734_);
lean_dec(v_val_3731_);
lean_dec(v_decl_3730_);
lean_dec_ref(v_env_3729_);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3790_ == 0)
{
lean_object* v_unused_3791_; 
v_unused_3791_ = lean_ctor_get(v___x_3772_, 0);
lean_dec(v_unused_3791_);
v___x_3783_ = v___x_3772_;
v_isShared_3784_ = v_isSharedCheck_3790_;
goto v_resetjp_3782_;
}
else
{
lean_dec(v___x_3772_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3790_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3788_; 
v___x_3785_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3786_ = lean_string_append(v_pfx_3748_, v___x_3785_);
if (v_isShared_3784_ == 0)
{
lean_ctor_set_tag(v___x_3783_, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3786_);
v___x_3788_ = v___x_3783_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3786_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
}
else
{
lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3800_; 
lean_dec(v_addEntryFn_3738_);
lean_dec_ref(v_toEnvExtension_3736_);
lean_del_object(v___x_3734_);
lean_dec_ref(v_ext_3732_);
lean_dec(v_val_3731_);
lean_dec(v_decl_3730_);
lean_dec_ref(v_env_3729_);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3800_ == 0)
{
lean_object* v_unused_3801_; 
v_unused_3801_ = lean_ctor_get(v___x_3749_, 0);
lean_dec(v_unused_3801_);
v___x_3793_ = v___x_3749_;
v_isShared_3794_ = v_isSharedCheck_3800_;
goto v_resetjp_3792_;
}
else
{
lean_dec(v___x_3749_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3800_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3798_; 
v___x_3795_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3796_ = lean_string_append(v_pfx_3748_, v___x_3795_);
if (v_isShared_3794_ == 0)
{
lean_ctor_set_tag(v___x_3793_, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3796_);
v___x_3798_ = v___x_3793_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3796_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3804_, lean_object* v_attrs_3805_, lean_object* v_env_3806_, lean_object* v_decl_3807_, lean_object* v_val_3808_){
_start:
{
lean_object* v___x_3809_; 
v___x_3809_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3805_, v_env_3806_, v_decl_3807_, v_val_3808_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3811_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3812_ = lean_st_mk_ref(v___x_3811_);
v___x_3813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3812_);
return v___x_3813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3818_, lean_object* v_builder_3819_){
_start:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
v___x_3821_ = l_Lean_attributeImplBuilderTableRef;
v___x_3822_ = lean_st_ref_get(v___x_3821_);
v___x_3823_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3822_, v_builderId_3818_);
lean_dec(v___x_3822_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3824_ = lean_st_ref_take(v___x_3821_);
v___x_3825_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3824_, v_builderId_3818_, v_builder_3819_);
v___x_3826_ = lean_st_ref_put(v___x_3821_, v___x_3825_);
v___x_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3826_);
return v___x_3827_;
}
else
{
lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
lean_dec_ref(v_builder_3819_);
v___x_3828_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3829_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3818_, v___x_3823_);
v___x_3830_ = lean_string_append(v___x_3828_, v___x_3829_);
lean_dec_ref(v___x_3829_);
v___x_3831_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3832_ = lean_string_append(v___x_3830_, v___x_3831_);
v___x_3833_ = lean_mk_io_user_error(v___x_3832_);
v___x_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3833_);
return v___x_3834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3835_, lean_object* v_builder_3836_, lean_object* v_a_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Lean_registerAttributeImplBuilder(v_builderId_3835_, v_builder_3836_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3839_){
_start:
{
if (lean_obj_tag(v_e_3839_) == 0)
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3849_; 
v_a_3841_ = lean_ctor_get(v_e_3839_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v_e_3839_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3843_ = v_e_3839_;
v_isShared_3844_ = v_isSharedCheck_3849_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v_e_3839_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3849_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3845_; lean_object* v___x_3847_; 
v___x_3845_ = lean_mk_io_user_error(v_a_3841_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set_tag(v___x_3843_, 1);
lean_ctor_set(v___x_3843_, 0, v___x_3845_);
v___x_3847_ = v___x_3843_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3845_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
v_a_3850_ = lean_ctor_get(v_e_3839_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v_e_3839_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v_e_3839_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v_e_3839_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
lean_ctor_set_tag(v___x_3852_, 0);
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3858_, lean_object* v_a_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3858_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3861_, lean_object* v_e_3862_){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3862_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3865_, lean_object* v_e_3866_, lean_object* v_a_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3865_, v_e_3866_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3869_, lean_object* v_x_3870_){
_start:
{
if (lean_obj_tag(v_x_3870_) == 0)
{
lean_object* v___x_3871_; 
v___x_3871_ = lean_box(0);
return v___x_3871_;
}
else
{
lean_object* v_key_3872_; lean_object* v_value_3873_; lean_object* v_tail_3874_; uint8_t v___x_3875_; 
v_key_3872_ = lean_ctor_get(v_x_3870_, 0);
v_value_3873_ = lean_ctor_get(v_x_3870_, 1);
v_tail_3874_ = lean_ctor_get(v_x_3870_, 2);
v___x_3875_ = lean_name_eq(v_key_3872_, v_a_3869_);
if (v___x_3875_ == 0)
{
v_x_3870_ = v_tail_3874_;
goto _start;
}
else
{
lean_object* v___x_3877_; 
lean_inc(v_value_3873_);
v___x_3877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3877_, 0, v_value_3873_);
return v___x_3877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3878_, lean_object* v_x_3879_){
_start:
{
lean_object* v_res_3880_; 
v_res_3880_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3878_, v_x_3879_);
lean_dec(v_x_3879_);
lean_dec(v_a_3878_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3881_, lean_object* v_a_3882_){
_start:
{
lean_object* v_buckets_3883_; lean_object* v___x_3884_; uint64_t v___y_3886_; 
v_buckets_3883_ = lean_ctor_get(v_m_3881_, 1);
v___x_3884_ = lean_array_get_size(v_buckets_3883_);
if (lean_obj_tag(v_a_3882_) == 0)
{
uint64_t v___x_3900_; 
v___x_3900_ = 1723ULL;
v___y_3886_ = v___x_3900_;
goto v___jp_3885_;
}
else
{
uint64_t v_hash_3901_; 
v_hash_3901_ = lean_ctor_get_uint64(v_a_3882_, sizeof(void*)*2);
v___y_3886_ = v_hash_3901_;
goto v___jp_3885_;
}
v___jp_3885_:
{
uint64_t v___x_3887_; uint64_t v___x_3888_; uint64_t v_fold_3889_; uint64_t v___x_3890_; uint64_t v___x_3891_; uint64_t v___x_3892_; size_t v___x_3893_; size_t v___x_3894_; size_t v___x_3895_; size_t v___x_3896_; size_t v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3887_ = 32ULL;
v___x_3888_ = lean_uint64_shift_right(v___y_3886_, v___x_3887_);
v_fold_3889_ = lean_uint64_xor(v___y_3886_, v___x_3888_);
v___x_3890_ = 16ULL;
v___x_3891_ = lean_uint64_shift_right(v_fold_3889_, v___x_3890_);
v___x_3892_ = lean_uint64_xor(v_fold_3889_, v___x_3891_);
v___x_3893_ = lean_uint64_to_usize(v___x_3892_);
v___x_3894_ = lean_usize_of_nat(v___x_3884_);
v___x_3895_ = ((size_t)1ULL);
v___x_3896_ = lean_usize_sub(v___x_3894_, v___x_3895_);
v___x_3897_ = lean_usize_land(v___x_3893_, v___x_3896_);
v___x_3898_ = lean_array_uget_borrowed(v_buckets_3883_, v___x_3897_);
v___x_3899_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3882_, v___x_3898_);
return v___x_3899_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3902_, lean_object* v_a_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3902_, v_a_3903_);
lean_dec(v_a_3903_);
lean_dec_ref(v_m_3902_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3906_){
_start:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v_builderId_3910_; lean_object* v_ref_3911_; lean_object* v_args_3912_; lean_object* v___x_3913_; 
v___x_3908_ = l_Lean_attributeImplBuilderTableRef;
v___x_3909_ = lean_st_ref_get(v___x_3908_);
v_builderId_3910_ = lean_ctor_get(v_e_3906_, 0);
lean_inc(v_builderId_3910_);
v_ref_3911_ = lean_ctor_get(v_e_3906_, 1);
lean_inc(v_ref_3911_);
v_args_3912_ = lean_ctor_get(v_e_3906_, 2);
lean_inc(v_args_3912_);
lean_dec_ref(v_e_3906_);
v___x_3913_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3909_, v_builderId_3910_);
lean_dec(v___x_3909_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v___x_3914_; uint8_t v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
lean_dec(v_args_3912_);
lean_dec(v_ref_3911_);
v___x_3914_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3915_ = 1;
v___x_3916_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3910_, v___x_3915_);
v___x_3917_ = lean_string_append(v___x_3914_, v___x_3916_);
lean_dec_ref(v___x_3916_);
v___x_3918_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3919_ = lean_string_append(v___x_3917_, v___x_3918_);
v___x_3920_ = lean_mk_io_user_error(v___x_3919_);
v___x_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
return v___x_3921_;
}
else
{
lean_object* v_val_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
lean_dec(v_builderId_3910_);
v_val_3922_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_val_3922_);
lean_dec_ref_known(v___x_3913_, 1);
v___x_3923_ = lean_apply_2(v_val_3922_, v_ref_3911_, v_args_3912_);
v___x_3924_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3923_);
return v___x_3924_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3925_, lean_object* v_a_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l_Lean_mkAttributeImplOfEntry(v_e_3925_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3928_, lean_object* v_m_3929_, lean_object* v_a_3930_){
_start:
{
lean_object* v___x_3931_; 
v___x_3931_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3929_, v_a_3930_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3932_, lean_object* v_m_3933_, lean_object* v_a_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3932_, v_m_3933_, v_a_3934_);
lean_dec(v_a_3934_);
lean_dec_ref(v_m_3933_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3936_, lean_object* v_a_3937_, lean_object* v_x_3938_){
_start:
{
lean_object* v___x_3939_; 
v___x_3939_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3937_, v_x_3938_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3940_, lean_object* v_a_3941_, lean_object* v_x_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3940_, v_a_3941_, v_x_3942_);
lean_dec(v_x_3942_);
lean_dec(v_a_3941_);
return v_res_3943_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3944_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3945_ = lean_box(0);
v___x_3946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3945_);
lean_ctor_set(v___x_3946_, 1, v___x_3944_);
return v___x_3946_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3947_; 
v___x_3947_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3947_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3948_; 
v___x_3948_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3950_ = l_Lean_attributeMapRef;
v___x_3951_ = lean_st_ref_get(v___x_3950_);
v___x_3952_ = lean_box(0);
v___x_3953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3952_);
lean_ctor_set(v___x_3953_, 1, v___x_3951_);
v___x_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3953_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3955_){
_start:
{
lean_object* v_res_3956_; 
v_res_3956_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3962_, lean_object* v_opts_3963_, lean_object* v_declName_3964_){
_start:
{
uint8_t v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = 0;
lean_inc(v_declName_3964_);
lean_inc_ref(v_env_3962_);
v___x_3968_ = l_Lean_Environment_find_x3f(v_env_3962_, v_declName_3964_, v___x_3967_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v___x_3969_; uint8_t v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
lean_dec_ref(v_env_3962_);
v___x_3969_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3970_ = 1;
v___x_3971_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3964_, v___x_3970_);
v___x_3972_ = lean_string_append(v___x_3969_, v___x_3971_);
lean_dec_ref(v___x_3971_);
v___x_3973_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3974_ = lean_string_append(v___x_3972_, v___x_3973_);
v___x_3975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3975_, 0, v___x_3974_);
return v___x_3975_;
}
else
{
lean_object* v_val_3976_; lean_object* v___x_3977_; 
v_val_3976_ = lean_ctor_get(v___x_3968_, 0);
lean_inc(v_val_3976_);
lean_dec_ref_known(v___x_3968_, 1);
v___x_3977_ = l_Lean_ConstantInfo_type(v_val_3976_);
lean_dec(v_val_3976_);
if (lean_obj_tag(v___x_3977_) == 4)
{
lean_object* v_declName_3978_; 
v_declName_3978_ = lean_ctor_get(v___x_3977_, 0);
lean_inc(v_declName_3978_);
lean_dec_ref_known(v___x_3977_, 2);
if (lean_obj_tag(v_declName_3978_) == 1)
{
lean_object* v_pre_3979_; 
v_pre_3979_ = lean_ctor_get(v_declName_3978_, 0);
lean_inc(v_pre_3979_);
if (lean_obj_tag(v_pre_3979_) == 1)
{
lean_object* v_pre_3980_; 
v_pre_3980_ = lean_ctor_get(v_pre_3979_, 0);
if (lean_obj_tag(v_pre_3980_) == 0)
{
lean_object* v_str_3981_; lean_object* v_str_3982_; lean_object* v___x_3983_; uint8_t v___x_3984_; 
v_str_3981_ = lean_ctor_get(v_declName_3978_, 1);
lean_inc_ref(v_str_3981_);
lean_dec_ref_known(v_declName_3978_, 2);
v_str_3982_ = lean_ctor_get(v_pre_3979_, 1);
lean_inc_ref(v_str_3982_);
lean_dec_ref_known(v_pre_3979_, 2);
v___x_3983_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_3984_ = lean_string_dec_eq(v_str_3982_, v___x_3983_);
lean_dec_ref(v_str_3982_);
if (v___x_3984_ == 0)
{
lean_dec_ref(v_str_3981_);
lean_dec(v_declName_3964_);
lean_dec_ref(v_env_3962_);
goto v___jp_3965_;
}
else
{
lean_object* v___x_3985_; uint8_t v___x_3986_; 
v___x_3985_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_3986_ = lean_string_dec_eq(v_str_3981_, v___x_3985_);
lean_dec_ref(v_str_3981_);
if (v___x_3986_ == 0)
{
lean_dec(v_declName_3964_);
lean_dec_ref(v_env_3962_);
goto v___jp_3965_;
}
else
{
lean_object* v___x_3987_; 
v___x_3987_ = l_Lean_Environment_evalConst___redArg(v_env_3962_, v_opts_3963_, v_declName_3964_, v___x_3986_);
lean_dec(v_declName_3964_);
lean_dec_ref(v_env_3962_);
return v___x_3987_;
}
}
}
else
{
lean_dec_ref_known(v_pre_3979_, 2);
lean_dec_ref_known(v_declName_3978_, 2);
lean_dec(v_declName_3964_);
lean_dec_ref(v_env_3962_);
goto v___jp_3965_;
}
}
else
{
lean_dec_ref_known(v_declName_3978_, 2);
lean_dec(v_pre_3979_);
lean_dec(v_declName_3964_);
lean_dec_ref(v_env_3962_);
goto v___jp_3965_;
}
}
else
{
lean_dec(v_declName_3978_);
lean_dec(v_declName_3964_);
lean_dec_ref(v_env_3962_);
goto v___jp_3965_;
}
}
else
{
lean_dec_ref(v___x_3977_);
lean_dec(v_declName_3964_);
lean_dec_ref(v_env_3962_);
goto v___jp_3965_;
}
}
v___jp_3965_:
{
lean_object* v___x_3966_; 
v___x_3966_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_3988_, lean_object* v_opts_3989_, lean_object* v_declName_3990_){
_start:
{
lean_object* v_res_3991_; 
v_res_3991_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_3988_, v_opts_3989_, v_declName_3990_);
lean_dec_ref(v_opts_3989_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_3992_, size_t v_i_3993_, size_t v_stop_3994_, lean_object* v_b_3995_){
_start:
{
uint8_t v___x_3997_; 
v___x_3997_ = lean_usize_dec_eq(v_i_3993_, v_stop_3994_);
if (v___x_3997_ == 0)
{
lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3998_ = lean_array_uget_borrowed(v_as_3992_, v_i_3993_);
lean_inc(v___x_3998_);
v___x_3999_ = l_Lean_mkAttributeImplOfEntry(v___x_3998_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; lean_object* v_toAttributeImplCore_4001_; lean_object* v_name_4002_; lean_object* v___x_4003_; size_t v___x_4004_; size_t v___x_4005_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc(v_a_4000_);
lean_dec_ref_known(v___x_3999_, 1);
v_toAttributeImplCore_4001_ = lean_ctor_get(v_a_4000_, 0);
v_name_4002_ = lean_ctor_get(v_toAttributeImplCore_4001_, 1);
lean_inc(v_name_4002_);
v___x_4003_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_3995_, v_name_4002_, v_a_4000_);
v___x_4004_ = ((size_t)1ULL);
v___x_4005_ = lean_usize_add(v_i_3993_, v___x_4004_);
v_i_3993_ = v___x_4005_;
v_b_3995_ = v___x_4003_;
goto _start;
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
lean_dec_ref(v_b_3995_);
v_a_4007_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_3999_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_3999_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
else
{
lean_object* v___x_4015_; 
v___x_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4015_, 0, v_b_3995_);
return v___x_4015_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_4016_, lean_object* v_i_4017_, lean_object* v_stop_4018_, lean_object* v_b_4019_, lean_object* v___y_4020_){
_start:
{
size_t v_i_boxed_4021_; size_t v_stop_boxed_4022_; lean_object* v_res_4023_; 
v_i_boxed_4021_ = lean_unbox_usize(v_i_4017_);
lean_dec(v_i_4017_);
v_stop_boxed_4022_ = lean_unbox_usize(v_stop_4018_);
lean_dec(v_stop_4018_);
v_res_4023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4016_, v_i_boxed_4021_, v_stop_boxed_4022_, v_b_4019_);
lean_dec_ref(v_as_4016_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_4024_, size_t v_i_4025_, size_t v_stop_4026_, lean_object* v_b_4027_, lean_object* v___y_4028_){
_start:
{
lean_object* v_a_4031_; uint8_t v___x_4035_; 
v___x_4035_ = lean_usize_dec_eq(v_i_4025_, v_stop_4026_);
if (v___x_4035_ == 0)
{
lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; uint8_t v___x_4039_; 
v___x_4036_ = lean_array_uget_borrowed(v_as_4024_, v_i_4025_);
v___x_4037_ = lean_unsigned_to_nat(0u);
v___x_4038_ = lean_array_get_size(v___x_4036_);
v___x_4039_ = lean_nat_dec_lt(v___x_4037_, v___x_4038_);
if (v___x_4039_ == 0)
{
v_a_4031_ = v_b_4027_;
goto v___jp_4030_;
}
else
{
size_t v___x_4040_; size_t v___x_4041_; lean_object* v___x_4042_; 
v___x_4040_ = ((size_t)0ULL);
v___x_4041_ = lean_usize_of_nat(v___x_4038_);
v___x_4042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4036_, v___x_4040_, v___x_4041_, v_b_4027_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v_a_4043_; 
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
lean_inc(v_a_4043_);
lean_dec_ref_known(v___x_4042_, 1);
v_a_4031_ = v_a_4043_;
goto v___jp_4030_;
}
else
{
return v___x_4042_;
}
}
}
else
{
lean_object* v___x_4044_; 
v___x_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4044_, 0, v_b_4027_);
return v___x_4044_;
}
v___jp_4030_:
{
size_t v___x_4032_; size_t v___x_4033_; 
v___x_4032_ = ((size_t)1ULL);
v___x_4033_ = lean_usize_add(v_i_4025_, v___x_4032_);
v_i_4025_ = v___x_4033_;
v_b_4027_ = v_a_4031_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4045_, lean_object* v_i_4046_, lean_object* v_stop_4047_, lean_object* v_b_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_){
_start:
{
size_t v_i_boxed_4051_; size_t v_stop_boxed_4052_; lean_object* v_res_4053_; 
v_i_boxed_4051_ = lean_unbox_usize(v_i_4046_);
lean_dec(v_i_4046_);
v_stop_boxed_4052_ = lean_unbox_usize(v_stop_4047_);
lean_dec(v_stop_4047_);
v_res_4053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4045_, v_i_boxed_4051_, v_stop_boxed_4052_, v_b_4048_, v___y_4049_);
lean_dec_ref(v___y_4049_);
lean_dec_ref(v_as_4045_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4054_, lean_object* v_a_4055_){
_start:
{
lean_object* v_a_4058_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; uint8_t v___x_4066_; 
v___x_4062_ = l_Lean_attributeMapRef;
v___x_4063_ = lean_st_ref_get(v___x_4062_);
v___x_4064_ = lean_unsigned_to_nat(0u);
v___x_4065_ = lean_array_get_size(v_es_4054_);
v___x_4066_ = lean_nat_dec_lt(v___x_4064_, v___x_4065_);
if (v___x_4066_ == 0)
{
v_a_4058_ = v___x_4063_;
goto v___jp_4057_;
}
else
{
size_t v___x_4067_; size_t v___x_4068_; lean_object* v___x_4069_; 
v___x_4067_ = ((size_t)0ULL);
v___x_4068_ = lean_usize_of_nat(v___x_4065_);
v___x_4069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4054_, v___x_4067_, v___x_4068_, v___x_4063_, v_a_4055_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_a_4070_; 
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc(v_a_4070_);
lean_dec_ref_known(v___x_4069_, 1);
v_a_4058_ = v_a_4070_;
goto v___jp_4057_;
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
v_a_4071_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_4069_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4069_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4071_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
v___jp_4057_:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4059_ = lean_box(0);
v___x_4060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4059_);
lean_ctor_set(v___x_4060_, 1, v_a_4058_);
v___x_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4060_);
return v___x_4061_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_){
_start:
{
lean_object* v_res_4082_; 
v_res_4082_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4079_, v_a_4080_);
lean_dec_ref(v_a_4080_);
lean_dec_ref(v_es_4079_);
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4083_, size_t v_i_4084_, size_t v_stop_4085_, lean_object* v_b_4086_, lean_object* v___y_4087_){
_start:
{
lean_object* v___x_4089_; 
v___x_4089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4083_, v_i_4084_, v_stop_4085_, v_b_4086_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4090_, lean_object* v_i_4091_, lean_object* v_stop_4092_, lean_object* v_b_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_){
_start:
{
size_t v_i_boxed_4096_; size_t v_stop_boxed_4097_; lean_object* v_res_4098_; 
v_i_boxed_4096_ = lean_unbox_usize(v_i_4091_);
lean_dec(v_i_4091_);
v_stop_boxed_4097_ = lean_unbox_usize(v_stop_4092_);
lean_dec(v_stop_4092_);
v_res_4098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4090_, v_i_boxed_4096_, v_stop_boxed_4097_, v_b_4093_, v___y_4094_);
lean_dec_ref(v___y_4094_);
lean_dec_ref(v_as_4090_);
return v_res_4098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4099_, lean_object* v_e_4100_){
_start:
{
lean_object* v_snd_4101_; lean_object* v_toAttributeImplCore_4102_; lean_object* v_fst_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4121_; 
v_snd_4101_ = lean_ctor_get(v_e_4100_, 1);
lean_inc(v_snd_4101_);
v_toAttributeImplCore_4102_ = lean_ctor_get(v_snd_4101_, 0);
v_fst_4103_ = lean_ctor_get(v_e_4100_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v_e_4100_);
if (v_isSharedCheck_4121_ == 0)
{
lean_object* v_unused_4122_; 
v_unused_4122_ = lean_ctor_get(v_e_4100_, 1);
lean_dec(v_unused_4122_);
v___x_4105_ = v_e_4100_;
v_isShared_4106_ = v_isSharedCheck_4121_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_fst_4103_);
lean_dec(v_e_4100_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4121_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v_newEntries_4107_; lean_object* v_map_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4120_; 
v_newEntries_4107_ = lean_ctor_get(v_s_4099_, 0);
v_map_4108_ = lean_ctor_get(v_s_4099_, 1);
v_isSharedCheck_4120_ = !lean_is_exclusive(v_s_4099_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4110_ = v_s_4099_;
v_isShared_4111_ = v_isSharedCheck_4120_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_map_4108_);
lean_inc(v_newEntries_4107_);
lean_dec(v_s_4099_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4120_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v_name_4112_; lean_object* v___x_4114_; 
v_name_4112_ = lean_ctor_get(v_toAttributeImplCore_4102_, 1);
lean_inc(v_name_4112_);
if (v_isShared_4106_ == 0)
{
lean_ctor_set_tag(v___x_4105_, 1);
lean_ctor_set(v___x_4105_, 1, v_newEntries_4107_);
v___x_4114_ = v___x_4105_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_fst_4103_);
lean_ctor_set(v_reuseFailAlloc_4119_, 1, v_newEntries_4107_);
v___x_4114_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
lean_object* v___x_4115_; lean_object* v___x_4117_; 
v___x_4115_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4108_, v_name_4112_, v_snd_4101_);
if (v_isShared_4111_ == 0)
{
lean_ctor_set(v___x_4110_, 1, v___x_4115_);
lean_ctor_set(v___x_4110_, 0, v___x_4114_);
v___x_4117_ = v___x_4110_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___x_4114_);
lean_ctor_set(v_reuseFailAlloc_4118_, 1, v___x_4115_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4123_, lean_object* v_s_4124_){
_start:
{
lean_object* v_newEntries_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; 
v_newEntries_4125_ = lean_ctor_get(v_s_4124_, 0);
lean_inc(v_newEntries_4125_);
lean_dec_ref(v_s_4124_);
v___x_4126_ = l_List_reverse___redArg(v_newEntries_4125_);
v___x_4127_ = lean_array_mk(v___x_4126_);
lean_inc_ref_n(v___x_4127_, 2);
v___x_4128_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4127_);
lean_ctor_set(v___x_4128_, 1, v___x_4127_);
lean_ctor_set(v___x_4128_, 2, v___x_4127_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4129_, lean_object* v_s_4130_){
_start:
{
lean_object* v_res_4131_; 
v_res_4131_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4129_, v_s_4130_);
lean_dec_ref(v_x_4129_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4132_){
_start:
{
lean_object* v_newEntries_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4144_; 
v_newEntries_4133_ = lean_ctor_get(v_s_4132_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v_s_4132_);
if (v_isSharedCheck_4144_ == 0)
{
lean_object* v_unused_4145_; 
v_unused_4145_ = lean_ctor_get(v_s_4132_, 1);
lean_dec(v_unused_4145_);
v___x_4135_ = v_s_4132_;
v_isShared_4136_ = v_isSharedCheck_4144_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_newEntries_4133_);
lean_dec(v_s_4132_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4144_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4142_; 
v___x_4137_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4138_ = l_List_lengthTR___redArg(v_newEntries_4133_);
lean_dec(v_newEntries_4133_);
v___x_4139_ = l_Nat_reprFast(v___x_4138_);
v___x_4140_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4139_);
if (v_isShared_4136_ == 0)
{
lean_ctor_set_tag(v___x_4135_, 5);
lean_ctor_set(v___x_4135_, 1, v___x_4140_);
lean_ctor_set(v___x_4135_, 0, v___x_4137_);
v___x_4142_ = v___x_4135_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v___x_4137_);
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
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4146_){
_start:
{
lean_object* v_newEntries_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; 
v_newEntries_4147_ = lean_ctor_get(v_s_4146_, 0);
lean_inc(v_newEntries_4147_);
lean_dec_ref(v_s_4146_);
v___x_4148_ = l_List_reverse___redArg(v_newEntries_4147_);
v___x_4149_ = lean_array_mk(v___x_4148_);
return v___x_4149_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___f_4162_; lean_object* v___f_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4159_ = 0;
v___x_4160_ = lean_box(0);
v___x_4161_ = lean_box(2);
v___f_4162_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4163_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4164_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4165_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4166_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4167_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4168_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
lean_ctor_set(v___x_4168_, 1, v___x_4166_);
lean_ctor_set(v___x_4168_, 2, v___x_4165_);
lean_ctor_set(v___x_4168_, 3, v___x_4164_);
lean_ctor_set(v___x_4168_, 4, v___f_4163_);
lean_ctor_set(v___x_4168_, 5, v___f_4162_);
lean_ctor_set(v___x_4168_, 6, v___x_4161_);
lean_ctor_set(v___x_4168_, 7, v___x_4160_);
lean_ctor_set_uint8(v___x_4168_, sizeof(void*)*8, v___x_4159_);
lean_ctor_set_uint8(v___x_4168_, sizeof(void*)*8 + 1, v___x_4159_);
return v___x_4168_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___f_4169_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4170_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4170_);
lean_ctor_set(v___x_4171_, 1, v___f_4169_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4173_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4174_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4173_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4175_){
_start:
{
lean_object* v_res_4176_; 
v_res_4176_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4176_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4177_){
_start:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; uint8_t v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4179_ = l_Lean_attributeMapRef;
v___x_4180_ = lean_st_ref_get(v___x_4179_);
v___x_4181_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4180_, v_n_4177_);
lean_dec(v___x_4180_);
v___x_4182_ = lean_box(v___x_4181_);
v___x_4183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4182_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l_Lean_isBuiltinAttribute(v_n_4184_);
lean_dec(v_n_4184_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4187_, lean_object* v_x_4188_){
_start:
{
if (lean_obj_tag(v_x_4188_) == 0)
{
return v_x_4187_;
}
else
{
lean_object* v_key_4189_; lean_object* v_tail_4190_; lean_object* v___x_4191_; 
v_key_4189_ = lean_ctor_get(v_x_4188_, 0);
v_tail_4190_ = lean_ctor_get(v_x_4188_, 2);
lean_inc(v_key_4189_);
v___x_4191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4191_, 0, v_key_4189_);
lean_ctor_set(v___x_4191_, 1, v_x_4187_);
v_x_4187_ = v___x_4191_;
v_x_4188_ = v_tail_4190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4193_, lean_object* v_x_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4193_, v_x_4194_);
lean_dec(v_x_4194_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4196_, size_t v_i_4197_, size_t v_stop_4198_, lean_object* v_b_4199_){
_start:
{
uint8_t v___x_4200_; 
v___x_4200_ = lean_usize_dec_eq(v_i_4197_, v_stop_4198_);
if (v___x_4200_ == 0)
{
lean_object* v___x_4201_; lean_object* v___x_4202_; size_t v___x_4203_; size_t v___x_4204_; 
v___x_4201_ = lean_array_uget_borrowed(v_as_4196_, v_i_4197_);
v___x_4202_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4199_, v___x_4201_);
v___x_4203_ = ((size_t)1ULL);
v___x_4204_ = lean_usize_add(v_i_4197_, v___x_4203_);
v_i_4197_ = v___x_4204_;
v_b_4199_ = v___x_4202_;
goto _start;
}
else
{
return v_b_4199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4206_, lean_object* v_i_4207_, lean_object* v_stop_4208_, lean_object* v_b_4209_){
_start:
{
size_t v_i_boxed_4210_; size_t v_stop_boxed_4211_; lean_object* v_res_4212_; 
v_i_boxed_4210_ = lean_unbox_usize(v_i_4207_);
lean_dec(v_i_4207_);
v_stop_boxed_4211_ = lean_unbox_usize(v_stop_4208_);
lean_dec(v_stop_4208_);
v_res_4212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4206_, v_i_boxed_4210_, v_stop_boxed_4211_, v_b_4209_);
lean_dec_ref(v_as_4206_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v_buckets_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; uint8_t v___x_4220_; 
v___x_4214_ = l_Lean_attributeMapRef;
v___x_4215_ = lean_st_ref_get(v___x_4214_);
v_buckets_4216_ = lean_ctor_get(v___x_4215_, 1);
lean_inc_ref(v_buckets_4216_);
lean_dec(v___x_4215_);
v___x_4217_ = lean_box(0);
v___x_4218_ = lean_unsigned_to_nat(0u);
v___x_4219_ = lean_array_get_size(v_buckets_4216_);
v___x_4220_ = lean_nat_dec_lt(v___x_4218_, v___x_4219_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4221_; 
lean_dec_ref(v_buckets_4216_);
v___x_4221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4217_);
return v___x_4221_;
}
else
{
size_t v___x_4222_; size_t v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
v___x_4222_ = ((size_t)0ULL);
v___x_4223_ = lean_usize_of_nat(v___x_4219_);
v___x_4224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4216_, v___x_4222_, v___x_4223_, v___x_4217_);
lean_dec_ref(v_buckets_4216_);
v___x_4225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4225_, 0, v___x_4224_);
return v___x_4225_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l_Lean_getBuiltinAttributeNames();
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4229_){
_start:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
v___x_4231_ = l_Lean_attributeMapRef;
v___x_4232_ = lean_st_ref_get(v___x_4231_);
v___x_4233_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4232_, v_attrName_4229_);
lean_dec(v___x_4232_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v___x_4234_; uint8_t v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4234_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4235_ = 1;
v___x_4236_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4229_, v___x_4235_);
v___x_4237_ = lean_string_append(v___x_4234_, v___x_4236_);
lean_dec_ref(v___x_4236_);
v___x_4238_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4239_ = lean_string_append(v___x_4237_, v___x_4238_);
v___x_4240_ = lean_mk_io_user_error(v___x_4239_);
v___x_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4240_);
return v___x_4241_;
}
else
{
lean_object* v_val_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
lean_dec(v_attrName_4229_);
v_val_4242_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4244_ = v___x_4233_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_val_4242_);
lean_dec(v___x_4233_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
lean_ctor_set_tag(v___x_4244_, 0);
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_val_4242_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4250_, lean_object* v_a_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4250_);
return v_res_4252_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4253_, lean_object* v_attrName_4254_){
_start:
{
lean_object* v___x_4255_; lean_object* v_toEnvExtension_4256_; lean_object* v_asyncMode_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; uint8_t v___x_4260_; lean_object* v___x_4261_; lean_object* v_map_4262_; uint8_t v___x_4263_; 
v___x_4255_ = l_Lean_attributeExtension;
v_toEnvExtension_4256_ = lean_ctor_get(v___x_4255_, 0);
v_asyncMode_4257_ = lean_ctor_get(v_toEnvExtension_4256_, 2);
v___x_4258_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4259_ = lean_box(0);
v___x_4260_ = 0;
v___x_4261_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4258_, v___x_4255_, v_env_4253_, v_asyncMode_4257_, v___x_4259_, v___x_4260_);
v_map_4262_ = lean_ctor_get(v___x_4261_, 1);
lean_inc_ref(v_map_4262_);
lean_dec(v___x_4261_);
v___x_4263_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4262_, v_attrName_4254_);
lean_dec_ref(v_map_4262_);
return v___x_4263_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4264_, lean_object* v_attrName_4265_){
_start:
{
uint8_t v_res_4266_; lean_object* v_r_4267_; 
v_res_4266_ = l_Lean_isAttribute(v_env_4264_, v_attrName_4265_);
lean_dec(v_attrName_4265_);
v_r_4267_ = lean_box(v_res_4266_);
return v_r_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4268_){
_start:
{
lean_object* v___x_4269_; lean_object* v_toEnvExtension_4270_; lean_object* v_asyncMode_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; uint8_t v___x_4274_; lean_object* v___x_4275_; lean_object* v_map_4276_; lean_object* v_buckets_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; uint8_t v___x_4281_; 
v___x_4269_ = l_Lean_attributeExtension;
v_toEnvExtension_4270_ = lean_ctor_get(v___x_4269_, 0);
v_asyncMode_4271_ = lean_ctor_get(v_toEnvExtension_4270_, 2);
v___x_4272_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4273_ = lean_box(0);
v___x_4274_ = 0;
v___x_4275_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4272_, v___x_4269_, v_env_4268_, v_asyncMode_4271_, v___x_4273_, v___x_4274_);
v_map_4276_ = lean_ctor_get(v___x_4275_, 1);
lean_inc_ref(v_map_4276_);
lean_dec(v___x_4275_);
v_buckets_4277_ = lean_ctor_get(v_map_4276_, 1);
lean_inc_ref(v_buckets_4277_);
lean_dec_ref(v_map_4276_);
v___x_4278_ = lean_box(0);
v___x_4279_ = lean_unsigned_to_nat(0u);
v___x_4280_ = lean_array_get_size(v_buckets_4277_);
v___x_4281_ = lean_nat_dec_lt(v___x_4279_, v___x_4280_);
if (v___x_4281_ == 0)
{
lean_dec_ref(v_buckets_4277_);
return v___x_4278_;
}
else
{
size_t v___x_4282_; size_t v___x_4283_; lean_object* v___x_4284_; 
v___x_4282_ = ((size_t)0ULL);
v___x_4283_ = lean_usize_of_nat(v___x_4280_);
v___x_4284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4277_, v___x_4282_, v___x_4283_, v___x_4278_);
lean_dec_ref(v_buckets_4277_);
return v___x_4284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4285_, lean_object* v_attrName_4286_){
_start:
{
lean_object* v___x_4287_; lean_object* v_toEnvExtension_4288_; lean_object* v_asyncMode_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; uint8_t v___x_4292_; lean_object* v___x_4293_; lean_object* v_map_4294_; lean_object* v___x_4295_; 
v___x_4287_ = l_Lean_attributeExtension;
v_toEnvExtension_4288_ = lean_ctor_get(v___x_4287_, 0);
v_asyncMode_4289_ = lean_ctor_get(v_toEnvExtension_4288_, 2);
v___x_4290_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4291_ = lean_box(0);
v___x_4292_ = 0;
v___x_4293_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4290_, v___x_4287_, v_env_4285_, v_asyncMode_4289_, v___x_4291_, v___x_4292_);
v_map_4294_ = lean_ctor_get(v___x_4293_, 1);
lean_inc_ref(v_map_4294_);
lean_dec(v___x_4293_);
v___x_4295_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4294_, v_attrName_4286_);
lean_dec_ref(v_map_4294_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v___x_4296_; uint8_t v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4296_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4297_ = 1;
v___x_4298_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4286_, v___x_4297_);
v___x_4299_ = lean_string_append(v___x_4296_, v___x_4298_);
lean_dec_ref(v___x_4298_);
v___x_4300_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4301_ = lean_string_append(v___x_4299_, v___x_4300_);
v___x_4302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4301_);
return v___x_4302_;
}
else
{
lean_object* v_val_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4310_; 
lean_dec(v_attrName_4286_);
v_val_4303_ = lean_ctor_get(v___x_4295_, 0);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4305_ = v___x_4295_;
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_val_4303_);
lean_dec(v___x_4295_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4308_; 
if (v_isShared_4306_ == 0)
{
v___x_4308_ = v___x_4305_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_val_4303_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___lam__0(lean_object* v_addEntryFn_4311_, lean_object* v___x_4312_, lean_object* v_s_4313_){
_start:
{
lean_object* v_importedEntries_4314_; lean_object* v_state_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4323_; 
v_importedEntries_4314_ = lean_ctor_get(v_s_4313_, 0);
v_state_4315_ = lean_ctor_get(v_s_4313_, 1);
v_isSharedCheck_4323_ = !lean_is_exclusive(v_s_4313_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4317_ = v_s_4313_;
v_isShared_4318_ = v_isSharedCheck_4323_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_state_4315_);
lean_inc(v_importedEntries_4314_);
lean_dec(v_s_4313_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4323_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v_state_4319_; lean_object* v___x_4321_; 
v_state_4319_ = lean_apply_2(v_addEntryFn_4311_, v_state_4315_, v___x_4312_);
if (v_isShared_4318_ == 0)
{
lean_ctor_set(v___x_4317_, 1, v_state_4319_);
v___x_4321_ = v___x_4317_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_importedEntries_4314_);
lean_ctor_set(v_reuseFailAlloc_4322_, 1, v_state_4319_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4324_, lean_object* v_builderId_4325_, lean_object* v_ref_4326_, lean_object* v_args_4327_){
_start:
{
lean_object* v_entry_4329_; lean_object* v___x_4330_; 
v_entry_4329_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4329_, 0, v_builderId_4325_);
lean_ctor_set(v_entry_4329_, 1, v_ref_4326_);
lean_ctor_set(v_entry_4329_, 2, v_args_4327_);
lean_inc_ref(v_entry_4329_);
v___x_4330_ = l_Lean_mkAttributeImplOfEntry(v_entry_4329_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4365_; 
v_a_4331_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4333_ = v___x_4330_;
v_isShared_4334_ = v_isSharedCheck_4365_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4330_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4365_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v_toAttributeImplCore_4335_; lean_object* v_name_4336_; uint8_t v___x_4337_; 
v_toAttributeImplCore_4335_ = lean_ctor_get(v_a_4331_, 0);
v_name_4336_ = lean_ctor_get(v_toAttributeImplCore_4335_, 1);
lean_inc_ref(v_env_4324_);
v___x_4337_ = l_Lean_isAttribute(v_env_4324_, v_name_4336_);
if (v___x_4337_ == 0)
{
lean_object* v___x_4338_; lean_object* v_toEnvExtension_4339_; lean_object* v_addEntryFn_4340_; lean_object* v_asyncMode_4341_; uint8_t v_logWrites_4342_; lean_object* v___x_4343_; lean_object* v___f_4344_; lean_object* v___x_4345_; uint8_t v___x_4346_; 
v___x_4338_ = l_Lean_attributeExtension;
v_toEnvExtension_4339_ = lean_ctor_get(v___x_4338_, 0);
v_addEntryFn_4340_ = lean_ctor_get(v___x_4338_, 3);
v_asyncMode_4341_ = lean_ctor_get(v_toEnvExtension_4339_, 2);
v_logWrites_4342_ = lean_ctor_get_uint8(v_toEnvExtension_4339_, sizeof(void*)*6);
v___x_4343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4343_, 0, v_entry_4329_);
lean_ctor_set(v___x_4343_, 1, v_a_4331_);
lean_inc(v_addEntryFn_4340_);
v___f_4344_ = lean_alloc_closure((void*)(l_Lean_registerAttributeOfBuilder___lam__0), 3, 2);
lean_closure_set(v___f_4344_, 0, v_addEntryFn_4340_);
lean_closure_set(v___f_4344_, 1, v___x_4343_);
v___x_4345_ = lean_box(0);
v___x_4346_ = 1;
if (v_logWrites_4342_ == 0)
{
lean_object* v___x_4347_; lean_object* v___x_4349_; 
lean_inc_ref(v_toEnvExtension_4339_);
v___x_4347_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4339_, v_env_4324_, v___f_4344_, v_asyncMode_4341_, v___x_4345_, v___x_4346_);
if (v_isShared_4334_ == 0)
{
lean_ctor_set(v___x_4333_, 0, v___x_4347_);
v___x_4349_ = v___x_4333_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4347_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
else
{
lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4354_; 
lean_inc_ref_n(v_toEnvExtension_4339_, 2);
v___x_4351_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4339_, v_env_4324_);
lean_dec_ref(v_env_4324_);
v___x_4352_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4339_, v___x_4351_, v___f_4344_, v_asyncMode_4341_, v___x_4345_, v___x_4346_);
if (v_isShared_4334_ == 0)
{
lean_ctor_set(v___x_4333_, 0, v___x_4352_);
v___x_4354_ = v___x_4333_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v___x_4352_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
return v___x_4354_;
}
}
}
else
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4363_; 
lean_inc(v_name_4336_);
lean_dec(v_a_4331_);
lean_dec_ref_known(v_entry_4329_, 3);
lean_dec_ref(v_env_4324_);
v___x_4356_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4357_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4336_, v___x_4337_);
v___x_4358_ = lean_string_append(v___x_4356_, v___x_4357_);
lean_dec_ref(v___x_4357_);
v___x_4359_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4360_ = lean_string_append(v___x_4358_, v___x_4359_);
v___x_4361_ = lean_mk_io_user_error(v___x_4360_);
if (v_isShared_4334_ == 0)
{
lean_ctor_set_tag(v___x_4333_, 1);
lean_ctor_set(v___x_4333_, 0, v___x_4361_);
v___x_4363_ = v___x_4333_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v___x_4361_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
return v___x_4363_;
}
}
}
}
else
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4373_; 
lean_dec_ref_known(v_entry_4329_, 3);
lean_dec_ref(v_env_4324_);
v_a_4366_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4368_ = v___x_4330_;
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4330_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4371_; 
if (v_isShared_4369_ == 0)
{
v___x_4371_ = v___x_4368_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_a_4366_);
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
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4374_, lean_object* v_builderId_4375_, lean_object* v_ref_4376_, lean_object* v_args_4377_, lean_object* v_a_4378_){
_start:
{
lean_object* v_res_4379_; 
v_res_4379_ = l_Lean_registerAttributeOfBuilder(v_env_4374_, v_builderId_4375_, v_ref_4376_, v_args_4377_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
if (lean_obj_tag(v_x_4380_) == 0)
{
lean_object* v_a_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
v_a_4384_ = lean_ctor_get(v_x_4380_, 0);
lean_inc(v_a_4384_);
lean_dec_ref_known(v_x_4380_, 1);
v___x_4385_ = l_Lean_stringToMessageData(v_a_4384_);
v___x_4386_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4385_, v___y_4381_, v___y_4382_);
return v___x_4386_;
}
else
{
lean_object* v_a_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4394_; 
v_a_4387_ = lean_ctor_get(v_x_4380_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v_x_4380_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4389_ = v_x_4380_;
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_a_4387_);
lean_dec(v_x_4380_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___x_4392_; 
if (v_isShared_4390_ == 0)
{
lean_ctor_set_tag(v___x_4389_, 0);
v___x_4392_ = v___x_4389_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_a_4387_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
return v___x_4392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
lean_object* v_res_4399_; 
v_res_4399_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4395_, v___y_4396_, v___y_4397_);
lean_dec(v___y_4397_);
lean_dec_ref(v___y_4396_);
return v_res_4399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4400_, lean_object* v_attrName_4401_, lean_object* v_stx_4402_, uint8_t v_kind_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_){
_start:
{
lean_object* v___x_4407_; lean_object* v_env_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4407_ = lean_st_ref_get(v_a_4405_);
v_env_4408_ = lean_ctor_get(v___x_4407_, 0);
lean_inc_ref(v_env_4408_);
lean_dec(v___x_4407_);
v___x_4409_ = l_Lean_getAttributeImpl(v_env_4408_, v_attrName_4401_);
v___x_4410_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4409_, v_a_4404_, v_a_4405_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; lean_object* v_add_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref_known(v___x_4410_, 1);
v_add_4412_ = lean_ctor_get(v_a_4411_, 1);
lean_inc_ref(v_add_4412_);
lean_dec(v_a_4411_);
v___x_4413_ = lean_box(v_kind_4403_);
lean_inc(v_a_4405_);
lean_inc_ref(v_a_4404_);
v___x_4414_ = lean_apply_6(v_add_4412_, v_declName_4400_, v_stx_4402_, v___x_4413_, v_a_4404_, v_a_4405_, lean_box(0));
return v___x_4414_;
}
else
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
lean_dec(v_stx_4402_);
lean_dec(v_declName_4400_);
v_a_4415_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4417_ = v___x_4410_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4410_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4423_, lean_object* v_attrName_4424_, lean_object* v_stx_4425_, lean_object* v_kind_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_){
_start:
{
uint8_t v_kind_boxed_4430_; lean_object* v_res_4431_; 
v_kind_boxed_4430_ = lean_unbox(v_kind_4426_);
v_res_4431_ = l_Lean_Attribute_add(v_declName_4423_, v_attrName_4424_, v_stx_4425_, v_kind_boxed_4430_, v_a_4427_, v_a_4428_);
lean_dec(v_a_4428_);
lean_dec_ref(v_a_4427_);
return v_res_4431_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4432_, lean_object* v_x_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
lean_object* v___x_4437_; 
v___x_4437_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4433_, v___y_4434_, v___y_4435_);
return v___x_4437_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4438_, lean_object* v_x_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v_res_4443_; 
v_res_4443_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4438_, v_x_4439_, v___y_4440_, v___y_4441_);
lean_dec(v___y_4441_);
lean_dec_ref(v___y_4440_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4444_, lean_object* v_attrName_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_){
_start:
{
lean_object* v___x_4449_; lean_object* v_env_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
v___x_4449_ = lean_st_ref_get(v_a_4447_);
v_env_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc_ref(v_env_4450_);
lean_dec(v___x_4449_);
v___x_4451_ = l_Lean_getAttributeImpl(v_env_4450_, v_attrName_4445_);
v___x_4452_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4451_, v_a_4446_, v_a_4447_);
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_object* v_a_4453_; lean_object* v_erase_4454_; lean_object* v___x_4455_; 
v_a_4453_ = lean_ctor_get(v___x_4452_, 0);
lean_inc(v_a_4453_);
lean_dec_ref_known(v___x_4452_, 1);
v_erase_4454_ = lean_ctor_get(v_a_4453_, 2);
lean_inc_ref(v_erase_4454_);
lean_dec(v_a_4453_);
lean_inc(v_a_4447_);
lean_inc_ref(v_a_4446_);
v___x_4455_ = lean_apply_4(v_erase_4454_, v_declName_4444_, v_a_4446_, v_a_4447_, lean_box(0));
return v___x_4455_;
}
else
{
lean_object* v_a_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4463_; 
lean_dec(v_declName_4444_);
v_a_4456_ = lean_ctor_get(v___x_4452_, 0);
v_isSharedCheck_4463_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4458_ = v___x_4452_;
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_a_4456_);
lean_dec(v___x_4452_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4461_; 
if (v_isShared_4459_ == 0)
{
v___x_4461_ = v___x_4458_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v_a_4456_);
v___x_4461_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
return v___x_4461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4464_, lean_object* v_attrName_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_){
_start:
{
lean_object* v_res_4469_; 
v_res_4469_ = l_Lean_Attribute_erase(v_declName_4464_, v_attrName_4465_, v_a_4466_, v_a_4467_);
lean_dec(v_a_4467_);
lean_dec_ref(v_a_4466_);
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___lam__0(lean_object* v___y_4470_, lean_object* v_ps_4471_){
_start:
{
lean_object* v_importedEntries_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4479_; 
v_importedEntries_4472_ = lean_ctor_get(v_ps_4471_, 0);
v_isSharedCheck_4479_ = !lean_is_exclusive(v_ps_4471_);
if (v_isSharedCheck_4479_ == 0)
{
lean_object* v_unused_4480_; 
v_unused_4480_ = lean_ctor_get(v_ps_4471_, 1);
lean_dec(v_unused_4480_);
v___x_4474_ = v_ps_4471_;
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
else
{
lean_inc(v_importedEntries_4472_);
lean_dec(v_ps_4471_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v___x_4477_; 
if (v_isShared_4475_ == 0)
{
lean_ctor_set(v___x_4474_, 1, v___y_4470_);
v___x_4477_ = v___x_4474_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_importedEntries_4472_);
lean_ctor_set(v_reuseFailAlloc_4478_, 1, v___y_4470_);
v___x_4477_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
return v___x_4477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4481_, lean_object* v_x_4482_){
_start:
{
if (lean_obj_tag(v_x_4482_) == 0)
{
return v_x_4481_;
}
else
{
lean_object* v_key_4483_; lean_object* v_value_4484_; lean_object* v_tail_4485_; lean_object* v_newEntries_4486_; lean_object* v_map_4487_; uint8_t v___x_4488_; 
v_key_4483_ = lean_ctor_get(v_x_4482_, 0);
lean_inc(v_key_4483_);
v_value_4484_ = lean_ctor_get(v_x_4482_, 1);
lean_inc(v_value_4484_);
v_tail_4485_ = lean_ctor_get(v_x_4482_, 2);
lean_inc(v_tail_4485_);
lean_dec_ref_known(v_x_4482_, 3);
v_newEntries_4486_ = lean_ctor_get(v_x_4481_, 0);
v_map_4487_ = lean_ctor_get(v_x_4481_, 1);
v___x_4488_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4487_, v_key_4483_);
if (v___x_4488_ == 0)
{
lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4497_; 
lean_inc_ref(v_map_4487_);
lean_inc(v_newEntries_4486_);
v_isSharedCheck_4497_ = !lean_is_exclusive(v_x_4481_);
if (v_isSharedCheck_4497_ == 0)
{
lean_object* v_unused_4498_; lean_object* v_unused_4499_; 
v_unused_4498_ = lean_ctor_get(v_x_4481_, 1);
lean_dec(v_unused_4498_);
v_unused_4499_ = lean_ctor_get(v_x_4481_, 0);
lean_dec(v_unused_4499_);
v___x_4490_ = v_x_4481_;
v_isShared_4491_ = v_isSharedCheck_4497_;
goto v_resetjp_4489_;
}
else
{
lean_dec(v_x_4481_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4497_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4492_; lean_object* v___x_4494_; 
v___x_4492_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4487_, v_key_4483_, v_value_4484_);
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 1, v___x_4492_);
v___x_4494_ = v___x_4490_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_newEntries_4486_);
lean_ctor_set(v_reuseFailAlloc_4496_, 1, v___x_4492_);
v___x_4494_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
v_x_4481_ = v___x_4494_;
v_x_4482_ = v_tail_4485_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4484_);
lean_dec(v_key_4483_);
v_x_4482_ = v_tail_4485_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4501_, size_t v_i_4502_, size_t v_stop_4503_, lean_object* v_b_4504_){
_start:
{
uint8_t v___x_4505_; 
v___x_4505_ = lean_usize_dec_eq(v_i_4502_, v_stop_4503_);
if (v___x_4505_ == 0)
{
lean_object* v___x_4506_; lean_object* v___x_4507_; size_t v___x_4508_; size_t v___x_4509_; 
v___x_4506_ = lean_array_uget_borrowed(v_as_4501_, v_i_4502_);
lean_inc(v___x_4506_);
v___x_4507_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4504_, v___x_4506_);
v___x_4508_ = ((size_t)1ULL);
v___x_4509_ = lean_usize_add(v_i_4502_, v___x_4508_);
v_i_4502_ = v___x_4509_;
v_b_4504_ = v___x_4507_;
goto _start;
}
else
{
return v_b_4504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4511_, lean_object* v_i_4512_, lean_object* v_stop_4513_, lean_object* v_b_4514_){
_start:
{
size_t v_i_boxed_4515_; size_t v_stop_boxed_4516_; lean_object* v_res_4517_; 
v_i_boxed_4515_ = lean_unbox_usize(v_i_4512_);
lean_dec(v_i_4512_);
v_stop_boxed_4516_ = lean_unbox_usize(v_stop_4513_);
lean_dec(v_stop_4513_);
v_res_4517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4511_, v_i_boxed_4515_, v_stop_boxed_4516_, v_b_4514_);
lean_dec_ref(v_as_4511_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4518_){
_start:
{
lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v_toEnvExtension_4524_; lean_object* v_asyncMode_4525_; uint8_t v_logWrites_4526_; lean_object* v___y_4528_; lean_object* v_buckets_4537_; lean_object* v___x_4538_; uint8_t v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; uint8_t v___x_4543_; 
v___x_4520_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4521_ = l_Lean_attributeMapRef;
v___x_4522_ = lean_st_ref_get(v___x_4521_);
v___x_4523_ = l_Lean_attributeExtension;
v_toEnvExtension_4524_ = lean_ctor_get(v___x_4523_, 0);
v_asyncMode_4525_ = lean_ctor_get(v_toEnvExtension_4524_, 2);
v_logWrites_4526_ = lean_ctor_get_uint8(v_toEnvExtension_4524_, sizeof(void*)*6);
v_buckets_4537_ = lean_ctor_get(v___x_4522_, 1);
lean_inc_ref(v_buckets_4537_);
lean_dec(v___x_4522_);
v___x_4538_ = lean_box(0);
v___x_4539_ = 0;
lean_inc_ref(v_env_4518_);
v___x_4540_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4520_, v___x_4523_, v_env_4518_, v_asyncMode_4525_, v___x_4538_, v___x_4539_);
v___x_4541_ = lean_unsigned_to_nat(0u);
v___x_4542_ = lean_array_get_size(v_buckets_4537_);
v___x_4543_ = lean_nat_dec_lt(v___x_4541_, v___x_4542_);
if (v___x_4543_ == 0)
{
lean_dec_ref(v_buckets_4537_);
v___y_4528_ = v___x_4540_;
goto v___jp_4527_;
}
else
{
size_t v___x_4544_; size_t v___x_4545_; lean_object* v___x_4546_; 
v___x_4544_ = ((size_t)0ULL);
v___x_4545_ = lean_usize_of_nat(v___x_4542_);
v___x_4546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4537_, v___x_4544_, v___x_4545_, v___x_4540_);
lean_dec_ref(v_buckets_4537_);
v___y_4528_ = v___x_4546_;
goto v___jp_4527_;
}
v___jp_4527_:
{
lean_object* v___f_4529_; lean_object* v___x_4530_; uint8_t v___x_4531_; 
v___f_4529_ = lean_alloc_closure((void*)(l_Lean_updateEnvAttributesImpl___lam__0), 2, 1);
lean_closure_set(v___f_4529_, 0, v___y_4528_);
v___x_4530_ = lean_box(0);
v___x_4531_ = 1;
if (v_logWrites_4526_ == 0)
{
lean_object* v___x_4532_; lean_object* v___x_4533_; 
lean_inc_ref(v_toEnvExtension_4524_);
v___x_4532_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4524_, v_env_4518_, v___f_4529_, v_asyncMode_4525_, v___x_4530_, v___x_4531_);
v___x_4533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4533_, 0, v___x_4532_);
return v___x_4533_;
}
else
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
lean_inc_ref_n(v_toEnvExtension_4524_, 2);
v___x_4534_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4524_, v_env_4518_);
lean_dec_ref(v_env_4518_);
v___x_4535_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4524_, v___x_4534_, v___f_4529_, v_asyncMode_4525_, v___x_4530_, v___x_4531_);
v___x_4536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4535_);
return v___x_4536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4547_, lean_object* v_a_4548_){
_start:
{
lean_object* v_res_4549_; 
v_res_4549_ = lean_update_env_attributes(v_env_4547_);
return v_res_4549_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v_size_4553_; lean_object* v___x_4554_; 
v___x_4551_ = l_Lean_attributeMapRef;
v___x_4552_ = lean_st_ref_get(v___x_4551_);
v_size_4553_ = lean_ctor_get(v___x_4552_, 0);
lean_inc(v_size_4553_);
lean_dec(v___x_4552_);
v___x_4554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4554_, 0, v_size_4553_);
return v___x_4554_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = lean_get_num_attributes();
return v_res_4556_;
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
