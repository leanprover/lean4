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
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_1028__boxed_314_; lean_object* v_res_315_; 
v___y_1028__boxed_314_ = lean_unbox(v___y_310_);
v_res_315_ = l_Lean_instInhabitedAttributeImpl_default___lam__0(v_x_308_, v___y_309_, v___y_1028__boxed_314_, v___y_311_, v___y_312_);
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
lean_object* v_toCold_663_; lean_object* v_currRecDepth_664_; lean_object* v_ref_665_; uint16_t v_optionFlags_666_; uint8_t v_suppressElabErrors_667_; uint8_t v_isRecordingDeps_668_; lean_object* v_ref_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_toCold_663_ = lean_ctor_get(v___y_660_, 0);
v_currRecDepth_664_ = lean_ctor_get(v___y_660_, 1);
v_ref_665_ = lean_ctor_get(v___y_660_, 2);
v_optionFlags_666_ = lean_ctor_get_uint16(v___y_660_, sizeof(void*)*3);
v_suppressElabErrors_667_ = lean_ctor_get_uint8(v___y_660_, sizeof(void*)*3 + 2);
v_isRecordingDeps_668_ = lean_ctor_get_uint8(v___y_660_, sizeof(void*)*3 + 3);
v_ref_669_ = l_Lean_replaceRef(v_ref_658_, v_ref_665_);
lean_inc(v_currRecDepth_664_);
lean_inc_ref(v_toCold_663_);
v___x_670_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_670_, 0, v_toCold_663_);
lean_ctor_set(v___x_670_, 1, v_currRecDepth_664_);
lean_ctor_set(v___x_670_, 2, v_ref_669_);
lean_ctor_set_uint16(v___x_670_, sizeof(void*)*3, v_optionFlags_666_);
lean_ctor_set_uint8(v___x_670_, sizeof(void*)*3 + 2, v_suppressElabErrors_667_);
lean_ctor_set_uint8(v___x_670_, sizeof(void*)*3 + 3, v_isRecordingDeps_668_);
v___x_671_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_659_, v___x_670_, v___y_661_);
lean_dec_ref_known(v___x_670_, 3);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object* v_ref_672_, lean_object* v_msg_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_672_, v_msg_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v_ref_672_);
return v_res_677_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__3));
v___x_687_ = l_Lean_stringToMessageData(v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object* v_stx_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v___x_698_; uint8_t v___y_709_; lean_object* v___x_715_; uint8_t v___x_716_; 
lean_inc(v_stx_694_);
v___x_698_ = l_Lean_Syntax_getKind(v_stx_694_);
v___x_715_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_716_ = lean_name_eq(v___x_698_, v___x_715_);
if (v___x_716_ == 0)
{
v___y_709_ = v___x_716_;
goto v___jp_708_;
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_717_ = lean_unsigned_to_nat(1u);
v___x_718_ = l_Lean_Syntax_getArg(v_stx_694_, v___x_717_);
v___x_719_ = l_Lean_Syntax_isNone(v___x_718_);
lean_dec(v___x_718_);
v___y_709_ = v___x_719_;
goto v___jp_708_;
}
v___jp_699_:
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__2));
v___x_701_ = lean_name_eq(v___x_698_, v___x_700_);
lean_dec(v___x_698_);
if (v___x_701_ == 0)
{
if (lean_obj_tag(v_stx_694_) == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_box(0);
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
return v___x_703_;
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_obj_once(&l_Lean_Attribute_Builtin_ensureNoArgs___closed__4, &l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once, _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4);
v___x_705_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_694_, v___x_704_, v_a_695_, v_a_696_);
lean_dec(v_stx_694_);
return v___x_705_;
}
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; 
lean_dec(v_stx_694_);
v___x_706_ = lean_box(0);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
}
v___jp_708_:
{
if (v___y_709_ == 0)
{
goto v___jp_699_;
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_710_ = lean_unsigned_to_nat(2u);
v___x_711_ = l_Lean_Syntax_getArg(v_stx_694_, v___x_710_);
v___x_712_ = l_Lean_Syntax_isNone(v___x_711_);
lean_dec(v___x_711_);
if (v___x_712_ == 0)
{
goto v___jp_699_;
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; 
lean_dec(v___x_698_);
lean_dec(v_stx_694_);
v___x_713_ = lean_box(0);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
return v___x_714_;
}
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
if (v___x_768_ == 0)
{
lean_dec(v___x_776_);
goto v___jp_763_;
}
else
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
v_isModule_1185_ = lean_ctor_get_uint8(v___x_1184_, sizeof(void*)*7 + 4);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_1284_, uint8_t v___y_1285_, lean_object* v_x_1286_){
_start:
{
if (lean_obj_tag(v_x_1286_) == 1)
{
lean_object* v_pre_1287_; 
v_pre_1287_ = lean_ctor_get(v_x_1286_, 0);
switch(lean_obj_tag(v_pre_1287_))
{
case 1:
{
lean_object* v_pre_1288_; 
v_pre_1288_ = lean_ctor_get(v_pre_1287_, 0);
switch(lean_obj_tag(v_pre_1288_))
{
case 0:
{
lean_object* v_str_1289_; lean_object* v_str_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v_str_1289_ = lean_ctor_get(v_x_1286_, 1);
v_str_1290_ = lean_ctor_get(v_pre_1287_, 1);
v___x_1291_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1292_ = lean_string_dec_eq(v_str_1290_, v___x_1291_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1293_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1294_ = lean_string_dec_eq(v_str_1290_, v___x_1293_);
if (v___x_1294_ == 0)
{
return v___x_1294_;
}
else
{
lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1296_ = lean_string_dec_eq(v_str_1289_, v___x_1295_);
if (v___x_1296_ == 0)
{
return v___x_1296_;
}
else
{
return v_suppressElabErrors_1284_;
}
}
}
else
{
lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1298_ = lean_string_dec_eq(v_str_1289_, v___x_1297_);
if (v___x_1298_ == 0)
{
return v___x_1298_;
}
else
{
return v_suppressElabErrors_1284_;
}
}
}
case 1:
{
lean_object* v_pre_1299_; 
v_pre_1299_ = lean_ctor_get(v_pre_1288_, 0);
if (lean_obj_tag(v_pre_1299_) == 0)
{
lean_object* v_str_1300_; lean_object* v_str_1301_; lean_object* v_str_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v_str_1300_ = lean_ctor_get(v_x_1286_, 1);
v_str_1301_ = lean_ctor_get(v_pre_1287_, 1);
v_str_1302_ = lean_ctor_get(v_pre_1288_, 1);
v___x_1303_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1304_ = lean_string_dec_eq(v_str_1302_, v___x_1303_);
if (v___x_1304_ == 0)
{
return v___x_1304_;
}
else
{
lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1305_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1306_ = lean_string_dec_eq(v_str_1301_, v___x_1305_);
if (v___x_1306_ == 0)
{
return v___x_1306_;
}
else
{
lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1308_ = lean_string_dec_eq(v_str_1300_, v___x_1307_);
if (v___x_1308_ == 0)
{
return v___x_1308_;
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
return v___y_1285_;
}
}
default: 
{
return v___y_1285_;
}
}
}
case 0:
{
lean_object* v_str_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v_str_1309_ = lean_ctor_get(v_x_1286_, 1);
v___x_1310_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1311_ = lean_string_dec_eq(v_str_1309_, v___x_1310_);
if (v___x_1311_ == 0)
{
return v___x_1311_;
}
else
{
return v_suppressElabErrors_1284_;
}
}
default: 
{
return v___y_1285_;
}
}
}
else
{
return v___y_1285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_1312_, lean_object* v___y_1313_, lean_object* v_x_1314_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1315_; uint8_t v___y_5082__boxed_1316_; uint8_t v_res_1317_; lean_object* v_r_1318_; 
v_suppressElabErrors_boxed_1315_ = lean_unbox(v_suppressElabErrors_1312_);
v___y_5082__boxed_1316_ = lean_unbox(v___y_1313_);
v_res_1317_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_1315_, v___y_5082__boxed_1316_, v_x_1314_);
lean_dec(v_x_1314_);
v_r_1318_ = lean_box(v_res_1317_);
return v_r_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1319_, lean_object* v_msgData_1320_, uint8_t v_severity_1321_, uint8_t v_isSilent_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___y_1327_; lean_object* v___y_1328_; uint8_t v___y_1329_; lean_object* v___y_1330_; uint8_t v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v_toCold_1334_; lean_object* v___y_1335_; lean_object* v___y_1364_; lean_object* v___y_1365_; uint8_t v___y_1366_; lean_object* v___y_1367_; uint8_t v___y_1368_; lean_object* v___y_1369_; uint8_t v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1391_; lean_object* v___y_1392_; uint8_t v___y_1393_; uint8_t v___y_1394_; uint8_t v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; uint8_t v___y_1401_; uint8_t v___y_1402_; uint8_t v___y_1403_; uint8_t v___x_1414_; uint8_t v___y_1416_; uint8_t v___y_1417_; uint8_t v___y_1418_; uint8_t v___y_1420_; uint8_t v___x_1428_; 
v___x_1414_ = 2;
v___x_1428_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1321_, v___x_1414_);
if (v___x_1428_ == 0)
{
v___y_1420_ = v___x_1428_;
goto v___jp_1419_;
}
else
{
uint8_t v___x_1429_; 
lean_inc_ref(v_msgData_1320_);
v___x_1429_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1320_);
v___y_1420_ = v___x_1429_;
goto v___jp_1419_;
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
lean_ctor_set(v___x_1339_, 1, v___y_1328_);
lean_inc_ref(v___y_1327_);
lean_inc_ref(v___y_1330_);
v___x_1340_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1340_, 0, v___y_1330_);
lean_ctor_set(v___x_1340_, 1, v___y_1333_);
lean_ctor_set(v___x_1340_, 2, v___y_1332_);
lean_ctor_set(v___x_1340_, 3, v___y_1327_);
lean_ctor_set(v___x_1340_, 4, v___x_1339_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*5, v___y_1331_);
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
v_fileName_1372_ = lean_ctor_get(v___y_1369_, 0);
v_fileMap_1373_ = lean_ctor_get(v___y_1369_, 1);
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
v___x_1380_ = l_Lean_FileMap_toPosition(v_fileMap_1373_, v___y_1367_);
lean_dec(v___y_1367_);
v___x_1381_ = l_Lean_FileMap_toPosition(v_fileMap_1373_, v___y_1371_);
lean_dec(v___y_1371_);
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
v___x_1383_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1370_ == 0)
{
lean_del_object(v___x_1378_);
lean_dec_ref(v___y_1365_);
v___y_1327_ = v___x_1383_;
v___y_1328_ = v_a_1376_;
v___y_1329_ = v___y_1366_;
v___y_1330_ = v_fileName_1372_;
v___y_1331_ = v___y_1368_;
v___y_1332_ = v___x_1382_;
v___y_1333_ = v___x_1380_;
v_toCold_1334_ = v___y_1364_;
v___y_1335_ = v___y_1324_;
goto v___jp_1326_;
}
else
{
uint8_t v___x_1384_; 
lean_inc(v_a_1376_);
v___x_1384_ = l_Lean_MessageData_hasTag(v___y_1365_, v_a_1376_);
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
v___y_1328_ = v_a_1376_;
v___y_1329_ = v___y_1366_;
v___y_1330_ = v_fileName_1372_;
v___y_1331_ = v___y_1368_;
v___y_1332_ = v___x_1382_;
v___y_1333_ = v___x_1380_;
v_toCold_1334_ = v___y_1364_;
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
v___y_1366_ = v___y_1394_;
v___y_1367_ = v___y_1397_;
v___y_1368_ = v___y_1395_;
v___y_1369_ = v___y_1391_;
v___y_1370_ = v___y_1393_;
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
v___y_1366_ = v___y_1394_;
v___y_1367_ = v___y_1397_;
v___y_1368_ = v___y_1395_;
v___y_1369_ = v___y_1391_;
v___y_1370_ = v___y_1393_;
v___y_1371_ = v_val_1399_;
goto v___jp_1363_;
}
}
v___jp_1400_:
{
lean_object* v_toCold_1404_; lean_object* v_ref_1405_; uint8_t v_suppressElabErrors_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___f_1409_; lean_object* v_ref_1410_; lean_object* v___x_1411_; 
v_toCold_1404_ = lean_ctor_get(v___y_1323_, 0);
v_ref_1405_ = lean_ctor_get(v___y_1323_, 2);
v_suppressElabErrors_1406_ = lean_ctor_get_uint8(v___y_1323_, sizeof(void*)*3 + 2);
v___x_1407_ = lean_box(v_suppressElabErrors_1406_);
v___x_1408_ = lean_box(v___y_1401_);
v___f_1409_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1409_, 0, v___x_1407_);
lean_closure_set(v___f_1409_, 1, v___x_1408_);
v_ref_1410_ = l_Lean_replaceRef(v_ref_1319_, v_ref_1405_);
v___x_1411_ = l_Lean_Syntax_getPos_x3f(v_ref_1410_, v___y_1402_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v___x_1412_; 
v___x_1412_ = lean_unsigned_to_nat(0u);
v___y_1391_ = v_toCold_1404_;
v___y_1392_ = v___f_1409_;
v___y_1393_ = v_suppressElabErrors_1406_;
v___y_1394_ = v___y_1403_;
v___y_1395_ = v___y_1402_;
v___y_1396_ = v_ref_1410_;
v___y_1397_ = v___x_1412_;
goto v___jp_1390_;
}
else
{
lean_object* v_val_1413_; 
v_val_1413_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_val_1413_);
lean_dec_ref_known(v___x_1411_, 1);
v___y_1391_ = v_toCold_1404_;
v___y_1392_ = v___f_1409_;
v___y_1393_ = v_suppressElabErrors_1406_;
v___y_1394_ = v___y_1403_;
v___y_1395_ = v___y_1402_;
v___y_1396_ = v_ref_1410_;
v___y_1397_ = v_val_1413_;
goto v___jp_1390_;
}
}
v___jp_1415_:
{
if (v___y_1418_ == 0)
{
v___y_1401_ = v___y_1416_;
v___y_1402_ = v___y_1417_;
v___y_1403_ = v_severity_1321_;
goto v___jp_1400_;
}
else
{
v___y_1401_ = v___y_1416_;
v___y_1402_ = v___y_1417_;
v___y_1403_ = v___x_1414_;
goto v___jp_1400_;
}
}
v___jp_1419_:
{
if (v___y_1420_ == 0)
{
uint8_t v___x_1421_; uint8_t v___x_1422_; 
v___x_1421_ = 1;
v___x_1422_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1321_, v___x_1421_);
if (v___x_1422_ == 0)
{
v___y_1416_ = v___y_1420_;
v___y_1417_ = v___y_1420_;
v___y_1418_ = v___x_1422_;
goto v___jp_1415_;
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1423_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1323_);
v___x_1424_ = l_Lean_warningAsError;
v___x_1425_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v___x_1423_, v___x_1424_);
lean_dec_ref(v___x_1423_);
v___y_1416_ = v___y_1420_;
v___y_1417_ = v___y_1420_;
v___y_1418_ = v___x_1425_;
goto v___jp_1415_;
}
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec_ref(v_msgData_1320_);
v___x_1426_ = lean_box(0);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1430_, lean_object* v_msgData_1431_, lean_object* v_severity_1432_, lean_object* v_isSilent_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
uint8_t v_severity_boxed_1437_; uint8_t v_isSilent_boxed_1438_; lean_object* v_res_1439_; 
v_severity_boxed_1437_ = lean_unbox(v_severity_1432_);
v_isSilent_boxed_1438_ = lean_unbox(v_isSilent_1433_);
v_res_1439_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1430_, v_msgData_1431_, v_severity_boxed_1437_, v_isSilent_boxed_1438_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v_ref_1430_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1440_, uint8_t v_severity_1441_, uint8_t v_isSilent_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_ref_1446_; lean_object* v___x_1447_; 
v_ref_1446_ = lean_ctor_get(v___y_1443_, 2);
v___x_1447_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1446_, v_msgData_1440_, v_severity_1441_, v_isSilent_1442_, v___y_1443_, v___y_1444_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1448_, lean_object* v_severity_1449_, lean_object* v_isSilent_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
uint8_t v_severity_boxed_1454_; uint8_t v_isSilent_boxed_1455_; lean_object* v_res_1456_; 
v_severity_boxed_1454_ = lean_unbox(v_severity_1449_);
v_isSilent_boxed_1455_ = lean_unbox(v_isSilent_1450_);
v_res_1456_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1448_, v_severity_boxed_1454_, v_isSilent_boxed_1455_, v___y_1451_, v___y_1452_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
uint8_t v___x_1461_; uint8_t v___x_1462_; lean_object* v___x_1463_; 
v___x_1461_ = 1;
v___x_1462_ = 0;
v___x_1463_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1457_, v___x_1461_, v___x_1462_, v___y_1458_, v___y_1459_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1472_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1470_);
v___x_1473_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v___x_1472_, v_opt_1469_);
lean_dec_ref(v___x_1472_);
v___x_1474_ = lean_box(v___x_1473_);
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1476_, v___y_1477_);
lean_dec_ref(v___y_1477_);
lean_dec_ref(v_opt_1476_);
return v_res_1479_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1482_ = l_Lean_stringToMessageData(v___x_1481_);
return v___x_1482_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1485_ = l_Lean_stringToMessageData(v___x_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v___x_1490_; lean_object* v_env_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1513_; 
v___x_1490_ = lean_st_ref_get(v___y_1488_);
v_env_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc_ref(v_env_1491_);
lean_dec(v___x_1490_);
v___x_1492_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1493_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1492_, v___y_1487_);
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1513_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1513_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
uint8_t v_isExporting_1503_; 
v_isExporting_1503_ = lean_ctor_get_uint8(v_env_1491_, sizeof(void*)*13);
lean_dec_ref(v_env_1491_);
if (v_isExporting_1503_ == 0)
{
lean_dec(v_a_1494_);
lean_dec(v_id_1486_);
goto v___jp_1498_;
}
else
{
uint8_t v___x_1504_; 
v___x_1504_ = l_Lean_isPrivateName(v_id_1486_);
if (v___x_1504_ == 0)
{
lean_dec(v_a_1494_);
lean_dec(v_id_1486_);
goto v___jp_1498_;
}
else
{
uint8_t v___x_1505_; 
v___x_1505_ = lean_unbox(v_a_1494_);
lean_dec(v_a_1494_);
if (v___x_1505_ == 0)
{
lean_dec(v_id_1486_);
goto v___jp_1498_;
}
else
{
lean_object* v___x_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_del_object(v___x_1496_);
v___x_1506_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1507_ = 0;
v___x_1508_ = l_Lean_MessageData_ofConstName(v_id_1486_, v___x_1507_);
v___x_1509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1506_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1509_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1512_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1511_, v___y_1487_, v___y_1488_);
return v___x_1512_;
}
}
}
v___jp_1498_:
{
lean_object* v___x_1499_; lean_object* v___x_1501_; 
v___x_1499_ = lean_box(0);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1499_);
v___x_1501_ = v___x_1496_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
return v_res_1518_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1521_ = l_Lean_stringToMessageData(v___x_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1522_, uint8_t v_isModule_1523_, lean_object* v_attrName_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___x_1528_; 
lean_inc(v_declName_1522_);
v___x_1528_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1522_, v___y_1525_, v___y_1526_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v___x_1529_; lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1550_; 
lean_dec_ref_known(v___x_1528_, 1);
lean_inc(v_declName_1522_);
v___x_1529_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1522_, v_isModule_1523_, v___y_1526_);
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1550_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1550_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
uint8_t v___x_1534_; 
v___x_1534_ = lean_unbox(v_a_1530_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_del_object(v___x_1532_);
v___x_1535_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1536_ = l_Lean_MessageData_ofName(v_attrName_1524_);
v___x_1537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1535_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1537_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = lean_unbox(v_a_1530_);
lean_dec(v_a_1530_);
v___x_1541_ = l_Lean_MessageData_ofConstName(v_declName_1522_, v___x_1540_);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1539_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1544_, v___y_1525_, v___y_1526_);
return v___x_1545_;
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1548_; 
lean_dec(v_a_1530_);
lean_dec(v_attrName_1524_);
lean_dec(v_declName_1522_);
v___x_1546_ = lean_box(0);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v___x_1546_);
v___x_1548_ = v___x_1532_;
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
lean_dec(v_attrName_1524_);
lean_dec(v_declName_1522_);
return v___x_1528_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1551_, lean_object* v_isModule_1552_, lean_object* v_attrName_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
uint8_t v_isModule_boxed_1557_; lean_object* v_res_1558_; 
v_isModule_boxed_1557_ = lean_unbox(v_isModule_1552_);
v_res_1558_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1551_, v_isModule_boxed_1557_, v_attrName_1553_, v___y_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1559_, lean_object* v_declName_1560_, uint8_t v_attrKind_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v___x_1565_; lean_object* v_env_1569_; lean_object* v___x_1570_; uint8_t v_isModule_1571_; 
v___x_1565_ = lean_st_ref_get(v_a_1563_);
v_env_1569_ = lean_ctor_get(v___x_1565_, 0);
lean_inc_ref(v_env_1569_);
lean_dec(v___x_1565_);
v___x_1570_ = l_Lean_Environment_header(v_env_1569_);
lean_dec_ref(v_env_1569_);
v_isModule_1571_ = lean_ctor_get_uint8(v___x_1570_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1570_);
if (v_isModule_1571_ == 0)
{
lean_dec(v_declName_1560_);
lean_dec(v_attrName_1559_);
goto v___jp_1566_;
}
else
{
uint8_t v___x_1572_; uint8_t v___x_1573_; 
v___x_1572_ = 1;
v___x_1573_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1561_, v___x_1572_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v___f_1575_; lean_object* v___x_1576_; 
v___x_1574_ = lean_box(v_isModule_1571_);
v___f_1575_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1575_, 0, v_declName_1560_);
lean_closure_set(v___f_1575_, 1, v___x_1574_);
lean_closure_set(v___f_1575_, 2, v_attrName_1559_);
v___x_1576_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1575_, v_isModule_1571_, v_a_1562_, v_a_1563_);
return v___x_1576_;
}
else
{
lean_dec(v_declName_1560_);
lean_dec(v_attrName_1559_);
goto v___jp_1566_;
}
}
v___jp_1566_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = lean_box(0);
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
return v___x_1568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1577_, lean_object* v_declName_1578_, lean_object* v_attrKind_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
uint8_t v_attrKind_boxed_1583_; lean_object* v_res_1584_; 
v_attrKind_boxed_1583_ = lean_unbox(v_attrKind_1579_);
v_res_1584_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1577_, v_declName_1578_, v_attrKind_boxed_1583_, v_a_1580_, v_a_1581_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1585_, v___y_1586_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec_ref(v_opt_1590_);
return v_res_1594_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1597_ = l_Lean_stringToMessageData(v___x_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1598_, lean_object* v_declName_1599_, uint8_t v_attrKind_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v___x_1604_; lean_object* v_env_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; uint8_t v_isModule_1608_; 
v___x_1604_ = lean_st_ref_get(v_a_1602_);
v_env_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc_ref(v_env_1605_);
lean_dec(v___x_1604_);
v___x_1606_ = lean_st_ref_get(v_a_1602_);
v___x_1607_ = l_Lean_Environment_header(v_env_1605_);
lean_dec_ref(v_env_1605_);
v_isModule_1608_ = lean_ctor_get_uint8(v___x_1607_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1607_);
if (v_isModule_1608_ == 0)
{
lean_object* v___x_1609_; 
lean_dec(v___x_1606_);
v___x_1609_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1598_, v_declName_1599_, v_attrKind_1600_, v_a_1601_, v_a_1602_);
return v___x_1609_;
}
else
{
lean_object* v_env_1610_; uint8_t v___x_1611_; 
v_env_1610_ = lean_ctor_get(v___x_1606_, 0);
lean_inc_ref(v_env_1610_);
lean_dec(v___x_1606_);
lean_inc(v_declName_1599_);
v___x_1611_ = l_Lean_isMarkedMeta(v_env_1610_, v_declName_1599_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1612_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1613_ = l_Lean_MessageData_ofName(v_attrName_1598_);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = l_Lean_MessageData_ofConstName(v_declName_1599_, v___x_1611_);
v___x_1618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1616_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1618_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1620_, v_a_1601_, v_a_1602_);
return v___x_1621_;
}
else
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1598_, v_declName_1599_, v_attrKind_1600_, v_a_1601_, v_a_1602_);
return v___x_1622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1623_, lean_object* v_declName_1624_, lean_object* v_attrKind_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_){
_start:
{
uint8_t v_attrKind_boxed_1629_; lean_object* v_res_1630_; 
v_attrKind_boxed_1629_ = lean_unbox(v_attrKind_1625_);
v_res_1630_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1623_, v_declName_1624_, v_attrKind_boxed_1629_, v_a_1626_, v_a_1627_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1639_, v___y_1640_);
lean_dec_ref(v___y_1640_);
lean_dec_ref(v_x_1639_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1643_, lean_object* v_x_1644_){
_start:
{
lean_inc(v_s_1643_);
return v_s_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1645_, lean_object* v_x_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1645_, v_x_1646_);
lean_dec(v_x_1646_);
lean_dec(v_s_1645_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1652_, lean_object* v_x_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1655_, lean_object* v_x_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1655_, v_x_1656_);
lean_dec(v_x_1656_);
lean_dec_ref(v_x_1655_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_box(0);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1660_);
lean_dec(v_x_1660_);
return v_res_1661_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_1666_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1667_; lean_object* v___f_1668_; lean_object* v___f_1669_; lean_object* v___f_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___f_1667_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1668_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1669_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1670_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1671_ = lean_box(0);
v___x_1672_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1673_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
lean_ctor_set(v___x_1673_, 1, v___x_1671_);
lean_ctor_set(v___x_1673_, 2, v___f_1670_);
lean_ctor_set(v___x_1673_, 3, v___f_1669_);
lean_ctor_set(v___x_1673_, 4, v___f_1668_);
lean_ctor_set(v___x_1673_, 5, v___f_1667_);
return v___x_1673_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1675_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1675_);
lean_ctor_set(v___x_1676_, 1, v___x_1674_);
return v___x_1676_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1677_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1678_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_registerTagAttribute___lam__0(v_x_1682_);
lean_dec(v_x_1682_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1684_, lean_object* v_x_1685_, lean_object* v_x_1686_){
_start:
{
if (lean_obj_tag(v_x_1686_) == 0)
{
return v_x_1685_;
}
else
{
lean_object* v_head_1687_; lean_object* v_tail_1688_; uint8_t v___x_1689_; 
v_head_1687_ = lean_ctor_get(v_x_1686_, 0);
lean_inc(v_head_1687_);
v_tail_1688_ = lean_ctor_get(v_x_1686_, 1);
lean_inc(v_tail_1688_);
lean_dec_ref_known(v_x_1686_, 2);
v___x_1689_ = l_Lean_NameSet_contains(v_newState_1684_, v_head_1687_);
if (v___x_1689_ == 0)
{
lean_dec(v_head_1687_);
v_x_1686_ = v_tail_1688_;
goto _start;
}
else
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Lean_NameSet_insert(v_x_1685_, v_head_1687_);
v_x_1685_ = v___x_1691_;
v_x_1686_ = v_tail_1688_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1693_, lean_object* v_x_1694_, lean_object* v_x_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1693_, v_x_1694_, v_x_1695_);
lean_dec(v_newState_1693_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1697_, lean_object* v_newState_1698_, lean_object* v_newConsts_1699_, lean_object* v_s_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1698_, v_s_1700_, v_newConsts_1699_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1702_, lean_object* v_newState_1703_, lean_object* v_newConsts_1704_, lean_object* v_s_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_registerTagAttribute___lam__1(v_x_1702_, v_newState_1703_, v_newConsts_1704_, v_s_1705_);
lean_dec(v_newState_1703_);
lean_dec(v_x_1702_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1719_){
_start:
{
lean_object* v___x_1720_; lean_object* v___y_1722_; 
v___x_1720_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1719_) == 0)
{
lean_object* v_size_1726_; 
v_size_1726_ = lean_ctor_get(v_s_1719_, 0);
lean_inc(v_size_1726_);
lean_dec_ref_known(v_s_1719_, 5);
v___y_1722_ = v_size_1726_;
goto v___jp_1721_;
}
else
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_unsigned_to_nat(0u);
v___y_1722_ = v___x_1727_;
goto v___jp_1721_;
}
v___jp_1721_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1723_ = l_Nat_reprFast(v___y_1722_);
v___x_1724_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
v___x_1725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1720_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
return v___x_1725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1728_, lean_object* v_pivot_1729_, lean_object* v_as_1730_, lean_object* v_i_1731_, lean_object* v_k_1732_){
_start:
{
uint8_t v___x_1733_; 
v___x_1733_ = lean_nat_dec_lt(v_k_1732_, v_hi_1728_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
lean_dec(v_k_1732_);
v___x_1734_ = lean_array_fswap(v_as_1730_, v_i_1731_, v_hi_1728_);
v___x_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1735_, 0, v_i_1731_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
return v___x_1735_;
}
else
{
lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1736_ = lean_array_fget_borrowed(v_as_1730_, v_k_1732_);
v___x_1737_ = l_Lean_Name_quickLt(v___x_1736_, v_pivot_1729_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = lean_unsigned_to_nat(1u);
v___x_1739_ = lean_nat_add(v_k_1732_, v___x_1738_);
lean_dec(v_k_1732_);
v_k_1732_ = v___x_1739_;
goto _start;
}
else
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1741_ = lean_array_fswap(v_as_1730_, v_i_1731_, v_k_1732_);
v___x_1742_ = lean_unsigned_to_nat(1u);
v___x_1743_ = lean_nat_add(v_i_1731_, v___x_1742_);
lean_dec(v_i_1731_);
v___x_1744_ = lean_nat_add(v_k_1732_, v___x_1742_);
lean_dec(v_k_1732_);
v_as_1730_ = v___x_1741_;
v_i_1731_ = v___x_1743_;
v_k_1732_ = v___x_1744_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1746_, lean_object* v_pivot_1747_, lean_object* v_as_1748_, lean_object* v_i_1749_, lean_object* v_k_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1746_, v_pivot_1747_, v_as_1748_, v_i_1749_, v_k_1750_);
lean_dec(v_pivot_1747_);
lean_dec(v_hi_1746_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1752_, lean_object* v_as_1753_, lean_object* v_lo_1754_, lean_object* v_hi_1755_){
_start:
{
lean_object* v___y_1757_; uint8_t v___x_1767_; 
v___x_1767_ = lean_nat_dec_lt(v_lo_1754_, v_hi_1755_);
if (v___x_1767_ == 0)
{
lean_dec(v_lo_1754_);
return v_as_1753_;
}
else
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v_mid_1770_; lean_object* v___y_1772_; lean_object* v___y_1778_; lean_object* v___x_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1768_ = lean_nat_add(v_lo_1754_, v_hi_1755_);
v___x_1769_ = lean_unsigned_to_nat(1u);
v_mid_1770_ = lean_nat_shiftr(v___x_1768_, v___x_1769_);
lean_dec(v___x_1768_);
v___x_1783_ = lean_array_fget_borrowed(v_as_1753_, v_mid_1770_);
v___x_1784_ = lean_array_fget_borrowed(v_as_1753_, v_lo_1754_);
v___x_1785_ = l_Lean_Name_quickLt(v___x_1783_, v___x_1784_);
if (v___x_1785_ == 0)
{
v___y_1778_ = v_as_1753_;
goto v___jp_1777_;
}
else
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_array_fswap(v_as_1753_, v_lo_1754_, v_mid_1770_);
v___y_1778_ = v___x_1786_;
goto v___jp_1777_;
}
v___jp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v___x_1773_ = lean_array_fget_borrowed(v___y_1772_, v_mid_1770_);
v___x_1774_ = lean_array_fget_borrowed(v___y_1772_, v_hi_1755_);
v___x_1775_ = l_Lean_Name_quickLt(v___x_1773_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_dec(v_mid_1770_);
v___y_1757_ = v___y_1772_;
goto v___jp_1756_;
}
else
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_array_fswap(v___y_1772_, v_mid_1770_, v_hi_1755_);
lean_dec(v_mid_1770_);
v___y_1757_ = v___x_1776_;
goto v___jp_1756_;
}
}
v___jp_1777_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1779_ = lean_array_fget_borrowed(v___y_1778_, v_hi_1755_);
v___x_1780_ = lean_array_fget_borrowed(v___y_1778_, v_lo_1754_);
v___x_1781_ = l_Lean_Name_quickLt(v___x_1779_, v___x_1780_);
if (v___x_1781_ == 0)
{
v___y_1772_ = v___y_1778_;
goto v___jp_1771_;
}
else
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_array_fswap(v___y_1778_, v_lo_1754_, v_hi_1755_);
v___y_1772_ = v___x_1782_;
goto v___jp_1771_;
}
}
}
v___jp_1756_:
{
lean_object* v_pivot_1758_; lean_object* v___x_1759_; lean_object* v_fst_1760_; lean_object* v_snd_1761_; uint8_t v___x_1762_; 
v_pivot_1758_ = lean_array_fget(v___y_1757_, v_hi_1755_);
lean_inc_n(v_lo_1754_, 2);
v___x_1759_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1755_, v_pivot_1758_, v___y_1757_, v_lo_1754_, v_lo_1754_);
lean_dec(v_pivot_1758_);
v_fst_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_fst_1760_);
v_snd_1761_ = lean_ctor_get(v___x_1759_, 1);
lean_inc(v_snd_1761_);
lean_dec_ref(v___x_1759_);
v___x_1762_ = lean_nat_dec_le(v_hi_1755_, v_fst_1760_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1752_, v_snd_1761_, v_lo_1754_, v_fst_1760_);
v___x_1764_ = lean_unsigned_to_nat(1u);
v___x_1765_ = lean_nat_add(v_fst_1760_, v___x_1764_);
lean_dec(v_fst_1760_);
v_as_1753_ = v___x_1763_;
v_lo_1754_ = v___x_1765_;
goto _start;
}
else
{
lean_dec(v_fst_1760_);
lean_dec(v_lo_1754_);
return v_snd_1761_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1787_, lean_object* v_as_1788_, lean_object* v_lo_1789_, lean_object* v_hi_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1787_, v_as_1788_, v_lo_1789_, v_hi_1790_);
lean_dec(v_hi_1790_);
lean_dec(v_n_1787_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1792_, lean_object* v_as_1793_, size_t v_i_1794_, size_t v_stop_1795_, lean_object* v_b_1796_){
_start:
{
lean_object* v___y_1798_; uint8_t v___x_1802_; 
v___x_1802_ = lean_usize_dec_eq(v_i_1794_, v_stop_1795_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; uint8_t v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1803_ = lean_array_uget_borrowed(v_as_1793_, v_i_1794_);
v___x_1804_ = 1;
lean_inc_ref(v_env_1792_);
v___x_1805_ = l_Lean_Environment_setExporting(v_env_1792_, v___x_1804_);
lean_inc(v___x_1803_);
v___x_1806_ = l_Lean_Environment_contains(v___x_1805_, v___x_1803_, v___x_1802_);
if (v___x_1806_ == 0)
{
v___y_1798_ = v_b_1796_;
goto v___jp_1797_;
}
else
{
lean_object* v___x_1807_; 
lean_inc(v___x_1803_);
v___x_1807_ = lean_array_push(v_b_1796_, v___x_1803_);
v___y_1798_ = v___x_1807_;
goto v___jp_1797_;
}
}
else
{
lean_dec_ref(v_env_1792_);
return v_b_1796_;
}
v___jp_1797_:
{
size_t v___x_1799_; size_t v___x_1800_; 
v___x_1799_ = ((size_t)1ULL);
v___x_1800_ = lean_usize_add(v_i_1794_, v___x_1799_);
v_i_1794_ = v___x_1800_;
v_b_1796_ = v___y_1798_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1808_, lean_object* v_as_1809_, lean_object* v_i_1810_, lean_object* v_stop_1811_, lean_object* v_b_1812_){
_start:
{
size_t v_i_boxed_1813_; size_t v_stop_boxed_1814_; lean_object* v_res_1815_; 
v_i_boxed_1813_ = lean_unbox_usize(v_i_1810_);
lean_dec(v_i_1810_);
v_stop_boxed_1814_ = lean_unbox_usize(v_stop_1811_);
lean_dec(v_stop_1811_);
v_res_1815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1808_, v_as_1809_, v_i_boxed_1813_, v_stop_boxed_1814_, v_b_1812_);
lean_dec_ref(v_as_1809_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1816_, lean_object* v_x_1817_){
_start:
{
if (lean_obj_tag(v_x_1817_) == 0)
{
lean_object* v_k_1818_; lean_object* v_l_1819_; lean_object* v_r_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v_k_1818_ = lean_ctor_get(v_x_1817_, 1);
lean_inc(v_k_1818_);
v_l_1819_ = lean_ctor_get(v_x_1817_, 3);
lean_inc(v_l_1819_);
v_r_1820_ = lean_ctor_get(v_x_1817_, 4);
lean_inc(v_r_1820_);
lean_dec_ref_known(v_x_1817_, 5);
v___x_1821_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1816_, v_l_1819_);
v___x_1822_ = lean_array_push(v___x_1821_, v_k_1818_);
v_init_1816_ = v___x_1822_;
v_x_1817_ = v_r_1820_;
goto _start;
}
else
{
return v_init_1816_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1824_, lean_object* v_es_1825_){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___y_1829_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___y_1846_; lean_object* v___y_1847_; uint8_t v___x_1849_; 
v___x_1826_ = lean_unsigned_to_nat(0u);
v___x_1827_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1843_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1827_, v_es_1825_);
v___x_1844_ = lean_array_get_size(v___x_1843_);
v___x_1849_ = lean_nat_dec_eq(v___x_1844_, v___x_1826_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___y_1853_; uint8_t v___x_1855_; 
v___x_1850_ = lean_unsigned_to_nat(1u);
v___x_1851_ = lean_nat_sub(v___x_1844_, v___x_1850_);
v___x_1855_ = lean_nat_dec_le(v___x_1826_, v___x_1851_);
if (v___x_1855_ == 0)
{
lean_inc(v___x_1851_);
v___y_1853_ = v___x_1851_;
goto v___jp_1852_;
}
else
{
v___y_1853_ = v___x_1826_;
goto v___jp_1852_;
}
v___jp_1852_:
{
uint8_t v___x_1854_; 
v___x_1854_ = lean_nat_dec_le(v___y_1853_, v___x_1851_);
if (v___x_1854_ == 0)
{
lean_dec(v___x_1851_);
lean_inc(v___y_1853_);
v___y_1846_ = v___y_1853_;
v___y_1847_ = v___y_1853_;
goto v___jp_1845_;
}
else
{
v___y_1846_ = v___y_1853_;
v___y_1847_ = v___x_1851_;
goto v___jp_1845_;
}
}
}
else
{
v___y_1829_ = v___x_1843_;
goto v___jp_1828_;
}
v___jp_1828_:
{
lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1830_ = lean_array_get_size(v___y_1829_);
v___x_1831_ = lean_nat_dec_lt(v___x_1826_, v___x_1830_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; 
lean_dec_ref(v_env_1824_);
v___x_1832_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1827_);
lean_ctor_set(v___x_1832_, 1, v___x_1827_);
lean_ctor_set(v___x_1832_, 2, v___y_1829_);
return v___x_1832_;
}
else
{
uint8_t v___x_1833_; 
v___x_1833_ = lean_nat_dec_le(v___x_1830_, v___x_1830_);
if (v___x_1833_ == 0)
{
if (v___x_1831_ == 0)
{
lean_object* v___x_1834_; 
lean_dec_ref(v_env_1824_);
v___x_1834_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1827_);
lean_ctor_set(v___x_1834_, 1, v___x_1827_);
lean_ctor_set(v___x_1834_, 2, v___y_1829_);
return v___x_1834_;
}
else
{
size_t v___x_1835_; size_t v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1835_ = ((size_t)0ULL);
v___x_1836_ = lean_usize_of_nat(v___x_1830_);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1824_, v___y_1829_, v___x_1835_, v___x_1836_, v___x_1827_);
lean_inc_ref(v___x_1837_);
v___x_1838_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
lean_ctor_set(v___x_1838_, 2, v___y_1829_);
return v___x_1838_;
}
}
else
{
size_t v___x_1839_; size_t v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1839_ = ((size_t)0ULL);
v___x_1840_ = lean_usize_of_nat(v___x_1830_);
v___x_1841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1824_, v___y_1829_, v___x_1839_, v___x_1840_, v___x_1827_);
lean_inc_ref(v___x_1841_);
v___x_1842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
lean_ctor_set(v___x_1842_, 2, v___y_1829_);
return v___x_1842_;
}
}
}
v___jp_1845_:
{
lean_object* v___x_1848_; 
v___x_1848_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1844_, v___x_1843_, v___y_1846_, v___y_1847_);
lean_dec(v___y_1847_);
v___y_1829_ = v___x_1848_;
goto v___jp_1828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v_name_1856_, lean_object* v_decl_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1861_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1862_ = l_Lean_MessageData_ofName(v_name_1856_);
v___x_1863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1861_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1863_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1865_, v___y_1858_, v___y_1859_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v_name_1867_, lean_object* v_decl_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_registerTagAttribute___lam__4(v_name_1867_, v_decl_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v_decl_1868_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1873_, lean_object* v_x_1874_, lean_object* v_x_1875_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1873_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_registerTagAttribute___lam__5(v___x_1878_, v_x_1879_, v_x_1880_);
lean_dec_ref(v_x_1880_);
lean_dec_ref(v_x_1879_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v___x_1883_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1883_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v___x_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_registerTagAttribute___lam__6(v___x_1886_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_a_1889_, lean_object* v_decl_1890_, lean_object* v_s_1891_){
_start:
{
lean_object* v_addEntryFn_1892_; lean_object* v_importedEntries_1893_; lean_object* v_state_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1902_; 
v_addEntryFn_1892_ = lean_ctor_get(v_a_1889_, 3);
lean_inc(v_addEntryFn_1892_);
lean_dec_ref(v_a_1889_);
v_importedEntries_1893_ = lean_ctor_get(v_s_1891_, 0);
v_state_1894_ = lean_ctor_get(v_s_1891_, 1);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_s_1891_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1896_ = v_s_1891_;
v_isShared_1897_ = v_isSharedCheck_1902_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_state_1894_);
lean_inc(v_importedEntries_1893_);
lean_dec(v_s_1891_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1902_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v_state_1898_; lean_object* v___x_1900_; 
v_state_1898_ = lean_apply_2(v_addEntryFn_1892_, v_state_1894_, v_decl_1890_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 1, v_state_1898_);
v___x_1900_ = v___x_1896_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_importedEntries_1893_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_state_1898_);
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
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1903_, lean_object* v_declName_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1908_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1909_ = l_Lean_MessageData_ofName(v_attrName_1903_);
v___x_1910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1908_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1910_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = 0;
v___x_1914_ = l_Lean_MessageData_ofConstName(v_declName_1904_, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1912_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1917_, v___y_1905_, v___y_1906_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1919_, lean_object* v_declName_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1919_, v_declName_1920_, v___y_1921_, v___y_1922_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1925_, lean_object* v_declName_1926_, lean_object* v_asyncPrefix_x3f_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___y_1932_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1927_) == 0)
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_MessageData_nil;
v___y_1932_ = v___x_1945_;
goto v___jp_1931_;
}
else
{
lean_object* v_val_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v_val_1946_ = lean_ctor_get(v_asyncPrefix_x3f_1927_, 0);
lean_inc(v_val_1946_);
lean_dec_ref_known(v_asyncPrefix_x3f_1927_, 1);
v___x_1947_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1948_ = l_Lean_MessageData_ofName(v_val_1946_);
v___x_1949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___y_1932_ = v___x_1951_;
goto v___jp_1931_;
}
v___jp_1931_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1933_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1934_ = l_Lean_MessageData_ofName(v_attrName_1925_);
v___x_1935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1933_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1935_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = 0;
v___x_1939_ = l_Lean_MessageData_ofConstName(v_declName_1926_, v___x_1938_);
v___x_1940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1937_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1940_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
lean_ctor_set(v___x_1943_, 1, v___y_1932_);
v___x_1944_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1943_, v___y_1928_, v___y_1929_);
return v___x_1944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1952_, lean_object* v_declName_1953_, lean_object* v_asyncPrefix_x3f_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1952_, v_declName_1953_, v_asyncPrefix_x3f_1954_, v___y_1955_, v___y_1956_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1959_, uint8_t v_kind_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___y_1970_; 
v___x_1964_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1965_ = l_Lean_MessageData_ofName(v_name_1959_);
v___x_1966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1964_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1966_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
switch(v_kind_1960_)
{
case 0:
{
lean_object* v___x_1977_; 
v___x_1977_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1970_ = v___x_1977_;
goto v___jp_1969_;
}
case 1:
{
lean_object* v___x_1978_; 
v___x_1978_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1970_ = v___x_1978_;
goto v___jp_1969_;
}
default: 
{
lean_object* v___x_1979_; 
v___x_1979_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1970_ = v___x_1979_;
goto v___jp_1969_;
}
}
v___jp_1969_:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
lean_inc_ref(v___y_1970_);
v___x_1971_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1971_, 0, v___y_1970_);
v___x_1972_ = l_Lean_MessageData_ofFormat(v___x_1971_);
v___x_1973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1968_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
v___x_1974_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1973_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1975_, v___y_1961_, v___y_1962_);
return v___x_1976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_1980_, lean_object* v_kind_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
uint8_t v_kind_boxed_1985_; lean_object* v_res_1986_; 
v_kind_boxed_1985_ = lean_unbox(v_kind_1981_);
v_res_1986_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1980_, v_kind_boxed_1985_, v___y_1982_, v___y_1983_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__8(lean_object* v_a_1987_, lean_object* v_validate_1988_, lean_object* v_name_1989_, lean_object* v_decl_1990_, lean_object* v_stx_1991_, uint8_t v_kind_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v_nextMacroScope_1999_; lean_object* v_ngen_2000_; lean_object* v_auxDeclNGen_2001_; lean_object* v_traceState_2002_; lean_object* v_recordedDeps_2003_; lean_object* v_messages_2004_; lean_object* v_infoState_2005_; lean_object* v_snapshotTasks_2006_; lean_object* v___y_2007_; lean_object* v___f_2012_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___x_2049_; 
lean_inc(v_decl_1990_);
lean_inc_ref(v_a_1987_);
v___f_2012_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7), 3, 2);
lean_closure_set(v___f_2012_, 0, v_a_1987_);
lean_closure_set(v___f_2012_, 1, v_decl_1990_);
v___x_2049_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1991_, v___y_1993_, v___y_1994_);
if (lean_obj_tag(v___x_2049_) == 0)
{
uint8_t v___x_2050_; uint8_t v___x_2051_; 
lean_dec_ref_known(v___x_2049_, 1);
v___x_2050_ = 0;
v___x_2051_ = l_Lean_instBEqAttributeKind_beq(v_kind_1992_, v___x_2050_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; 
lean_dec_ref(v___f_2012_);
lean_dec(v_decl_1990_);
lean_dec_ref(v_validate_1988_);
lean_dec_ref(v_a_1987_);
v___x_2052_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1989_, v_kind_1992_, v___y_1993_, v___y_1994_);
return v___x_2052_;
}
else
{
goto v___jp_2044_;
}
}
else
{
lean_dec_ref(v___f_2012_);
lean_dec(v_decl_1990_);
lean_dec(v_name_1989_);
lean_dec_ref(v_validate_1988_);
lean_dec_ref(v_a_1987_);
return v___x_2049_;
}
v___jp_1996_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2008_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_2009_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2009_, 0, v___y_2007_);
lean_ctor_set(v___x_2009_, 1, v_nextMacroScope_1999_);
lean_ctor_set(v___x_2009_, 2, v_ngen_2000_);
lean_ctor_set(v___x_2009_, 3, v_auxDeclNGen_2001_);
lean_ctor_set(v___x_2009_, 4, v_traceState_2002_);
lean_ctor_set(v___x_2009_, 5, v___x_2008_);
lean_ctor_set(v___x_2009_, 6, v_recordedDeps_2003_);
lean_ctor_set(v___x_2009_, 7, v_messages_2004_);
lean_ctor_set(v___x_2009_, 8, v_infoState_2005_);
lean_ctor_set(v___x_2009_, 9, v_snapshotTasks_2006_);
v___x_2010_ = lean_st_ref_put(v___y_1997_, v___x_2009_);
v___x_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2011_, 0, v___y_1998_);
return v___x_2011_;
}
v___jp_2013_:
{
lean_object* v___x_2016_; 
lean_inc(v___y_2015_);
lean_inc_ref(v___y_2014_);
lean_inc(v_decl_1990_);
v___x_2016_ = lean_apply_4(v_validate_1988_, v_decl_1990_, v___y_2014_, v___y_2015_, lean_box(0));
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v___x_2017_; lean_object* v_toEnvExtension_2018_; lean_object* v_env_2019_; lean_object* v_nextMacroScope_2020_; lean_object* v_ngen_2021_; lean_object* v_auxDeclNGen_2022_; lean_object* v_traceState_2023_; lean_object* v_recordedDeps_2024_; lean_object* v_messages_2025_; lean_object* v_infoState_2026_; lean_object* v_snapshotTasks_2027_; lean_object* v_asyncMode_2028_; uint8_t v_logWrites_2029_; lean_object* v___x_2030_; uint8_t v___x_2031_; 
lean_dec_ref_known(v___x_2016_, 1);
v___x_2017_ = lean_st_ref_take(v___y_2015_);
v_toEnvExtension_2018_ = lean_ctor_get(v_a_1987_, 0);
lean_inc_ref(v_toEnvExtension_2018_);
lean_dec_ref(v_a_1987_);
v_env_2019_ = lean_ctor_get(v___x_2017_, 0);
lean_inc_ref(v_env_2019_);
v_nextMacroScope_2020_ = lean_ctor_get(v___x_2017_, 1);
lean_inc(v_nextMacroScope_2020_);
v_ngen_2021_ = lean_ctor_get(v___x_2017_, 2);
lean_inc_ref(v_ngen_2021_);
v_auxDeclNGen_2022_ = lean_ctor_get(v___x_2017_, 3);
lean_inc_ref(v_auxDeclNGen_2022_);
v_traceState_2023_ = lean_ctor_get(v___x_2017_, 4);
lean_inc_ref(v_traceState_2023_);
v_recordedDeps_2024_ = lean_ctor_get(v___x_2017_, 6);
lean_inc_ref(v_recordedDeps_2024_);
v_messages_2025_ = lean_ctor_get(v___x_2017_, 7);
lean_inc_ref(v_messages_2025_);
v_infoState_2026_ = lean_ctor_get(v___x_2017_, 8);
lean_inc_ref(v_infoState_2026_);
v_snapshotTasks_2027_ = lean_ctor_get(v___x_2017_, 9);
lean_inc_ref(v_snapshotTasks_2027_);
lean_dec(v___x_2017_);
v_asyncMode_2028_ = lean_ctor_get(v_toEnvExtension_2018_, 2);
lean_inc(v_asyncMode_2028_);
v_logWrites_2029_ = lean_ctor_get_uint8(v_toEnvExtension_2018_, sizeof(void*)*6);
v___x_2030_ = lean_box(0);
v___x_2031_ = 1;
if (v_logWrites_2029_ == 0)
{
lean_object* v___x_2032_; 
v___x_2032_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2018_, v_env_2019_, v___f_2012_, v_asyncMode_2028_, v_decl_1990_, v___x_2031_);
lean_dec(v_asyncMode_2028_);
v___y_1997_ = v___y_2015_;
v___y_1998_ = v___x_2030_;
v_nextMacroScope_1999_ = v_nextMacroScope_2020_;
v_ngen_2000_ = v_ngen_2021_;
v_auxDeclNGen_2001_ = v_auxDeclNGen_2022_;
v_traceState_2002_ = v_traceState_2023_;
v_recordedDeps_2003_ = v_recordedDeps_2024_;
v_messages_2004_ = v_messages_2025_;
v_infoState_2005_ = v_infoState_2026_;
v_snapshotTasks_2006_ = v_snapshotTasks_2027_;
v___y_2007_ = v___x_2032_;
goto v___jp_1996_;
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
lean_inc(v_decl_1990_);
v___x_2033_ = l_Lean_Environment_logDeclChange(v_env_2019_, v_decl_1990_);
v___x_2034_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2018_, v___x_2033_, v___f_2012_, v_asyncMode_2028_, v_decl_1990_, v___x_2031_);
lean_dec(v_asyncMode_2028_);
v___y_1997_ = v___y_2015_;
v___y_1998_ = v___x_2030_;
v_nextMacroScope_1999_ = v_nextMacroScope_2020_;
v_ngen_2000_ = v_ngen_2021_;
v_auxDeclNGen_2001_ = v_auxDeclNGen_2022_;
v_traceState_2002_ = v_traceState_2023_;
v_recordedDeps_2003_ = v_recordedDeps_2024_;
v_messages_2004_ = v_messages_2025_;
v_infoState_2005_ = v_infoState_2026_;
v_snapshotTasks_2006_ = v_snapshotTasks_2027_;
v___y_2007_ = v___x_2034_;
goto v___jp_1996_;
}
}
else
{
lean_dec_ref(v___f_2012_);
lean_dec(v_decl_1990_);
lean_dec_ref(v_a_1987_);
return v___x_2016_;
}
}
v___jp_2035_:
{
lean_object* v_toEnvExtension_2039_; lean_object* v_asyncMode_2040_; uint8_t v___x_2041_; 
v_toEnvExtension_2039_ = lean_ctor_get(v_a_1987_, 0);
v_asyncMode_2040_ = lean_ctor_get(v_toEnvExtension_2039_, 2);
lean_inc(v_decl_1990_);
lean_inc_ref(v___y_2036_);
v___x_2041_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2036_, v_decl_1990_, v_asyncMode_2040_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
lean_dec_ref(v___f_2012_);
lean_dec_ref(v_validate_1988_);
lean_dec_ref(v_a_1987_);
v___x_2042_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2036_);
v___x_2043_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_1989_, v_decl_1990_, v___x_2042_, v___y_2037_, v___y_2038_);
return v___x_2043_;
}
else
{
lean_dec_ref(v___y_2036_);
lean_dec(v_name_1989_);
v___y_2014_ = v___y_2037_;
v___y_2015_ = v___y_2038_;
goto v___jp_2013_;
}
}
v___jp_2044_:
{
lean_object* v___x_2045_; lean_object* v_env_2046_; lean_object* v___x_2047_; 
v___x_2045_ = lean_st_ref_get(v___y_1994_);
v_env_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc_ref(v_env_2046_);
lean_dec(v___x_2045_);
v___x_2047_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2046_, v_decl_1990_);
if (lean_obj_tag(v___x_2047_) == 0)
{
v___y_2036_ = v_env_2046_;
v___y_2037_ = v___y_1993_;
v___y_2038_ = v___y_1994_;
goto v___jp_2035_;
}
else
{
lean_object* v___x_2048_; 
lean_dec_ref_known(v___x_2047_, 1);
lean_dec_ref(v_env_2046_);
lean_dec_ref(v___f_2012_);
lean_dec_ref(v_validate_1988_);
lean_dec_ref(v_a_1987_);
v___x_2048_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_1989_, v_decl_1990_, v___y_1993_, v___y_1994_);
return v___x_2048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__8___boxed(lean_object* v_a_2053_, lean_object* v_validate_2054_, lean_object* v_name_2055_, lean_object* v_decl_2056_, lean_object* v_stx_2057_, lean_object* v_kind_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
uint8_t v_kind_boxed_2062_; lean_object* v_res_2063_; 
v_kind_boxed_2062_ = lean_unbox(v_kind_2058_);
v_res_2063_ = l_Lean_registerTagAttribute___lam__8(v_a_2053_, v_validate_2054_, v_name_2055_, v_decl_2056_, v_stx_2057_, v_kind_boxed_2062_, v___y_2059_, v___y_2060_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
return v_res_2063_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2069_; lean_object* v___f_2070_; 
v___x_2069_ = l_Lean_NameSet_empty;
v___f_2070_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 4, 1);
lean_closure_set(v___f_2070_, 0, v___x_2069_);
return v___f_2070_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2071_; lean_object* v___f_2072_; 
v___x_2071_ = l_Lean_NameSet_empty;
v___f_2072_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 2, 1);
lean_closure_set(v___f_2072_, 0, v___x_2071_);
return v___f_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2075_, lean_object* v_descr_2076_, lean_object* v_validate_2077_, lean_object* v_ref_2078_, uint8_t v_applicationTime_2079_, lean_object* v_asyncMode_2080_, uint8_t v_logWrites_2081_){
_start:
{
lean_object* v___f_2083_; lean_object* v___f_2084_; lean_object* v___f_2085_; lean_object* v___f_2086_; lean_object* v___f_2087_; lean_object* v___f_2088_; lean_object* v___f_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___f_2083_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2084_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2085_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2086_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
lean_inc(v_name_2075_);
v___f_2087_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 5, 1);
lean_closure_set(v___f_2087_, 0, v_name_2075_);
v___f_2088_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2089_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2090_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
v___x_2091_ = 0;
lean_inc(v_ref_2078_);
v___x_2092_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2092_, 0, v_ref_2078_);
lean_ctor_set(v___x_2092_, 1, v___f_2089_);
lean_ctor_set(v___x_2092_, 2, v___f_2088_);
lean_ctor_set(v___x_2092_, 3, v___f_2086_);
lean_ctor_set(v___x_2092_, 4, v___f_2085_);
lean_ctor_set(v___x_2092_, 5, v___f_2084_);
lean_ctor_set(v___x_2092_, 6, v_asyncMode_2080_);
lean_ctor_set(v___x_2092_, 7, v___x_2090_);
lean_ctor_set_uint8(v___x_2092_, sizeof(void*)*8, v___x_2091_);
lean_ctor_set_uint8(v___x_2092_, sizeof(void*)*8 + 1, v_logWrites_2081_);
v___x_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
lean_ctor_set(v___x_2093_, 1, v___f_2083_);
v___x_2094_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2093_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___f_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc_n(v_a_2095_, 2);
lean_dec_ref_known(v___x_2094_, 1);
lean_inc(v_name_2075_);
v___f_2096_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__8___boxed), 9, 3);
lean_closure_set(v___f_2096_, 0, v_a_2095_);
lean_closure_set(v___f_2096_, 1, v_validate_2077_);
lean_closure_set(v___f_2096_, 2, v_name_2075_);
v___x_2097_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2097_, 0, v_ref_2078_);
lean_ctor_set(v___x_2097_, 1, v_name_2075_);
lean_ctor_set(v___x_2097_, 2, v_descr_2076_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*3, v_applicationTime_2079_);
v___x_2098_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set(v___x_2098_, 1, v___f_2096_);
lean_ctor_set(v___x_2098_, 2, v___f_2087_);
lean_inc_ref(v___x_2098_);
v___x_2099_ = l_Lean_registerBuiltinAttribute(v___x_2098_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2107_; 
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2107_ == 0)
{
lean_object* v_unused_2108_; 
v_unused_2108_ = lean_ctor_get(v___x_2099_, 0);
lean_dec(v_unused_2108_);
v___x_2101_ = v___x_2099_;
v_isShared_2102_ = v_isSharedCheck_2107_;
goto v_resetjp_2100_;
}
else
{
lean_dec(v___x_2099_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2107_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2098_);
lean_ctor_set(v___x_2103_, 1, v_a_2095_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2103_);
v___x_2105_ = v___x_2101_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec_ref_known(v___x_2098_, 3);
lean_dec(v_a_2095_);
v_a_2109_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2099_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2099_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec_ref(v___f_2087_);
lean_dec(v_ref_2078_);
lean_dec_ref(v_validate_2077_);
lean_dec_ref(v_descr_2076_);
lean_dec(v_name_2075_);
v_a_2117_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2094_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2094_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2125_, lean_object* v_descr_2126_, lean_object* v_validate_2127_, lean_object* v_ref_2128_, lean_object* v_applicationTime_2129_, lean_object* v_asyncMode_2130_, lean_object* v_logWrites_2131_, lean_object* v_a_2132_){
_start:
{
uint8_t v_applicationTime_boxed_2133_; uint8_t v_logWrites_boxed_2134_; lean_object* v_res_2135_; 
v_applicationTime_boxed_2133_ = lean_unbox(v_applicationTime_2129_);
v_logWrites_boxed_2134_ = lean_unbox(v_logWrites_2131_);
v_res_2135_ = l_Lean_registerTagAttribute(v_name_2125_, v_descr_2126_, v_validate_2127_, v_ref_2128_, v_applicationTime_boxed_2133_, v_asyncMode_2130_, v_logWrites_boxed_2134_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2136_, lean_object* v_t_2137_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2136_, v_t_2137_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2139_, lean_object* v_as_2140_, lean_object* v_lo_2141_, lean_object* v_hi_2142_, lean_object* v_w_2143_, lean_object* v_hlo_2144_, lean_object* v_hhi_2145_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2139_, v_as_2140_, v_lo_2141_, v_hi_2142_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2147_, lean_object* v_as_2148_, lean_object* v_lo_2149_, lean_object* v_hi_2150_, lean_object* v_w_2151_, lean_object* v_hlo_2152_, lean_object* v_hhi_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2147_, v_as_2148_, v_lo_2149_, v_hi_2150_, v_w_2151_, v_hlo_2152_, v_hhi_2153_);
lean_dec(v_hi_2150_);
lean_dec(v_n_2147_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2155_, lean_object* v_attrName_2156_, lean_object* v_declName_2157_, lean_object* v_asyncPrefix_x3f_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2156_, v_declName_2157_, v_asyncPrefix_x3f_2158_, v___y_2159_, v___y_2160_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2163_, lean_object* v_attrName_2164_, lean_object* v_declName_2165_, lean_object* v_asyncPrefix_x3f_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2163_, v_attrName_2164_, v_declName_2165_, v_asyncPrefix_x3f_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2171_, lean_object* v_attrName_2172_, lean_object* v_declName_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2172_, v_declName_2173_, v___y_2174_, v___y_2175_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2178_, lean_object* v_attrName_2179_, lean_object* v_declName_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2178_, v_attrName_2179_, v_declName_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2185_, lean_object* v_name_2186_, uint8_t v_kind_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2186_, v_kind_2187_, v___y_2188_, v___y_2189_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2192_, lean_object* v_name_2193_, lean_object* v_kind_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
uint8_t v_kind_boxed_2198_; lean_object* v_res_2199_; 
v_kind_boxed_2198_ = lean_unbox(v_kind_2194_);
v_res_2199_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2192_, v_name_2193_, v_kind_boxed_2198_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2200_, lean_object* v_lo_2201_, lean_object* v_hi_2202_, lean_object* v_hhi_2203_, lean_object* v_pivot_2204_, lean_object* v_as_2205_, lean_object* v_i_2206_, lean_object* v_k_2207_, lean_object* v_ilo_2208_, lean_object* v_ik_2209_, lean_object* v_w_2210_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2202_, v_pivot_2204_, v_as_2205_, v_i_2206_, v_k_2207_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2212_, lean_object* v_lo_2213_, lean_object* v_hi_2214_, lean_object* v_hhi_2215_, lean_object* v_pivot_2216_, lean_object* v_as_2217_, lean_object* v_i_2218_, lean_object* v_k_2219_, lean_object* v_ilo_2220_, lean_object* v_ik_2221_, lean_object* v_w_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2212_, v_lo_2213_, v_hi_2214_, v_hhi_2215_, v_pivot_2216_, v_as_2217_, v_i_2218_, v_k_2219_, v_ilo_2220_, v_ik_2221_, v_w_2222_);
lean_dec(v_pivot_2216_);
lean_dec(v_hi_2214_);
lean_dec(v_lo_2213_);
lean_dec(v_n_2212_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_addEntryFn_2224_, lean_object* v_decl_2225_, lean_object* v_s_2226_){
_start:
{
lean_object* v_importedEntries_2227_; lean_object* v_state_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2236_; 
v_importedEntries_2227_ = lean_ctor_get(v_s_2226_, 0);
v_state_2228_ = lean_ctor_get(v_s_2226_, 1);
v_isSharedCheck_2236_ = !lean_is_exclusive(v_s_2226_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2230_ = v_s_2226_;
v_isShared_2231_ = v_isSharedCheck_2236_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_state_2228_);
lean_inc(v_importedEntries_2227_);
lean_dec(v_s_2226_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2236_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v_state_2232_; lean_object* v___x_2234_; 
v_state_2232_ = lean_apply_2(v_addEntryFn_2224_, v_state_2228_, v_decl_2225_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 1, v_state_2232_);
v___x_2234_ = v___x_2230_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_importedEntries_2227_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_state_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_attr_2237_, lean_object* v_decl_2238_, lean_object* v_env_2239_){
_start:
{
lean_object* v_ext_2240_; lean_object* v_toEnvExtension_2241_; lean_object* v_addEntryFn_2242_; lean_object* v_asyncMode_2243_; uint8_t v_logWrites_2244_; lean_object* v___f_2245_; uint8_t v___x_2246_; 
v_ext_2240_ = lean_ctor_get(v_attr_2237_, 1);
lean_inc_ref(v_ext_2240_);
lean_dec_ref(v_attr_2237_);
v_toEnvExtension_2241_ = lean_ctor_get(v_ext_2240_, 0);
lean_inc_ref(v_toEnvExtension_2241_);
v_addEntryFn_2242_ = lean_ctor_get(v_ext_2240_, 3);
lean_inc(v_addEntryFn_2242_);
lean_dec_ref(v_ext_2240_);
v_asyncMode_2243_ = lean_ctor_get(v_toEnvExtension_2241_, 2);
lean_inc(v_asyncMode_2243_);
v_logWrites_2244_ = lean_ctor_get_uint8(v_toEnvExtension_2241_, sizeof(void*)*6);
lean_inc(v_decl_2238_);
v___f_2245_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2245_, 0, v_addEntryFn_2242_);
lean_closure_set(v___f_2245_, 1, v_decl_2238_);
v___x_2246_ = 1;
if (v_logWrites_2244_ == 0)
{
lean_object* v___x_2247_; 
v___x_2247_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2241_, v_env_2239_, v___f_2245_, v_asyncMode_2243_, v_decl_2238_, v___x_2246_);
lean_dec(v_asyncMode_2243_);
return v___x_2247_;
}
else
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
lean_inc_ref(v_toEnvExtension_2241_);
v___x_2248_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2241_, v_env_2239_);
lean_dec_ref(v_env_2239_);
v___x_2249_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2241_, v___x_2248_, v___f_2245_, v_asyncMode_2243_, v_decl_2238_, v___x_2246_);
lean_dec(v_asyncMode_2243_);
return v___x_2249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_modifyEnv_2250_, lean_object* v___f_2251_, lean_object* v_____r_2252_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = lean_apply_1(v_modifyEnv_2250_, v___f_2251_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v_attr_2254_, lean_object* v_env_2255_, lean_object* v_decl_2256_, lean_object* v_inst_2257_, lean_object* v_inst_2258_, lean_object* v_toBind_2259_, lean_object* v___f_2260_, lean_object* v_modifyEnv_2261_, lean_object* v___f_2262_, lean_object* v_____r_2263_){
_start:
{
lean_object* v_ext_2264_; lean_object* v_toEnvExtension_2265_; lean_object* v_attr_2266_; lean_object* v_asyncMode_2267_; uint8_t v___x_2268_; 
v_ext_2264_ = lean_ctor_get(v_attr_2254_, 1);
v_toEnvExtension_2265_ = lean_ctor_get(v_ext_2264_, 0);
lean_inc_ref(v_toEnvExtension_2265_);
v_attr_2266_ = lean_ctor_get(v_attr_2254_, 0);
lean_inc_ref(v_attr_2266_);
lean_dec_ref(v_attr_2254_);
v_asyncMode_2267_ = lean_ctor_get(v_toEnvExtension_2265_, 2);
lean_inc(v_asyncMode_2267_);
lean_dec_ref(v_toEnvExtension_2265_);
lean_inc(v_decl_2256_);
lean_inc_ref(v_env_2255_);
v___x_2268_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2255_, v_decl_2256_, v_asyncMode_2267_);
lean_dec(v_asyncMode_2267_);
if (v___x_2268_ == 0)
{
lean_object* v_toAttributeImplCore_2269_; lean_object* v_name_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_dec_ref(v___f_2262_);
lean_dec(v_modifyEnv_2261_);
v_toAttributeImplCore_2269_ = lean_ctor_get(v_attr_2266_, 0);
lean_inc_ref(v_toAttributeImplCore_2269_);
lean_dec_ref(v_attr_2266_);
v_name_2270_ = lean_ctor_get(v_toAttributeImplCore_2269_, 1);
lean_inc(v_name_2270_);
lean_dec_ref(v_toAttributeImplCore_2269_);
v___x_2271_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2255_);
v___x_2272_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2257_, v_inst_2258_, v_name_2270_, v_decl_2256_, v___x_2271_);
v___x_2273_ = lean_apply_4(v_toBind_2259_, lean_box(0), lean_box(0), v___x_2272_, v___f_2260_);
return v___x_2273_;
}
else
{
lean_object* v___x_2274_; 
lean_dec_ref(v_attr_2266_);
lean_dec(v___f_2260_);
lean_dec(v_toBind_2259_);
lean_dec_ref(v_inst_2258_);
lean_dec_ref(v_inst_2257_);
lean_dec(v_decl_2256_);
lean_dec_ref(v_env_2255_);
v___x_2274_ = lean_apply_1(v_modifyEnv_2261_, v___f_2262_);
return v___x_2274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v___f_2275_, lean_object* v_____r_2276_){
_start:
{
lean_object* v___x_2277_; 
v___x_2277_ = lean_apply_1(v___f_2275_, v_____r_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__5(lean_object* v_attr_2278_, lean_object* v_decl_2279_, lean_object* v_inst_2280_, lean_object* v_inst_2281_, lean_object* v_toBind_2282_, lean_object* v___f_2283_, lean_object* v_modifyEnv_2284_, lean_object* v___f_2285_, lean_object* v_env_2286_){
_start:
{
lean_object* v___f_2287_; lean_object* v___x_2288_; 
lean_inc_ref(v___f_2285_);
lean_inc(v_modifyEnv_2284_);
lean_inc(v___f_2283_);
lean_inc(v_toBind_2282_);
lean_inc_ref(v_inst_2281_);
lean_inc_ref(v_inst_2280_);
lean_inc(v_decl_2279_);
lean_inc_ref(v_env_2286_);
lean_inc_ref(v_attr_2278_);
v___f_2287_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 10, 9);
lean_closure_set(v___f_2287_, 0, v_attr_2278_);
lean_closure_set(v___f_2287_, 1, v_env_2286_);
lean_closure_set(v___f_2287_, 2, v_decl_2279_);
lean_closure_set(v___f_2287_, 3, v_inst_2280_);
lean_closure_set(v___f_2287_, 4, v_inst_2281_);
lean_closure_set(v___f_2287_, 5, v_toBind_2282_);
lean_closure_set(v___f_2287_, 6, v___f_2283_);
lean_closure_set(v___f_2287_, 7, v_modifyEnv_2284_);
lean_closure_set(v___f_2287_, 8, v___f_2285_);
v___x_2288_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2286_, v_decl_2279_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
lean_dec_ref(v___f_2287_);
v___x_2289_ = lean_box(0);
v___x_2290_ = l_Lean_TagAttribute_setTag___redArg___lam__3(v_attr_2278_, v_env_2286_, v_decl_2279_, v_inst_2280_, v_inst_2281_, v_toBind_2282_, v___f_2283_, v_modifyEnv_2284_, v___f_2285_, v___x_2289_);
return v___x_2290_;
}
else
{
lean_object* v_attr_2291_; lean_object* v_toAttributeImplCore_2292_; lean_object* v_name_2293_; lean_object* v___f_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
lean_dec_ref_known(v___x_2288_, 1);
lean_dec_ref(v_env_2286_);
lean_dec_ref(v___f_2285_);
lean_dec(v_modifyEnv_2284_);
lean_dec(v___f_2283_);
v_attr_2291_ = lean_ctor_get(v_attr_2278_, 0);
lean_inc_ref(v_attr_2291_);
lean_dec_ref(v_attr_2278_);
v_toAttributeImplCore_2292_ = lean_ctor_get(v_attr_2291_, 0);
lean_inc_ref(v_toAttributeImplCore_2292_);
lean_dec_ref(v_attr_2291_);
v_name_2293_ = lean_ctor_get(v_toAttributeImplCore_2292_, 1);
lean_inc(v_name_2293_);
lean_dec_ref(v_toAttributeImplCore_2292_);
v___f_2294_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2294_, 0, v___f_2287_);
v___x_2295_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2280_, v_inst_2281_, v_name_2293_, v_decl_2279_);
v___x_2296_ = lean_apply_4(v_toBind_2282_, lean_box(0), lean_box(0), v___x_2295_, v___f_2294_);
return v___x_2296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2297_, lean_object* v_inst_2298_, lean_object* v_inst_2299_, lean_object* v_attr_2300_, lean_object* v_decl_2301_){
_start:
{
lean_object* v_toBind_2302_; lean_object* v_getEnv_2303_; lean_object* v_modifyEnv_2304_; lean_object* v___f_2305_; lean_object* v___f_2306_; lean_object* v___f_2307_; lean_object* v___x_2308_; 
v_toBind_2302_ = lean_ctor_get(v_inst_2297_, 1);
lean_inc_n(v_toBind_2302_, 2);
v_getEnv_2303_ = lean_ctor_get(v_inst_2299_, 0);
lean_inc(v_getEnv_2303_);
v_modifyEnv_2304_ = lean_ctor_get(v_inst_2299_, 1);
lean_inc_n(v_modifyEnv_2304_, 2);
lean_dec_ref(v_inst_2299_);
lean_inc(v_decl_2301_);
lean_inc_ref(v_attr_2300_);
v___f_2305_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2305_, 0, v_attr_2300_);
lean_closure_set(v___f_2305_, 1, v_decl_2301_);
lean_inc_ref(v___f_2305_);
v___f_2306_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2306_, 0, v_modifyEnv_2304_);
lean_closure_set(v___f_2306_, 1, v___f_2305_);
v___f_2307_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__5), 9, 8);
lean_closure_set(v___f_2307_, 0, v_attr_2300_);
lean_closure_set(v___f_2307_, 1, v_decl_2301_);
lean_closure_set(v___f_2307_, 2, v_inst_2297_);
lean_closure_set(v___f_2307_, 3, v_inst_2298_);
lean_closure_set(v___f_2307_, 4, v_toBind_2302_);
lean_closure_set(v___f_2307_, 5, v___f_2306_);
lean_closure_set(v___f_2307_, 6, v_modifyEnv_2304_);
lean_closure_set(v___f_2307_, 7, v___f_2305_);
v___x_2308_ = lean_apply_4(v_toBind_2302_, lean_box(0), lean_box(0), v_getEnv_2303_, v___f_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2309_, lean_object* v_inst_2310_, lean_object* v_inst_2311_, lean_object* v_inst_2312_, lean_object* v_attr_2313_, lean_object* v_decl_2314_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2310_, v_inst_2311_, v_inst_2312_, v_attr_2313_, v_decl_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v___y_2316_, lean_object* v_as_2317_, lean_object* v_k_2318_, lean_object* v_x_2319_, lean_object* v_x_2320_){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v_m_2323_; lean_object* v_a_2324_; uint8_t v___x_2325_; 
v___x_2321_ = lean_nat_add(v_x_2319_, v_x_2320_);
v___x_2322_ = lean_unsigned_to_nat(1u);
v_m_2323_ = lean_nat_shiftr(v___x_2321_, v___x_2322_);
lean_dec(v___x_2321_);
v_a_2324_ = lean_array_fget_borrowed(v_as_2317_, v_m_2323_);
v___x_2325_ = l_Lean_Name_quickLt(v_a_2324_, v_k_2318_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; uint8_t v___x_2327_; 
lean_dec(v_x_2320_);
v___x_2326_ = lean_unsigned_to_nat(0u);
v___x_2327_ = l_Lean_Name_quickLt(v_k_2318_, v_a_2324_);
if (v___x_2327_ == 0)
{
uint8_t v___x_2328_; 
lean_dec(v_m_2323_);
lean_dec(v_x_2319_);
v___x_2328_ = lean_nat_dec_le(v___x_2326_, v___y_2316_);
return v___x_2328_;
}
else
{
uint8_t v___x_2329_; 
v___x_2329_ = lean_nat_dec_eq(v_m_2323_, v___x_2326_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___x_2330_ = lean_nat_sub(v_m_2323_, v___x_2322_);
lean_dec(v_m_2323_);
v___x_2331_ = lean_nat_dec_lt(v___x_2330_, v_x_2319_);
if (v___x_2331_ == 0)
{
v_x_2320_ = v___x_2330_;
goto _start;
}
else
{
lean_dec(v___x_2330_);
lean_dec(v_x_2319_);
return v___x_2329_;
}
}
else
{
lean_dec(v_m_2323_);
lean_dec(v_x_2319_);
return v___x_2325_;
}
}
}
else
{
lean_object* v___x_2333_; uint8_t v___x_2334_; 
lean_dec(v_x_2319_);
v___x_2333_ = lean_nat_add(v_m_2323_, v___x_2322_);
lean_dec(v_m_2323_);
v___x_2334_ = lean_nat_dec_le(v___x_2333_, v_x_2320_);
if (v___x_2334_ == 0)
{
lean_dec(v___x_2333_);
lean_dec(v_x_2320_);
return v___x_2334_;
}
else
{
v_x_2319_ = v___x_2333_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v___y_2336_, lean_object* v_as_2337_, lean_object* v_k_2338_, lean_object* v_x_2339_, lean_object* v_x_2340_){
_start:
{
uint8_t v_res_2341_; lean_object* v_r_2342_; 
v_res_2341_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2336_, v_as_2337_, v_k_2338_, v_x_2339_, v_x_2340_);
lean_dec(v_k_2338_);
lean_dec_ref(v_as_2337_);
lean_dec(v___y_2336_);
v_r_2342_ = lean_box(v_res_2341_);
return v_r_2342_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2343_, lean_object* v_env_2344_, lean_object* v_decl_2345_){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = lean_box(1);
v___x_2347_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2344_, v_decl_2345_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_ext_2348_; lean_object* v_toEnvExtension_2349_; lean_object* v_asyncMode_2350_; uint8_t v___x_2351_; lean_object* v___x_2352_; uint8_t v___x_2353_; 
v_ext_2348_ = lean_ctor_get(v_attr_2343_, 1);
v_toEnvExtension_2349_ = lean_ctor_get(v_ext_2348_, 0);
v_asyncMode_2350_ = lean_ctor_get(v_toEnvExtension_2349_, 2);
v___x_2351_ = 0;
lean_inc(v_decl_2345_);
v___x_2352_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2346_, v_ext_2348_, v_env_2344_, v_asyncMode_2350_, v_decl_2345_, v___x_2351_);
v___x_2353_ = l_Lean_NameSet_contains(v___x_2352_, v_decl_2345_);
lean_dec(v_decl_2345_);
lean_dec(v___x_2352_);
return v___x_2353_;
}
else
{
lean_object* v_val_2354_; lean_object* v_ext_2355_; uint8_t v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; uint8_t v___x_2360_; 
v_val_2354_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_val_2354_);
lean_dec_ref_known(v___x_2347_, 1);
v_ext_2355_ = lean_ctor_get(v_attr_2343_, 1);
v___x_2356_ = 0;
v___x_2357_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2346_, v_ext_2355_, v_env_2344_, v_val_2354_, v___x_2356_);
lean_dec(v_val_2354_);
lean_dec_ref(v_env_2344_);
v___x_2358_ = lean_unsigned_to_nat(0u);
v___x_2359_ = lean_array_get_size(v___x_2357_);
v___x_2360_ = lean_nat_dec_lt(v___x_2358_, v___x_2359_);
if (v___x_2360_ == 0)
{
lean_dec_ref(v___x_2357_);
lean_dec(v_decl_2345_);
return v___x_2360_;
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v___x_2361_ = lean_unsigned_to_nat(1u);
v___x_2362_ = lean_nat_sub(v___x_2359_, v___x_2361_);
v___x_2363_ = lean_nat_dec_le(v___x_2358_, v___x_2362_);
if (v___x_2363_ == 0)
{
lean_dec(v___x_2362_);
lean_dec_ref(v___x_2357_);
lean_dec(v_decl_2345_);
return v___x_2363_;
}
else
{
uint8_t v___x_2364_; 
lean_inc(v___x_2362_);
v___x_2364_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2362_, v___x_2357_, v_decl_2345_, v___x_2358_, v___x_2362_);
lean_dec(v_decl_2345_);
lean_dec_ref(v___x_2357_);
lean_dec(v___x_2362_);
return v___x_2364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2365_, lean_object* v_env_2366_, lean_object* v_decl_2367_){
_start:
{
uint8_t v_res_2368_; lean_object* v_r_2369_; 
v_res_2368_ = l_Lean_TagAttribute_hasTag(v_attr_2365_, v_env_2366_, v_decl_2367_);
lean_dec_ref(v_attr_2365_);
v_r_2369_ = lean_box(v_res_2368_);
return v_r_2369_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v___y_2370_, lean_object* v_as_2371_, lean_object* v_k_2372_, lean_object* v_x_2373_, lean_object* v_x_2374_, lean_object* v_x_2375_){
_start:
{
uint8_t v___x_2376_; 
v___x_2376_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2370_, v_as_2371_, v_k_2372_, v_x_2373_, v_x_2374_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v___y_2377_, lean_object* v_as_2378_, lean_object* v_k_2379_, lean_object* v_x_2380_, lean_object* v_x_2381_, lean_object* v_x_2382_){
_start:
{
uint8_t v_res_2383_; lean_object* v_r_2384_; 
v_res_2383_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v___y_2377_, v_as_2378_, v_k_2379_, v_x_2380_, v_x_2381_, v_x_2382_);
lean_dec(v_k_2379_);
lean_dec_ref(v_as_2378_);
lean_dec(v___y_2377_);
v_r_2384_ = lean_box(v_res_2383_);
return v_r_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(lean_object* v_x_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0___boxed(lean_object* v_x_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(v_x_2390_, v___y_2391_);
lean_dec_ref(v___y_2391_);
lean_dec_ref(v_x_2390_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(lean_object* v_s_2394_, lean_object* v_x_2395_){
_start:
{
lean_inc_ref(v_s_2394_);
return v_s_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1___boxed(lean_object* v_s_2396_, lean_object* v_x_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(v_s_2396_, v_x_2397_);
lean_dec_ref(v_x_2397_);
lean_dec_ref(v_s_2396_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(lean_object* v_x_2403_, lean_object* v_x_2404_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___boxed(lean_object* v_x_2406_, lean_object* v_x_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(v_x_2406_, v_x_2407_);
lean_dec_ref(v_x_2407_);
lean_dec_ref(v_x_2406_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(lean_object* v_x_2409_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = lean_box(0);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3___boxed(lean_object* v_x_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(v_x_2411_);
lean_dec_ref(v_x_2411_);
return v_res_2412_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4(void){
_start:
{
lean_object* v___f_2417_; lean_object* v___f_2418_; lean_object* v___f_2419_; lean_object* v___f_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___f_2417_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3));
v___f_2418_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2));
v___f_2419_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1));
v___f_2420_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0));
v___x_2421_ = lean_box(0);
v___x_2422_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_2423_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
lean_ctor_set(v___x_2423_, 1, v___x_2421_);
lean_ctor_set(v___x_2423_, 2, v___f_2420_);
lean_ctor_set(v___x_2423_, 3, v___f_2419_);
lean_ctor_set(v___x_2423_, 4, v___f_2418_);
lean_ctor_set(v___x_2423_, 5, v___f_2417_);
return v___x_2423_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5(void){
_start:
{
uint8_t v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2424_ = 0;
v___x_2425_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4);
v___x_2426_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2427_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
lean_ctor_set(v___x_2427_, 1, v___x_2425_);
lean_ctor_set_uint8(v___x_2427_, sizeof(void*)*2, v___x_2424_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg(){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___boxed(lean_object* v___dummy_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v_res_2431_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__0(void){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2433_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg(){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg___boxed(lean_object* v___dummy_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_instInhabitedParametricAttribute___redArg();
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2439_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object* v_x_2441_, lean_object* v_p_2442_){
_start:
{
lean_object* v_fst_2443_; lean_object* v_snd_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2461_; 
v_fst_2443_ = lean_ctor_get(v_x_2441_, 0);
v_snd_2444_ = lean_ctor_get(v_x_2441_, 1);
v_isSharedCheck_2461_ = !lean_is_exclusive(v_x_2441_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2446_ = v_x_2441_;
v_isShared_2447_ = v_isSharedCheck_2461_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_snd_2444_);
lean_inc(v_fst_2443_);
lean_dec(v_x_2441_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2461_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v_fst_2448_; lean_object* v_snd_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2460_; 
v_fst_2448_ = lean_ctor_get(v_p_2442_, 0);
v_snd_2449_ = lean_ctor_get(v_p_2442_, 1);
v_isSharedCheck_2460_ = !lean_is_exclusive(v_p_2442_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2451_ = v_p_2442_;
v_isShared_2452_ = v_isSharedCheck_2460_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_snd_2449_);
lean_inc(v_fst_2448_);
lean_dec(v_p_2442_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2460_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
lean_inc(v_fst_2448_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set_tag(v___x_2446_, 1);
lean_ctor_set(v___x_2446_, 1, v_fst_2443_);
lean_ctor_set(v___x_2446_, 0, v_fst_2448_);
v___x_2454_ = v___x_2446_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_fst_2448_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v_fst_2443_);
v___x_2454_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2457_; 
v___x_2455_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2448_, v_snd_2449_, v_snd_2444_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 1, v___x_2455_);
lean_ctor_set(v___x_2451_, 0, v___x_2454_);
v___x_2457_ = v___x_2451_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v___x_2455_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object* v_init_2462_, lean_object* v_x_2463_){
_start:
{
if (lean_obj_tag(v_x_2463_) == 0)
{
lean_object* v_k_2464_; lean_object* v_v_2465_; lean_object* v_l_2466_; lean_object* v_r_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v_k_2464_ = lean_ctor_get(v_x_2463_, 1);
v_v_2465_ = lean_ctor_get(v_x_2463_, 2);
v_l_2466_ = lean_ctor_get(v_x_2463_, 3);
v_r_2467_ = lean_ctor_get(v_x_2463_, 4);
v___x_2468_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2462_, v_l_2466_);
lean_inc(v_v_2465_);
lean_inc(v_k_2464_);
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v_k_2464_);
lean_ctor_set(v___x_2469_, 1, v_v_2465_);
v___x_2470_ = lean_array_push(v___x_2468_, v___x_2469_);
v_init_2462_ = v___x_2470_;
v_x_2463_ = v_r_2467_;
goto _start;
}
else
{
return v_init_2462_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object* v_init_2472_, lean_object* v_x_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2472_, v_x_2473_);
lean_dec(v_x_2473_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object* v_snd_2475_, lean_object* v_as_2476_, size_t v_i_2477_, size_t v_stop_2478_, lean_object* v_b_2479_){
_start:
{
lean_object* v___y_2481_; uint8_t v___x_2485_; 
v___x_2485_ = lean_usize_dec_eq(v_i_2477_, v_stop_2478_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = lean_array_uget_borrowed(v_as_2476_, v_i_2477_);
v___x_2487_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2475_, v___x_2486_);
if (lean_obj_tag(v___x_2487_) == 0)
{
v___y_2481_ = v_b_2479_;
goto v___jp_2480_;
}
else
{
lean_object* v_val_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v_val_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_val_2488_);
lean_dec_ref_known(v___x_2487_, 1);
lean_inc(v___x_2486_);
v___x_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2486_);
lean_ctor_set(v___x_2489_, 1, v_val_2488_);
v___x_2490_ = lean_array_push(v_b_2479_, v___x_2489_);
v___y_2481_ = v___x_2490_;
goto v___jp_2480_;
}
}
else
{
return v_b_2479_;
}
v___jp_2480_:
{
size_t v___x_2482_; size_t v___x_2483_; 
v___x_2482_ = ((size_t)1ULL);
v___x_2483_ = lean_usize_add(v_i_2477_, v___x_2482_);
v_i_2477_ = v___x_2483_;
v_b_2479_ = v___y_2481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2491_, lean_object* v_as_2492_, lean_object* v_i_2493_, lean_object* v_stop_2494_, lean_object* v_b_2495_){
_start:
{
size_t v_i_boxed_2496_; size_t v_stop_boxed_2497_; lean_object* v_res_2498_; 
v_i_boxed_2496_ = lean_unbox_usize(v_i_2493_);
lean_dec(v_i_2493_);
v_stop_boxed_2497_ = lean_unbox_usize(v_stop_2494_);
lean_dec(v_stop_2494_);
v_res_2498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2491_, v_as_2492_, v_i_boxed_2496_, v_stop_boxed_2497_, v_b_2495_);
lean_dec_ref(v_as_2492_);
lean_dec(v_snd_2491_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object* v_snd_2499_, lean_object* v_as_2500_, lean_object* v_start_2501_, lean_object* v_stop_2502_){
_start:
{
lean_object* v___x_2503_; uint8_t v___x_2504_; 
v___x_2503_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2504_ = lean_nat_dec_lt(v_start_2501_, v_stop_2502_);
if (v___x_2504_ == 0)
{
return v___x_2503_;
}
else
{
lean_object* v___x_2505_; uint8_t v___x_2506_; 
v___x_2505_ = lean_array_get_size(v_as_2500_);
v___x_2506_ = lean_nat_dec_le(v_stop_2502_, v___x_2505_);
if (v___x_2506_ == 0)
{
uint8_t v___x_2507_; 
v___x_2507_ = lean_nat_dec_lt(v_start_2501_, v___x_2505_);
if (v___x_2507_ == 0)
{
return v___x_2503_;
}
else
{
size_t v___x_2508_; size_t v___x_2509_; lean_object* v___x_2510_; 
v___x_2508_ = lean_usize_of_nat(v_start_2501_);
v___x_2509_ = lean_usize_of_nat(v___x_2505_);
v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2499_, v_as_2500_, v___x_2508_, v___x_2509_, v___x_2503_);
return v___x_2510_;
}
}
else
{
size_t v___x_2511_; size_t v___x_2512_; lean_object* v___x_2513_; 
v___x_2511_ = lean_usize_of_nat(v_start_2501_);
v___x_2512_ = lean_usize_of_nat(v_stop_2502_);
v___x_2513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2499_, v_as_2500_, v___x_2511_, v___x_2512_, v___x_2503_);
return v___x_2513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object* v_snd_2514_, lean_object* v_as_2515_, lean_object* v_start_2516_, lean_object* v_stop_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2514_, v_as_2515_, v_start_2516_, v_stop_2517_);
lean_dec(v_stop_2517_);
lean_dec(v_start_2516_);
lean_dec_ref(v_as_2515_);
lean_dec(v_snd_2514_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object* v_hi_2519_, lean_object* v_pivot_2520_, lean_object* v_as_2521_, lean_object* v_i_2522_, lean_object* v_k_2523_){
_start:
{
uint8_t v___x_2524_; 
v___x_2524_ = lean_nat_dec_lt(v_k_2523_, v_hi_2519_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
lean_dec(v_k_2523_);
v___x_2525_ = lean_array_fswap(v_as_2521_, v_i_2522_, v_hi_2519_);
v___x_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2526_, 0, v_i_2522_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
return v___x_2526_;
}
else
{
lean_object* v___x_2527_; lean_object* v_fst_2528_; lean_object* v_fst_2529_; uint8_t v___x_2530_; 
v___x_2527_ = lean_array_fget_borrowed(v_as_2521_, v_k_2523_);
v_fst_2528_ = lean_ctor_get(v___x_2527_, 0);
v_fst_2529_ = lean_ctor_get(v_pivot_2520_, 0);
v___x_2530_ = l_Lean_Name_quickLt(v_fst_2528_, v_fst_2529_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = lean_unsigned_to_nat(1u);
v___x_2532_ = lean_nat_add(v_k_2523_, v___x_2531_);
lean_dec(v_k_2523_);
v_k_2523_ = v___x_2532_;
goto _start;
}
else
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2534_ = lean_array_fswap(v_as_2521_, v_i_2522_, v_k_2523_);
v___x_2535_ = lean_unsigned_to_nat(1u);
v___x_2536_ = lean_nat_add(v_i_2522_, v___x_2535_);
lean_dec(v_i_2522_);
v___x_2537_ = lean_nat_add(v_k_2523_, v___x_2535_);
lean_dec(v_k_2523_);
v_as_2521_ = v___x_2534_;
v_i_2522_ = v___x_2536_;
v_k_2523_ = v___x_2537_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2539_, lean_object* v_pivot_2540_, lean_object* v_as_2541_, lean_object* v_i_2542_, lean_object* v_k_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2539_, v_pivot_2540_, v_as_2541_, v_i_2542_, v_k_2543_);
lean_dec_ref(v_pivot_2540_);
lean_dec(v_hi_2539_);
return v_res_2544_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object* v_a_2545_, lean_object* v_b_2546_){
_start:
{
lean_object* v_fst_2547_; lean_object* v_fst_2548_; uint8_t v___x_2549_; 
v_fst_2547_ = lean_ctor_get(v_a_2545_, 0);
v_fst_2548_ = lean_ctor_get(v_b_2546_, 0);
v___x_2549_ = l_Lean_Name_quickLt(v_fst_2547_, v_fst_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object* v_a_2550_, lean_object* v_b_2551_){
_start:
{
uint8_t v_res_2552_; lean_object* v_r_2553_; 
v_res_2552_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2550_, v_b_2551_);
lean_dec_ref(v_b_2551_);
lean_dec_ref(v_a_2550_);
v_r_2553_ = lean_box(v_res_2552_);
return v_r_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object* v_n_2554_, lean_object* v_as_2555_, lean_object* v_lo_2556_, lean_object* v_hi_2557_){
_start:
{
lean_object* v___y_2559_; uint8_t v___x_2569_; 
v___x_2569_ = lean_nat_dec_lt(v_lo_2556_, v_hi_2557_);
if (v___x_2569_ == 0)
{
lean_dec(v_lo_2556_);
return v_as_2555_;
}
else
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v_mid_2572_; lean_object* v___y_2574_; lean_object* v___y_2580_; lean_object* v___x_2585_; lean_object* v___x_2586_; uint8_t v___x_2587_; 
v___x_2570_ = lean_nat_add(v_lo_2556_, v_hi_2557_);
v___x_2571_ = lean_unsigned_to_nat(1u);
v_mid_2572_ = lean_nat_shiftr(v___x_2570_, v___x_2571_);
lean_dec(v___x_2570_);
v___x_2585_ = lean_array_fget_borrowed(v_as_2555_, v_mid_2572_);
v___x_2586_ = lean_array_fget_borrowed(v_as_2555_, v_lo_2556_);
v___x_2587_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2585_, v___x_2586_);
if (v___x_2587_ == 0)
{
v___y_2580_ = v_as_2555_;
goto v___jp_2579_;
}
else
{
lean_object* v___x_2588_; 
v___x_2588_ = lean_array_fswap(v_as_2555_, v_lo_2556_, v_mid_2572_);
v___y_2580_ = v___x_2588_;
goto v___jp_2579_;
}
v___jp_2573_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2575_ = lean_array_fget_borrowed(v___y_2574_, v_mid_2572_);
v___x_2576_ = lean_array_fget_borrowed(v___y_2574_, v_hi_2557_);
v___x_2577_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2575_, v___x_2576_);
if (v___x_2577_ == 0)
{
lean_dec(v_mid_2572_);
v___y_2559_ = v___y_2574_;
goto v___jp_2558_;
}
else
{
lean_object* v___x_2578_; 
v___x_2578_ = lean_array_fswap(v___y_2574_, v_mid_2572_, v_hi_2557_);
lean_dec(v_mid_2572_);
v___y_2559_ = v___x_2578_;
goto v___jp_2558_;
}
}
v___jp_2579_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; 
v___x_2581_ = lean_array_fget_borrowed(v___y_2580_, v_hi_2557_);
v___x_2582_ = lean_array_fget_borrowed(v___y_2580_, v_lo_2556_);
v___x_2583_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2581_, v___x_2582_);
if (v___x_2583_ == 0)
{
v___y_2574_ = v___y_2580_;
goto v___jp_2573_;
}
else
{
lean_object* v___x_2584_; 
v___x_2584_ = lean_array_fswap(v___y_2580_, v_lo_2556_, v_hi_2557_);
v___y_2574_ = v___x_2584_;
goto v___jp_2573_;
}
}
}
v___jp_2558_:
{
lean_object* v_pivot_2560_; lean_object* v___x_2561_; lean_object* v_fst_2562_; lean_object* v_snd_2563_; uint8_t v___x_2564_; 
v_pivot_2560_ = lean_array_fget(v___y_2559_, v_hi_2557_);
lean_inc_n(v_lo_2556_, 2);
v___x_2561_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2557_, v_pivot_2560_, v___y_2559_, v_lo_2556_, v_lo_2556_);
lean_dec(v_pivot_2560_);
v_fst_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_fst_2562_);
v_snd_2563_ = lean_ctor_get(v___x_2561_, 1);
lean_inc(v_snd_2563_);
lean_dec_ref(v___x_2561_);
v___x_2564_ = lean_nat_dec_le(v_hi_2557_, v_fst_2562_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2565_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2554_, v_snd_2563_, v_lo_2556_, v_fst_2562_);
v___x_2566_ = lean_unsigned_to_nat(1u);
v___x_2567_ = lean_nat_add(v_fst_2562_, v___x_2566_);
lean_dec(v_fst_2562_);
v_as_2555_ = v___x_2565_;
v_lo_2556_ = v___x_2567_;
goto _start;
}
else
{
lean_dec(v_fst_2562_);
lean_dec(v_lo_2556_);
return v_snd_2563_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object* v_n_2589_, lean_object* v_as_2590_, lean_object* v_lo_2591_, lean_object* v_hi_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2589_, v_as_2590_, v_lo_2591_, v_hi_2592_);
lean_dec(v_hi_2592_);
lean_dec(v_n_2589_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object* v_filterExport_2594_, lean_object* v_env_2595_, lean_object* v_as_2596_, size_t v_i_2597_, size_t v_stop_2598_, lean_object* v_b_2599_){
_start:
{
lean_object* v___y_2601_; uint8_t v___x_2605_; 
v___x_2605_ = lean_usize_dec_eq(v_i_2597_, v_stop_2598_);
if (v___x_2605_ == 0)
{
lean_object* v___x_2606_; lean_object* v_fst_2607_; lean_object* v_snd_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; 
v___x_2606_ = lean_array_uget_borrowed(v_as_2596_, v_i_2597_);
v_fst_2607_ = lean_ctor_get(v___x_2606_, 0);
v_snd_2608_ = lean_ctor_get(v___x_2606_, 1);
lean_inc_ref(v_filterExport_2594_);
lean_inc(v_snd_2608_);
lean_inc(v_fst_2607_);
lean_inc_ref(v_env_2595_);
v___x_2609_ = lean_apply_3(v_filterExport_2594_, v_env_2595_, v_fst_2607_, v_snd_2608_);
v___x_2610_ = lean_unbox(v___x_2609_);
if (v___x_2610_ == 0)
{
v___y_2601_ = v_b_2599_;
goto v___jp_2600_;
}
else
{
lean_object* v___x_2611_; 
lean_inc(v___x_2606_);
v___x_2611_ = lean_array_push(v_b_2599_, v___x_2606_);
v___y_2601_ = v___x_2611_;
goto v___jp_2600_;
}
}
else
{
lean_dec_ref(v_env_2595_);
lean_dec_ref(v_filterExport_2594_);
return v_b_2599_;
}
v___jp_2600_:
{
size_t v___x_2602_; size_t v___x_2603_; 
v___x_2602_ = ((size_t)1ULL);
v___x_2603_ = lean_usize_add(v_i_2597_, v___x_2602_);
v_i_2597_ = v___x_2603_;
v_b_2599_ = v___y_2601_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object* v_filterExport_2612_, lean_object* v_env_2613_, lean_object* v_as_2614_, lean_object* v_i_2615_, lean_object* v_stop_2616_, lean_object* v_b_2617_){
_start:
{
size_t v_i_boxed_2618_; size_t v_stop_boxed_2619_; lean_object* v_res_2620_; 
v_i_boxed_2618_ = lean_unbox_usize(v_i_2615_);
lean_dec(v_i_2615_);
v_stop_boxed_2619_ = lean_unbox_usize(v_stop_2616_);
lean_dec(v_stop_2616_);
v_res_2620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2612_, v_env_2613_, v_as_2614_, v_i_boxed_2618_, v_stop_boxed_2619_, v_b_2617_);
lean_dec_ref(v_as_2614_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object* v_filterExport_2621_, uint8_t v_preserveOrder_2622_, lean_object* v_env_2623_, lean_object* v_x_2624_){
_start:
{
lean_object* v___y_2626_; 
if (v_preserveOrder_2622_ == 0)
{
lean_object* v_snd_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v_r_2645_; lean_object* v___x_2646_; lean_object* v___y_2648_; lean_object* v___y_2649_; uint8_t v___x_2651_; 
v_snd_2642_ = lean_ctor_get(v_x_2624_, 1);
lean_inc(v_snd_2642_);
lean_dec_ref(v_x_2624_);
v___x_2643_ = lean_unsigned_to_nat(0u);
v___x_2644_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v_r_2645_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_2644_, v_snd_2642_);
lean_dec(v_snd_2642_);
v___x_2646_ = lean_array_get_size(v_r_2645_);
v___x_2651_ = lean_nat_dec_eq(v___x_2646_, v___x_2643_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___y_2655_; uint8_t v___x_2657_; 
v___x_2652_ = lean_unsigned_to_nat(1u);
v___x_2653_ = lean_nat_sub(v___x_2646_, v___x_2652_);
v___x_2657_ = lean_nat_dec_le(v___x_2643_, v___x_2653_);
if (v___x_2657_ == 0)
{
lean_inc(v___x_2653_);
v___y_2655_ = v___x_2653_;
goto v___jp_2654_;
}
else
{
v___y_2655_ = v___x_2643_;
goto v___jp_2654_;
}
v___jp_2654_:
{
uint8_t v___x_2656_; 
v___x_2656_ = lean_nat_dec_le(v___y_2655_, v___x_2653_);
if (v___x_2656_ == 0)
{
lean_dec(v___x_2653_);
lean_inc(v___y_2655_);
v___y_2648_ = v___y_2655_;
v___y_2649_ = v___y_2655_;
goto v___jp_2647_;
}
else
{
v___y_2648_ = v___y_2655_;
v___y_2649_ = v___x_2653_;
goto v___jp_2647_;
}
}
}
else
{
v___y_2626_ = v_r_2645_;
goto v___jp_2625_;
}
v___jp_2647_:
{
lean_object* v___x_2650_; 
v___x_2650_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_2646_, v_r_2645_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2649_);
v___y_2626_ = v___x_2650_;
goto v___jp_2625_;
}
}
else
{
lean_object* v_fst_2658_; lean_object* v_snd_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v_fst_2658_ = lean_ctor_get(v_x_2624_, 0);
lean_inc(v_fst_2658_);
v_snd_2659_ = lean_ctor_get(v_x_2624_, 1);
lean_inc(v_snd_2659_);
lean_dec_ref(v_x_2624_);
v___x_2660_ = lean_array_mk(v_fst_2658_);
v___x_2661_ = l_Array_reverse___redArg(v___x_2660_);
v___x_2662_ = lean_unsigned_to_nat(0u);
v___x_2663_ = lean_array_get_size(v___x_2661_);
v___x_2664_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2659_, v___x_2661_, v___x_2662_, v___x_2663_);
lean_dec_ref(v___x_2661_);
lean_dec(v_snd_2659_);
v___y_2626_ = v___x_2664_;
goto v___jp_2625_;
}
v___jp_2625_:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; 
v___x_2627_ = lean_unsigned_to_nat(0u);
v___x_2628_ = lean_array_get_size(v___y_2626_);
v___x_2629_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2630_ = lean_nat_dec_lt(v___x_2627_, v___x_2628_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; 
lean_dec_ref(v_env_2623_);
lean_dec_ref(v_filterExport_2621_);
v___x_2631_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2629_);
lean_ctor_set(v___x_2631_, 1, v___x_2629_);
lean_ctor_set(v___x_2631_, 2, v___y_2626_);
return v___x_2631_;
}
else
{
uint8_t v___x_2632_; 
v___x_2632_ = lean_nat_dec_le(v___x_2628_, v___x_2628_);
if (v___x_2632_ == 0)
{
if (v___x_2630_ == 0)
{
lean_object* v___x_2633_; 
lean_dec_ref(v_env_2623_);
lean_dec_ref(v_filterExport_2621_);
v___x_2633_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2629_);
lean_ctor_set(v___x_2633_, 1, v___x_2629_);
lean_ctor_set(v___x_2633_, 2, v___y_2626_);
return v___x_2633_;
}
else
{
size_t v___x_2634_; size_t v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2634_ = ((size_t)0ULL);
v___x_2635_ = lean_usize_of_nat(v___x_2628_);
v___x_2636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2621_, v_env_2623_, v___y_2626_, v___x_2634_, v___x_2635_, v___x_2629_);
lean_inc_ref(v___x_2636_);
v___x_2637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
lean_ctor_set(v___x_2637_, 2, v___y_2626_);
return v___x_2637_;
}
}
else
{
size_t v___x_2638_; size_t v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2638_ = ((size_t)0ULL);
v___x_2639_ = lean_usize_of_nat(v___x_2628_);
v___x_2640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2621_, v_env_2623_, v___y_2626_, v___x_2638_, v___x_2639_, v___x_2629_);
lean_inc_ref(v___x_2640_);
v___x_2641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2640_);
lean_ctor_set(v___x_2641_, 1, v___x_2640_);
lean_ctor_set(v___x_2641_, 2, v___y_2626_);
return v___x_2641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object* v_filterExport_2665_, lean_object* v_preserveOrder_2666_, lean_object* v_env_2667_, lean_object* v_x_2668_){
_start:
{
uint8_t v_preserveOrder_boxed_2669_; lean_object* v_res_2670_; 
v_preserveOrder_boxed_2669_ = lean_unbox(v_preserveOrder_2666_);
v_res_2670_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2665_, v_preserveOrder_boxed_2669_, v_env_2667_, v_x_2668_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object* v_x_2680_){
_start:
{
lean_object* v_snd_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2695_; 
v_snd_2681_ = lean_ctor_get(v_x_2680_, 1);
v_isSharedCheck_2695_ = !lean_is_exclusive(v_x_2680_);
if (v_isSharedCheck_2695_ == 0)
{
lean_object* v_unused_2696_; 
v_unused_2696_ = lean_ctor_get(v_x_2680_, 0);
lean_dec(v_unused_2696_);
v___x_2683_ = v_x_2680_;
v_isShared_2684_ = v_isSharedCheck_2695_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_snd_2681_);
lean_dec(v_x_2680_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2695_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2685_; lean_object* v___y_2687_; 
v___x_2685_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2681_) == 0)
{
lean_object* v_size_2693_; 
v_size_2693_ = lean_ctor_get(v_snd_2681_, 0);
lean_inc(v_size_2693_);
lean_dec_ref_known(v_snd_2681_, 5);
v___y_2687_ = v_size_2693_;
goto v___jp_2686_;
}
else
{
lean_object* v___x_2694_; 
v___x_2694_ = lean_unsigned_to_nat(0u);
v___y_2687_ = v___x_2694_;
goto v___jp_2686_;
}
v___jp_2686_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2691_; 
v___x_2688_ = l_Nat_reprFast(v___y_2687_);
v___x_2689_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2688_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set_tag(v___x_2683_, 5);
lean_ctor_set(v___x_2683_, 1, v___x_2689_);
lean_ctor_set(v___x_2683_, 0, v___x_2685_);
v___x_2691_ = v___x_2683_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2685_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v___x_2689_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object* v_x_2697_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object* v_x_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_Lean_registerParametricAttributeExt___redArg___lam__3(v_x_2699_);
lean_dec_ref(v_x_2699_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object* v___x_2701_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object* v___x_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2704_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object* v___x_2707_, lean_object* v_x_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2707_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object* v___x_2712_, lean_object* v_x_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2712_, v_x_2713_, v___y_2714_);
lean_dec_ref(v___y_2714_);
lean_dec_ref(v_x_2713_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object* v_ref_2727_, uint8_t v_preserveOrder_2728_, lean_object* v_filterExport_2729_, uint8_t v_logWrites_2730_){
_start:
{
lean_object* v___f_2732_; lean_object* v___x_2733_; lean_object* v___f_2734_; lean_object* v___f_2735_; lean_object* v___f_2736_; lean_object* v___f_2737_; lean_object* v___f_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; uint8_t v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___f_2732_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__0));
v___x_2733_ = lean_box(v_preserveOrder_2728_);
v___f_2734_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2734_, 0, v_filterExport_2729_);
lean_closure_set(v___f_2734_, 1, v___x_2733_);
v___f_2735_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__1));
v___f_2736_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__2));
v___f_2737_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__4));
v___f_2738_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__5));
v___x_2739_ = lean_box(2);
v___x_2740_ = lean_box(0);
v___x_2741_ = 0;
v___x_2742_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2742_, 0, v_ref_2727_);
lean_ctor_set(v___x_2742_, 1, v___f_2737_);
lean_ctor_set(v___x_2742_, 2, v___f_2738_);
lean_ctor_set(v___x_2742_, 3, v___f_2732_);
lean_ctor_set(v___x_2742_, 4, v___f_2734_);
lean_ctor_set(v___x_2742_, 5, v___f_2735_);
lean_ctor_set(v___x_2742_, 6, v___x_2739_);
lean_ctor_set(v___x_2742_, 7, v___x_2740_);
lean_ctor_set_uint8(v___x_2742_, sizeof(void*)*8, v___x_2741_);
lean_ctor_set_uint8(v___x_2742_, sizeof(void*)*8 + 1, v_logWrites_2730_);
v___x_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2742_);
lean_ctor_set(v___x_2743_, 1, v___f_2736_);
v___x_2744_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2743_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object* v_ref_2745_, lean_object* v_preserveOrder_2746_, lean_object* v_filterExport_2747_, lean_object* v_logWrites_2748_, lean_object* v_a_2749_){
_start:
{
uint8_t v_preserveOrder_boxed_2750_; uint8_t v_logWrites_boxed_2751_; lean_object* v_res_2752_; 
v_preserveOrder_boxed_2750_ = lean_unbox(v_preserveOrder_2746_);
v_logWrites_boxed_2751_ = lean_unbox(v_logWrites_2748_);
v_res_2752_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2745_, v_preserveOrder_boxed_2750_, v_filterExport_2747_, v_logWrites_boxed_2751_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object* v_00_u03b1_2753_, lean_object* v_ref_2754_, uint8_t v_preserveOrder_2755_, lean_object* v_filterExport_2756_, uint8_t v_logWrites_2757_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2754_, v_preserveOrder_2755_, v_filterExport_2756_, v_logWrites_2757_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object* v_00_u03b1_2760_, lean_object* v_ref_2761_, lean_object* v_preserveOrder_2762_, lean_object* v_filterExport_2763_, lean_object* v_logWrites_2764_, lean_object* v_a_2765_){
_start:
{
uint8_t v_preserveOrder_boxed_2766_; uint8_t v_logWrites_boxed_2767_; lean_object* v_res_2768_; 
v_preserveOrder_boxed_2766_ = lean_unbox(v_preserveOrder_2762_);
v_logWrites_boxed_2767_ = lean_unbox(v_logWrites_2764_);
v_res_2768_ = l_Lean_registerParametricAttributeExt(v_00_u03b1_2760_, v_ref_2761_, v_preserveOrder_boxed_2766_, v_filterExport_2763_, v_logWrites_boxed_2767_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object* v_00_u03b1_2769_, lean_object* v_filterExport_2770_, lean_object* v_env_2771_, lean_object* v_as_2772_, size_t v_i_2773_, size_t v_stop_2774_, lean_object* v_b_2775_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2770_, v_env_2771_, v_as_2772_, v_i_2773_, v_stop_2774_, v_b_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object* v_00_u03b1_2777_, lean_object* v_filterExport_2778_, lean_object* v_env_2779_, lean_object* v_as_2780_, lean_object* v_i_2781_, lean_object* v_stop_2782_, lean_object* v_b_2783_){
_start:
{
size_t v_i_boxed_2784_; size_t v_stop_boxed_2785_; lean_object* v_res_2786_; 
v_i_boxed_2784_ = lean_unbox_usize(v_i_2781_);
lean_dec(v_i_2781_);
v_stop_boxed_2785_ = lean_unbox_usize(v_stop_2782_);
lean_dec(v_stop_2782_);
v_res_2786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(v_00_u03b1_2777_, v_filterExport_2778_, v_env_2779_, v_as_2780_, v_i_boxed_2784_, v_stop_boxed_2785_, v_b_2783_);
lean_dec_ref(v_as_2780_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object* v_init_2787_, lean_object* v_t_2788_){
_start:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2787_, v_t_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object* v_init_2790_, lean_object* v_t_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(v_init_2790_, v_t_2791_);
lean_dec(v_t_2791_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object* v_00_u03b1_2793_, lean_object* v_init_2794_, lean_object* v_t_2795_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2794_, v_t_2795_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object* v_00_u03b1_2797_, lean_object* v_init_2798_, lean_object* v_t_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(v_00_u03b1_2797_, v_init_2798_, v_t_2799_);
lean_dec(v_t_2799_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object* v_00_u03b1_2801_, lean_object* v_n_2802_, lean_object* v_as_2803_, lean_object* v_lo_2804_, lean_object* v_hi_2805_, lean_object* v_w_2806_, lean_object* v_hlo_2807_, lean_object* v_hhi_2808_){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2802_, v_as_2803_, v_lo_2804_, v_hi_2805_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object* v_00_u03b1_2810_, lean_object* v_n_2811_, lean_object* v_as_2812_, lean_object* v_lo_2813_, lean_object* v_hi_2814_, lean_object* v_w_2815_, lean_object* v_hlo_2816_, lean_object* v_hhi_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(v_00_u03b1_2810_, v_n_2811_, v_as_2812_, v_lo_2813_, v_hi_2814_, v_w_2815_, v_hlo_2816_, v_hhi_2817_);
lean_dec(v_hi_2814_);
lean_dec(v_n_2811_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object* v_00_u03b1_2819_, lean_object* v_snd_2820_, lean_object* v_as_2821_, lean_object* v_start_2822_, lean_object* v_stop_2823_){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2820_, v_as_2821_, v_start_2822_, v_stop_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object* v_00_u03b1_2825_, lean_object* v_snd_2826_, lean_object* v_as_2827_, lean_object* v_start_2828_, lean_object* v_stop_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(v_00_u03b1_2825_, v_snd_2826_, v_as_2827_, v_start_2828_, v_stop_2829_);
lean_dec(v_stop_2829_);
lean_dec(v_start_2828_);
lean_dec_ref(v_as_2827_);
lean_dec(v_snd_2826_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object* v_00_u03b1_2831_, lean_object* v_init_2832_, lean_object* v_x_2833_){
_start:
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2832_, v_x_2833_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2835_, lean_object* v_init_2836_, lean_object* v_x_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(v_00_u03b1_2835_, v_init_2836_, v_x_2837_);
lean_dec(v_x_2837_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object* v_00_u03b1_2839_, lean_object* v_n_2840_, lean_object* v_lo_2841_, lean_object* v_hi_2842_, lean_object* v_hhi_2843_, lean_object* v_pivot_2844_, lean_object* v_as_2845_, lean_object* v_i_2846_, lean_object* v_k_2847_, lean_object* v_ilo_2848_, lean_object* v_ik_2849_, lean_object* v_w_2850_){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2842_, v_pivot_2844_, v_as_2845_, v_i_2846_, v_k_2847_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2852_, lean_object* v_n_2853_, lean_object* v_lo_2854_, lean_object* v_hi_2855_, lean_object* v_hhi_2856_, lean_object* v_pivot_2857_, lean_object* v_as_2858_, lean_object* v_i_2859_, lean_object* v_k_2860_, lean_object* v_ilo_2861_, lean_object* v_ik_2862_, lean_object* v_w_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(v_00_u03b1_2852_, v_n_2853_, v_lo_2854_, v_hi_2855_, v_hhi_2856_, v_pivot_2857_, v_as_2858_, v_i_2859_, v_k_2860_, v_ilo_2861_, v_ik_2862_, v_w_2863_);
lean_dec_ref(v_pivot_2857_);
lean_dec(v_hi_2855_);
lean_dec(v_lo_2854_);
lean_dec(v_n_2853_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object* v_00_u03b1_2865_, lean_object* v_snd_2866_, lean_object* v_as_2867_, size_t v_i_2868_, size_t v_stop_2869_, lean_object* v_b_2870_){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2866_, v_as_2867_, v_i_2868_, v_stop_2869_, v_b_2870_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2872_, lean_object* v_snd_2873_, lean_object* v_as_2874_, lean_object* v_i_2875_, lean_object* v_stop_2876_, lean_object* v_b_2877_){
_start:
{
size_t v_i_boxed_2878_; size_t v_stop_boxed_2879_; lean_object* v_res_2880_; 
v_i_boxed_2878_ = lean_unbox_usize(v_i_2875_);
lean_dec(v_i_2875_);
v_stop_boxed_2879_ = lean_unbox_usize(v_stop_2876_);
lean_dec(v_stop_2876_);
v_res_2880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(v_00_u03b1_2872_, v_snd_2873_, v_as_2874_, v_i_boxed_2878_, v_stop_boxed_2879_, v_b_2877_);
lean_dec_ref(v_as_2874_);
lean_dec(v_snd_2873_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object* v_env_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v___x_2884_; lean_object* v_nextMacroScope_2885_; lean_object* v_ngen_2886_; lean_object* v_auxDeclNGen_2887_; lean_object* v_traceState_2888_; lean_object* v_recordedDeps_2889_; lean_object* v_messages_2890_; lean_object* v_infoState_2891_; lean_object* v_snapshotTasks_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2903_; 
v___x_2884_ = lean_st_ref_take(v___y_2882_);
v_nextMacroScope_2885_ = lean_ctor_get(v___x_2884_, 1);
v_ngen_2886_ = lean_ctor_get(v___x_2884_, 2);
v_auxDeclNGen_2887_ = lean_ctor_get(v___x_2884_, 3);
v_traceState_2888_ = lean_ctor_get(v___x_2884_, 4);
v_recordedDeps_2889_ = lean_ctor_get(v___x_2884_, 6);
v_messages_2890_ = lean_ctor_get(v___x_2884_, 7);
v_infoState_2891_ = lean_ctor_get(v___x_2884_, 8);
v_snapshotTasks_2892_ = lean_ctor_get(v___x_2884_, 9);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2903_ == 0)
{
lean_object* v_unused_2904_; lean_object* v_unused_2905_; 
v_unused_2904_ = lean_ctor_get(v___x_2884_, 5);
lean_dec(v_unused_2904_);
v_unused_2905_ = lean_ctor_get(v___x_2884_, 0);
lean_dec(v_unused_2905_);
v___x_2894_ = v___x_2884_;
v_isShared_2895_ = v_isSharedCheck_2903_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_snapshotTasks_2892_);
lean_inc(v_infoState_2891_);
lean_inc(v_messages_2890_);
lean_inc(v_recordedDeps_2889_);
lean_inc(v_traceState_2888_);
lean_inc(v_auxDeclNGen_2887_);
lean_inc(v_ngen_2886_);
lean_inc(v_nextMacroScope_2885_);
lean_dec(v___x_2884_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2903_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2899_; 
v___x_2896_ = lean_box(0);
v___x_2897_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 5, v___x_2897_);
lean_ctor_set(v___x_2894_, 0, v_env_2881_);
v___x_2899_ = v___x_2894_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_env_2881_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v_nextMacroScope_2885_);
lean_ctor_set(v_reuseFailAlloc_2902_, 2, v_ngen_2886_);
lean_ctor_set(v_reuseFailAlloc_2902_, 3, v_auxDeclNGen_2887_);
lean_ctor_set(v_reuseFailAlloc_2902_, 4, v_traceState_2888_);
lean_ctor_set(v_reuseFailAlloc_2902_, 5, v___x_2897_);
lean_ctor_set(v_reuseFailAlloc_2902_, 6, v_recordedDeps_2889_);
lean_ctor_set(v_reuseFailAlloc_2902_, 7, v_messages_2890_);
lean_ctor_set(v_reuseFailAlloc_2902_, 8, v_infoState_2891_);
lean_ctor_set(v_reuseFailAlloc_2902_, 9, v_snapshotTasks_2892_);
v___x_2899_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2900_ = lean_st_ref_put(v___y_2882_, v___x_2899_);
v___x_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2896_);
return v___x_2901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object* v_env_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2906_, v___y_2907_);
lean_dec(v___y_2907_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object* v_env_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2910_, v___y_2912_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object* v_env_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(v_env_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object* v_addEntryFn_2920_, lean_object* v___x_2921_, lean_object* v_s_2922_){
_start:
{
lean_object* v_importedEntries_2923_; lean_object* v_state_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2932_; 
v_importedEntries_2923_ = lean_ctor_get(v_s_2922_, 0);
v_state_2924_ = lean_ctor_get(v_s_2922_, 1);
v_isSharedCheck_2932_ = !lean_is_exclusive(v_s_2922_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2926_ = v_s_2922_;
v_isShared_2927_ = v_isSharedCheck_2932_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_state_2924_);
lean_inc(v_importedEntries_2923_);
lean_dec(v_s_2922_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2932_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v_state_2928_; lean_object* v___x_2930_; 
v_state_2928_ = lean_apply_2(v_addEntryFn_2920_, v_state_2924_, v___x_2921_);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 1, v_state_2928_);
v___x_2930_ = v___x_2926_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_importedEntries_2923_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_state_2928_);
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
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object* v_afterSet_2933_, lean_object* v_getParam_2934_, lean_object* v_ext_2935_, lean_object* v_toAttributeImplCore_2936_, lean_object* v_decl_2937_, lean_object* v_stx_2938_, uint8_t v_kind_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; uint8_t v___y_2947_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v_nextMacroScope_2954_; lean_object* v_ngen_2955_; lean_object* v_auxDeclNGen_2956_; lean_object* v_traceState_2957_; lean_object* v_recordedDeps_2958_; lean_object* v_messages_2959_; lean_object* v_infoState_2960_; lean_object* v_snapshotTasks_2961_; lean_object* v___y_2962_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; uint8_t v___x_3010_; uint8_t v___x_3011_; 
v___x_3010_ = 0;
v___x_3011_ = l_Lean_instBEqAttributeKind_beq(v_kind_2939_, v___x_3010_);
if (v___x_3011_ == 0)
{
lean_object* v_name_3012_; lean_object* v___x_3013_; 
lean_dec(v_stx_2938_);
lean_dec(v_decl_2937_);
lean_dec_ref(v_ext_2935_);
lean_dec_ref(v_getParam_2934_);
lean_dec_ref(v_afterSet_2933_);
v_name_3012_ = lean_ctor_get(v_toAttributeImplCore_2936_, 1);
lean_inc(v_name_3012_);
lean_dec_ref(v_toAttributeImplCore_2936_);
v___x_3013_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_3012_, v_kind_2939_, v___y_2940_, v___y_2941_);
return v___x_3013_;
}
else
{
goto v___jp_3004_;
}
v___jp_2943_:
{
if (v___y_2947_ == 0)
{
lean_object* v___x_2948_; 
lean_dec_ref(v___y_2946_);
v___x_2948_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v___y_2944_, v___y_2945_);
return v___x_2948_;
}
else
{
lean_dec_ref(v___y_2944_);
return v___y_2946_;
}
}
v___jp_2949_:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2963_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_2964_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2964_, 0, v___y_2962_);
lean_ctor_set(v___x_2964_, 1, v_nextMacroScope_2954_);
lean_ctor_set(v___x_2964_, 2, v_ngen_2955_);
lean_ctor_set(v___x_2964_, 3, v_auxDeclNGen_2956_);
lean_ctor_set(v___x_2964_, 4, v_traceState_2957_);
lean_ctor_set(v___x_2964_, 5, v___x_2963_);
lean_ctor_set(v___x_2964_, 6, v_recordedDeps_2958_);
lean_ctor_set(v___x_2964_, 7, v_messages_2959_);
lean_ctor_set(v___x_2964_, 8, v_infoState_2960_);
lean_ctor_set(v___x_2964_, 9, v_snapshotTasks_2961_);
v___x_2965_ = lean_st_ref_put(v___y_2952_, v___x_2964_);
lean_inc(v___y_2952_);
lean_inc_ref(v___y_2951_);
v___x_2966_ = lean_apply_5(v_afterSet_2933_, v_decl_2937_, v___y_2953_, v___y_2951_, v___y_2952_, lean_box(0));
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_dec_ref(v___y_2950_);
return v___x_2966_;
}
else
{
lean_object* v_a_2967_; uint8_t v___x_2968_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2967_);
v___x_2968_ = l_Lean_Exception_isInterrupt(v_a_2967_);
if (v___x_2968_ == 0)
{
uint8_t v___x_2969_; 
v___x_2969_ = l_Lean_Exception_isRuntime(v_a_2967_);
v___y_2944_ = v___y_2950_;
v___y_2945_ = v___y_2952_;
v___y_2946_ = v___x_2966_;
v___y_2947_ = v___x_2969_;
goto v___jp_2943_;
}
else
{
lean_dec(v_a_2967_);
v___y_2944_ = v___y_2950_;
v___y_2945_ = v___y_2952_;
v___y_2946_ = v___x_2966_;
v___y_2947_ = v___x_2968_;
goto v___jp_2943_;
}
}
}
v___jp_2970_:
{
lean_object* v___x_2974_; 
lean_inc(v___y_2973_);
lean_inc_ref(v___y_2972_);
lean_inc(v_decl_2937_);
v___x_2974_ = lean_apply_5(v_getParam_2934_, v_decl_2937_, v_stx_2938_, v___y_2972_, v___y_2973_, lean_box(0));
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; lean_object* v___x_2976_; lean_object* v_toEnvExtension_2977_; lean_object* v_env_2978_; lean_object* v_nextMacroScope_2979_; lean_object* v_ngen_2980_; lean_object* v_auxDeclNGen_2981_; lean_object* v_traceState_2982_; lean_object* v_recordedDeps_2983_; lean_object* v_messages_2984_; lean_object* v_infoState_2985_; lean_object* v_snapshotTasks_2986_; lean_object* v_addEntryFn_2987_; lean_object* v_asyncMode_2988_; uint8_t v_logWrites_2989_; lean_object* v___x_2990_; lean_object* v___f_2991_; uint8_t v___x_2992_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc_n(v_a_2975_, 2);
lean_dec_ref_known(v___x_2974_, 1);
v___x_2976_ = lean_st_ref_take(v___y_2973_);
v_toEnvExtension_2977_ = lean_ctor_get(v_ext_2935_, 0);
lean_inc_ref(v_toEnvExtension_2977_);
v_env_2978_ = lean_ctor_get(v___x_2976_, 0);
lean_inc_ref(v_env_2978_);
v_nextMacroScope_2979_ = lean_ctor_get(v___x_2976_, 1);
lean_inc(v_nextMacroScope_2979_);
v_ngen_2980_ = lean_ctor_get(v___x_2976_, 2);
lean_inc_ref(v_ngen_2980_);
v_auxDeclNGen_2981_ = lean_ctor_get(v___x_2976_, 3);
lean_inc_ref(v_auxDeclNGen_2981_);
v_traceState_2982_ = lean_ctor_get(v___x_2976_, 4);
lean_inc_ref(v_traceState_2982_);
v_recordedDeps_2983_ = lean_ctor_get(v___x_2976_, 6);
lean_inc_ref(v_recordedDeps_2983_);
v_messages_2984_ = lean_ctor_get(v___x_2976_, 7);
lean_inc_ref(v_messages_2984_);
v_infoState_2985_ = lean_ctor_get(v___x_2976_, 8);
lean_inc_ref(v_infoState_2985_);
v_snapshotTasks_2986_ = lean_ctor_get(v___x_2976_, 9);
lean_inc_ref(v_snapshotTasks_2986_);
lean_dec(v___x_2976_);
v_addEntryFn_2987_ = lean_ctor_get(v_ext_2935_, 3);
lean_inc(v_addEntryFn_2987_);
lean_dec_ref(v_ext_2935_);
v_asyncMode_2988_ = lean_ctor_get(v_toEnvExtension_2977_, 2);
lean_inc(v_asyncMode_2988_);
v_logWrites_2989_ = lean_ctor_get_uint8(v_toEnvExtension_2977_, sizeof(void*)*6);
lean_inc(v_decl_2937_);
v___x_2990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2990_, 0, v_decl_2937_);
lean_ctor_set(v___x_2990_, 1, v_a_2975_);
v___f_2991_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2991_, 0, v_addEntryFn_2987_);
lean_closure_set(v___f_2991_, 1, v___x_2990_);
v___x_2992_ = 1;
if (v_logWrites_2989_ == 0)
{
lean_object* v___x_2993_; 
lean_inc(v_decl_2937_);
v___x_2993_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2977_, v_env_2978_, v___f_2991_, v_asyncMode_2988_, v_decl_2937_, v___x_2992_);
lean_dec(v_asyncMode_2988_);
v___y_2950_ = v___y_2971_;
v___y_2951_ = v___y_2972_;
v___y_2952_ = v___y_2973_;
v___y_2953_ = v_a_2975_;
v_nextMacroScope_2954_ = v_nextMacroScope_2979_;
v_ngen_2955_ = v_ngen_2980_;
v_auxDeclNGen_2956_ = v_auxDeclNGen_2981_;
v_traceState_2957_ = v_traceState_2982_;
v_recordedDeps_2958_ = v_recordedDeps_2983_;
v_messages_2959_ = v_messages_2984_;
v_infoState_2960_ = v_infoState_2985_;
v_snapshotTasks_2961_ = v_snapshotTasks_2986_;
v___y_2962_ = v___x_2993_;
goto v___jp_2949_;
}
else
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
lean_inc_n(v_decl_2937_, 2);
v___x_2994_ = l_Lean_Environment_logDeclChange(v_env_2978_, v_decl_2937_);
v___x_2995_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2977_, v___x_2994_, v___f_2991_, v_asyncMode_2988_, v_decl_2937_, v___x_2992_);
lean_dec(v_asyncMode_2988_);
v___y_2950_ = v___y_2971_;
v___y_2951_ = v___y_2972_;
v___y_2952_ = v___y_2973_;
v___y_2953_ = v_a_2975_;
v_nextMacroScope_2954_ = v_nextMacroScope_2979_;
v_ngen_2955_ = v_ngen_2980_;
v_auxDeclNGen_2956_ = v_auxDeclNGen_2981_;
v_traceState_2957_ = v_traceState_2982_;
v_recordedDeps_2958_ = v_recordedDeps_2983_;
v_messages_2959_ = v_messages_2984_;
v_infoState_2960_ = v_infoState_2985_;
v_snapshotTasks_2961_ = v_snapshotTasks_2986_;
v___y_2962_ = v___x_2995_;
goto v___jp_2949_;
}
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec_ref(v___y_2971_);
lean_dec(v_decl_2937_);
lean_dec_ref(v_ext_2935_);
lean_dec_ref(v_afterSet_2933_);
v_a_2996_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2974_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2974_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
v___jp_3004_:
{
lean_object* v___x_3005_; lean_object* v_env_3006_; lean_object* v___x_3007_; 
v___x_3005_ = lean_st_ref_get(v___y_2941_);
v_env_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc_ref(v_env_3006_);
lean_dec(v___x_3005_);
v___x_3007_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3006_, v_decl_2937_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_dec_ref(v_toAttributeImplCore_2936_);
v___y_2971_ = v_env_3006_;
v___y_2972_ = v___y_2940_;
v___y_2973_ = v___y_2941_;
goto v___jp_2970_;
}
else
{
lean_object* v_name_3008_; lean_object* v___x_3009_; 
lean_dec_ref_known(v___x_3007_, 1);
lean_dec_ref(v_env_3006_);
lean_dec(v_stx_2938_);
lean_dec_ref(v_ext_2935_);
lean_dec_ref(v_getParam_2934_);
lean_dec_ref(v_afterSet_2933_);
v_name_3008_ = lean_ctor_get(v_toAttributeImplCore_2936_, 1);
lean_inc(v_name_3008_);
lean_dec_ref(v_toAttributeImplCore_2936_);
v___x_3009_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_3008_, v_decl_2937_, v___y_2940_, v___y_2941_);
return v___x_3009_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object* v_afterSet_3014_, lean_object* v_getParam_3015_, lean_object* v_ext_3016_, lean_object* v_toAttributeImplCore_3017_, lean_object* v_decl_3018_, lean_object* v_stx_3019_, lean_object* v_kind_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
uint8_t v_kind_boxed_3024_; lean_object* v_res_3025_; 
v_kind_boxed_3024_ = lean_unbox(v_kind_3020_);
v_res_3025_ = l_Lean_registerParametricAttributeForExt___redArg___lam__1(v_afterSet_3014_, v_getParam_3015_, v_ext_3016_, v_toAttributeImplCore_3017_, v_decl_3018_, v_stx_3019_, v_kind_boxed_3024_, v___y_3021_, v___y_3022_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__2(lean_object* v_toAttributeImplCore_3026_, lean_object* v_decl_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_name_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v_name_3031_ = lean_ctor_get(v_toAttributeImplCore_3026_, 1);
lean_inc(v_name_3031_);
lean_dec_ref(v_toAttributeImplCore_3026_);
v___x_3032_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3033_ = l_Lean_MessageData_ofName(v_name_3031_);
v___x_3034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3032_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
v___x_3035_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3034_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v___x_3037_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3036_, v___y_3028_, v___y_3029_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__2___boxed(lean_object* v_toAttributeImplCore_3038_, lean_object* v_decl_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lean_registerParametricAttributeForExt___redArg___lam__2(v_toAttributeImplCore_3038_, v_decl_3039_, v___y_3040_, v___y_3041_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v_decl_3039_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object* v_impl_3044_, lean_object* v_ext_3045_){
_start:
{
lean_object* v_toAttributeImplCore_3047_; lean_object* v_getParam_3048_; lean_object* v_afterSet_3049_; uint8_t v_preserveOrder_3050_; lean_object* v___f_3051_; lean_object* v___f_3052_; lean_object* v_attrImpl_3053_; lean_object* v___x_3054_; 
v_toAttributeImplCore_3047_ = lean_ctor_get(v_impl_3044_, 0);
lean_inc_ref_n(v_toAttributeImplCore_3047_, 3);
v_getParam_3048_ = lean_ctor_get(v_impl_3044_, 1);
lean_inc_ref(v_getParam_3048_);
v_afterSet_3049_ = lean_ctor_get(v_impl_3044_, 2);
lean_inc_ref(v_afterSet_3049_);
v_preserveOrder_3050_ = lean_ctor_get_uint8(v_impl_3044_, sizeof(void*)*4);
lean_dec_ref(v_impl_3044_);
lean_inc_ref(v_ext_3045_);
v___f_3051_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3051_, 0, v_afterSet_3049_);
lean_closure_set(v___f_3051_, 1, v_getParam_3048_);
lean_closure_set(v___f_3051_, 2, v_ext_3045_);
lean_closure_set(v___f_3051_, 3, v_toAttributeImplCore_3047_);
v___f_3052_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__2___boxed), 5, 1);
lean_closure_set(v___f_3052_, 0, v_toAttributeImplCore_3047_);
v_attrImpl_3053_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_attrImpl_3053_, 0, v_toAttributeImplCore_3047_);
lean_ctor_set(v_attrImpl_3053_, 1, v___f_3051_);
lean_ctor_set(v_attrImpl_3053_, 2, v___f_3052_);
lean_inc_ref(v_attrImpl_3053_);
v___x_3054_ = l_Lean_registerBuiltinAttribute(v_attrImpl_3053_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3062_; 
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3062_ == 0)
{
lean_object* v_unused_3063_; 
v_unused_3063_ = lean_ctor_get(v___x_3054_, 0);
lean_dec(v_unused_3063_);
v___x_3056_ = v___x_3054_;
v_isShared_3057_ = v_isSharedCheck_3062_;
goto v_resetjp_3055_;
}
else
{
lean_dec(v___x_3054_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3062_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3058_; lean_object* v___x_3060_; 
v___x_3058_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3058_, 0, v_attrImpl_3053_);
lean_ctor_set(v___x_3058_, 1, v_ext_3045_);
lean_ctor_set_uint8(v___x_3058_, sizeof(void*)*2, v_preserveOrder_3050_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 0, v___x_3058_);
v___x_3060_ = v___x_3056_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3058_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec_ref_known(v_attrImpl_3053_, 3);
lean_dec_ref(v_ext_3045_);
v_a_3064_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3054_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3054_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object* v_impl_3072_, lean_object* v_ext_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3072_, v_ext_3073_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object* v_00_u03b1_3076_, lean_object* v_impl_3077_, lean_object* v_ext_3078_){
_start:
{
lean_object* v___x_3080_; 
v___x_3080_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3077_, v_ext_3078_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object* v_00_u03b1_3081_, lean_object* v_impl_3082_, lean_object* v_ext_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Lean_registerParametricAttributeForExt(v_00_u03b1_3081_, v_impl_3082_, v_ext_3083_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_3086_){
_start:
{
lean_object* v_toAttributeImplCore_3088_; uint8_t v_preserveOrder_3089_; lean_object* v_filterExport_3090_; lean_object* v_ref_3091_; uint8_t v___x_3092_; lean_object* v___x_3093_; 
v_toAttributeImplCore_3088_ = lean_ctor_get(v_impl_3086_, 0);
v_preserveOrder_3089_ = lean_ctor_get_uint8(v_impl_3086_, sizeof(void*)*4);
v_filterExport_3090_ = lean_ctor_get(v_impl_3086_, 3);
v_ref_3091_ = lean_ctor_get(v_toAttributeImplCore_3088_, 0);
v___x_3092_ = 0;
lean_inc_ref(v_filterExport_3090_);
lean_inc(v_ref_3091_);
v___x_3093_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_3091_, v_preserveOrder_3089_, v_filterExport_3090_, v___x_3092_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v___x_3095_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_a_3094_);
lean_dec_ref_known(v___x_3093_, 1);
v___x_3095_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3086_, v_a_3094_);
return v___x_3095_;
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec_ref(v_impl_3086_);
v_a_3096_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3093_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3093_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_3104_, lean_object* v_a_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_Lean_registerParametricAttribute___redArg(v_impl_3104_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_3107_, lean_object* v_impl_3108_){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l_Lean_registerParametricAttribute___redArg(v_impl_3108_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_3111_, lean_object* v_impl_3112_, lean_object* v_a_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_Lean_registerParametricAttribute(v_00_u03b1_3111_, v_impl_3112_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(lean_object* v_decl_3115_, lean_object* v___x_3116_, lean_object* v___x_3117_, lean_object* v_a_3118_, lean_object* v_x_3119_, lean_object* v___y_3120_){
_start:
{
lean_object* v_fst_3121_; uint8_t v___x_3122_; 
v_fst_3121_ = lean_ctor_get(v_a_3118_, 0);
v___x_3122_ = lean_name_eq(v_fst_3121_, v_decl_3115_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; 
lean_dec_ref(v_a_3118_);
v___x_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3116_);
return v___x_3123_;
}
else
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
lean_dec_ref(v___x_3116_);
v___x_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3124_, 0, v_a_3118_);
v___x_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3124_);
v___x_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
lean_ctor_set(v___x_3126_, 1, v___x_3117_);
v___x_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3126_);
return v___x_3127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed(lean_object* v_decl_3128_, lean_object* v___x_3129_, lean_object* v___x_3130_, lean_object* v_a_3131_, lean_object* v_x_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(v_decl_3128_, v___x_3129_, v___x_3130_, v_a_3131_, v_x_3132_, v___y_3133_);
lean_dec_ref(v___y_3133_);
lean_dec(v_decl_3128_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object* v_inst_3162_, lean_object* v_ext_3163_, uint8_t v_preserveOrder_3164_, lean_object* v_env_3165_, lean_object* v_decl_3166_){
_start:
{
lean_object* v___y_3168_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3180_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3165_, v_decl_3166_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_toEnvExtension_3181_; lean_object* v_asyncMode_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; lean_object* v___x_3185_; lean_object* v_snd_3186_; lean_object* v___x_3187_; 
lean_dec(v_inst_3162_);
v_toEnvExtension_3181_ = lean_ctor_get(v_ext_3163_, 0);
v_asyncMode_3182_ = lean_ctor_get(v_toEnvExtension_3181_, 2);
v___x_3183_ = lean_box(0);
v___x_3184_ = 0;
v___x_3185_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3179_, v_ext_3163_, v_env_3165_, v_asyncMode_3182_, v___x_3183_, v___x_3184_);
v_snd_3186_ = lean_ctor_get(v___x_3185_, 1);
lean_inc(v_snd_3186_);
lean_dec(v___x_3185_);
v___x_3187_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3186_, v_decl_3166_);
lean_dec(v_decl_3166_);
lean_dec(v_snd_3186_);
return v___x_3187_;
}
else
{
if (v_preserveOrder_3164_ == 0)
{
lean_object* v_val_3188_; uint8_t v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; uint8_t v___x_3193_; 
v_val_3188_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_val_3188_);
lean_dec_ref_known(v___x_3180_, 1);
v___x_3189_ = 0;
v___x_3190_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3179_, v_ext_3163_, v_env_3165_, v_val_3188_, v___x_3189_);
lean_dec(v_val_3188_);
lean_dec_ref(v_env_3165_);
v___x_3191_ = lean_unsigned_to_nat(0u);
v___x_3192_ = lean_array_get_size(v___x_3190_);
v___x_3193_ = lean_nat_dec_lt(v___x_3191_, v___x_3192_);
if (v___x_3193_ == 0)
{
lean_object* v___x_3194_; 
lean_dec_ref(v___x_3190_);
lean_dec(v_decl_3166_);
lean_dec(v_inst_3162_);
v___x_3194_ = lean_box(0);
return v___x_3194_;
}
else
{
lean_object* v___x_3195_; lean_object* v___x_3196_; uint8_t v___x_3197_; 
v___x_3195_ = lean_unsigned_to_nat(1u);
v___x_3196_ = lean_nat_sub(v___x_3192_, v___x_3195_);
v___x_3197_ = lean_nat_dec_le(v___x_3191_, v___x_3196_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3198_; 
lean_dec(v___x_3196_);
lean_dec_ref(v___x_3190_);
lean_dec(v_decl_3166_);
lean_dec(v_inst_3162_);
v___x_3198_ = lean_box(0);
return v___x_3198_;
}
else
{
lean_object* v___f_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___f_3199_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
v___x_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3200_, 0, v_decl_3166_);
lean_ctor_set(v___x_3200_, 1, v_inst_3162_);
v___x_3201_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3202_ = l_Array_binSearchAux___redArg(v___f_3199_, v___x_3201_, v___x_3190_, v___x_3200_, v___x_3191_, v___x_3196_);
lean_dec_ref(v___x_3190_);
v___y_3168_ = v___x_3202_;
goto v___jp_3167_;
}
}
}
else
{
lean_object* v_val_3203_; uint8_t v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___f_3210_; size_t v_sz_3211_; size_t v___x_3212_; lean_object* v___x_3213_; lean_object* v_fst_3214_; 
lean_dec(v_inst_3162_);
v_val_3203_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_val_3203_);
lean_dec_ref_known(v___x_3180_, 1);
v___x_3204_ = 0;
v___x_3205_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3179_, v_ext_3163_, v_env_3165_, v_val_3203_, v___x_3204_);
lean_dec(v_val_3203_);
lean_dec_ref(v_env_3165_);
v___x_3206_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12));
v___x_3207_ = lean_box(0);
v___x_3208_ = lean_box(0);
v___x_3209_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13));
v___f_3210_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3210_, 0, v_decl_3166_);
lean_closure_set(v___f_3210_, 1, v___x_3209_);
lean_closure_set(v___f_3210_, 2, v___x_3208_);
v_sz_3211_ = lean_array_size(v___x_3205_);
v___x_3212_ = ((size_t)0ULL);
v___x_3213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3206_, v___x_3205_, v___f_3210_, v_sz_3211_, v___x_3212_, v___x_3209_);
v_fst_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_fst_3214_);
lean_dec(v___x_3213_);
if (lean_obj_tag(v_fst_3214_) == 0)
{
return v___x_3207_;
}
else
{
lean_object* v_val_3215_; 
v_val_3215_ = lean_ctor_get(v_fst_3214_, 0);
lean_inc(v_val_3215_);
lean_dec_ref_known(v_fst_3214_, 1);
v___y_3168_ = v_val_3215_;
goto v___jp_3167_;
}
}
}
v___jp_3167_:
{
if (lean_obj_tag(v___y_3168_) == 0)
{
lean_object* v___x_3169_; 
v___x_3169_ = lean_box(0);
return v___x_3169_;
}
else
{
lean_object* v_val_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3178_; 
v_val_3170_ = lean_ctor_get(v___y_3168_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___y_3168_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3172_ = v___y_3168_;
v_isShared_3173_ = v_isSharedCheck_3178_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_val_3170_);
lean_dec(v___y_3168_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3178_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v_snd_3174_; lean_object* v___x_3176_; 
v_snd_3174_ = lean_ctor_get(v_val_3170_, 1);
lean_inc(v_snd_3174_);
lean_dec(v_val_3170_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 0, v_snd_3174_);
v___x_3176_ = v___x_3172_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_snd_3174_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object* v_inst_3216_, lean_object* v_ext_3217_, lean_object* v_preserveOrder_3218_, lean_object* v_env_3219_, lean_object* v_decl_3220_){
_start:
{
uint8_t v_preserveOrder_boxed_3221_; lean_object* v_res_3222_; 
v_preserveOrder_boxed_3221_ = lean_unbox(v_preserveOrder_3218_);
v_res_3222_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3216_, v_ext_3217_, v_preserveOrder_boxed_3221_, v_env_3219_, v_decl_3220_);
lean_dec_ref(v_ext_3217_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object* v_00_u03b1_3223_, lean_object* v_inst_3224_, lean_object* v_ext_3225_, uint8_t v_preserveOrder_3226_, lean_object* v_env_3227_, lean_object* v_decl_3228_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3224_, v_ext_3225_, v_preserveOrder_3226_, v_env_3227_, v_decl_3228_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object* v_00_u03b1_3230_, lean_object* v_inst_3231_, lean_object* v_ext_3232_, lean_object* v_preserveOrder_3233_, lean_object* v_env_3234_, lean_object* v_decl_3235_){
_start:
{
uint8_t v_preserveOrder_boxed_3236_; lean_object* v_res_3237_; 
v_preserveOrder_boxed_3236_ = lean_unbox(v_preserveOrder_3233_);
v_res_3237_ = l_Lean_ParametricAttribute_getParamFromExt_x3f(v_00_u03b1_3230_, v_inst_3231_, v_ext_3232_, v_preserveOrder_boxed_3236_, v_env_3234_, v_decl_3235_);
lean_dec_ref(v_ext_3232_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3238_, lean_object* v_attr_3239_, lean_object* v_env_3240_, lean_object* v_decl_3241_){
_start:
{
lean_object* v_ext_3242_; uint8_t v_preserveOrder_3243_; lean_object* v___x_3244_; 
v_ext_3242_ = lean_ctor_get(v_attr_3239_, 1);
v_preserveOrder_3243_ = lean_ctor_get_uint8(v_attr_3239_, sizeof(void*)*2);
v___x_3244_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3238_, v_ext_3242_, v_preserveOrder_3243_, v_env_3240_, v_decl_3241_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3245_, lean_object* v_attr_3246_, lean_object* v_env_3247_, lean_object* v_decl_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3245_, v_attr_3246_, v_env_3247_, v_decl_3248_);
lean_dec_ref(v_attr_3246_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3250_, lean_object* v_inst_3251_, lean_object* v_attr_3252_, lean_object* v_env_3253_, lean_object* v_decl_3254_){
_start:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3251_, v_attr_3252_, v_env_3253_, v_decl_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3256_, lean_object* v_inst_3257_, lean_object* v_attr_3258_, lean_object* v_env_3259_, lean_object* v_decl_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3256_, v_inst_3257_, v_attr_3258_, v_env_3259_, v_decl_3260_);
lean_dec_ref(v_attr_3258_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object* v_ext_3266_, lean_object* v_attr_3267_, lean_object* v_env_3268_, lean_object* v_decl_3269_, lean_object* v_param_3270_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3268_, v_decl_3269_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_toEnvExtension_3272_; lean_object* v_addEntryFn_3273_; lean_object* v_asyncMode_3274_; uint8_t v_logWrites_3275_; uint8_t v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v_snd_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3315_; 
v_toEnvExtension_3272_ = lean_ctor_get(v_ext_3266_, 0);
lean_inc_ref(v_toEnvExtension_3272_);
v_addEntryFn_3273_ = lean_ctor_get(v_ext_3266_, 3);
lean_inc(v_addEntryFn_3273_);
v_asyncMode_3274_ = lean_ctor_get(v_toEnvExtension_3272_, 2);
lean_inc(v_asyncMode_3274_);
v_logWrites_3275_ = lean_ctor_get_uint8(v_toEnvExtension_3272_, sizeof(void*)*6);
v___x_3276_ = 0;
v___x_3277_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3278_ = lean_box(0);
lean_inc_ref(v_env_3268_);
v___x_3279_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3277_, v_ext_3266_, v_env_3268_, v_asyncMode_3274_, v___x_3278_, v___x_3276_);
lean_dec_ref(v_ext_3266_);
v_snd_3280_ = lean_ctor_get(v___x_3279_, 1);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3315_ == 0)
{
lean_object* v_unused_3316_; 
v_unused_3316_ = lean_ctor_get(v___x_3279_, 0);
lean_dec(v_unused_3316_);
v___x_3282_ = v___x_3279_;
v_isShared_3283_ = v_isSharedCheck_3315_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_snd_3280_);
lean_dec(v___x_3279_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3315_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3280_, v_decl_3269_);
lean_dec(v_snd_3280_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v___x_3286_; 
lean_dec_ref(v_attr_3267_);
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 1, v_param_3270_);
lean_ctor_set(v___x_3282_, 0, v_decl_3269_);
v___x_3286_ = v___x_3282_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_decl_3269_);
lean_ctor_set(v_reuseFailAlloc_3294_, 1, v_param_3270_);
v___x_3286_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
lean_object* v___f_3287_; uint8_t v___x_3288_; 
v___f_3287_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3287_, 0, v_addEntryFn_3273_);
lean_closure_set(v___f_3287_, 1, v___x_3286_);
v___x_3288_ = 1;
if (v_logWrites_3275_ == 0)
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3272_, v_env_3268_, v___f_3287_, v_asyncMode_3274_, v___x_3278_, v___x_3288_);
lean_dec(v_asyncMode_3274_);
v___x_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
return v___x_3290_;
}
else
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
lean_inc_ref(v_toEnvExtension_3272_);
v___x_3291_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3272_, v_env_3268_);
lean_dec_ref(v_env_3268_);
v___x_3292_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3272_, v___x_3291_, v___f_3287_, v_asyncMode_3274_, v___x_3278_, v___x_3288_);
lean_dec(v_asyncMode_3274_);
v___x_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
return v___x_3293_;
}
}
}
else
{
lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3313_; 
lean_del_object(v___x_3282_);
lean_dec(v_asyncMode_3274_);
lean_dec(v_addEntryFn_3273_);
lean_dec_ref(v_toEnvExtension_3272_);
lean_dec(v_param_3270_);
lean_dec_ref(v_env_3268_);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3313_ == 0)
{
lean_object* v_unused_3314_; 
v_unused_3314_ = lean_ctor_get(v___x_3284_, 0);
lean_dec(v_unused_3314_);
v___x_3296_ = v___x_3284_;
v_isShared_3297_ = v_isSharedCheck_3313_;
goto v_resetjp_3295_;
}
else
{
lean_dec(v___x_3284_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3313_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v_toAttributeImplCore_3298_; lean_object* v_name_3299_; uint8_t v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3311_; 
v_toAttributeImplCore_3298_ = lean_ctor_get(v_attr_3267_, 0);
lean_inc_ref(v_toAttributeImplCore_3298_);
lean_dec_ref(v_attr_3267_);
v_name_3299_ = lean_ctor_get(v_toAttributeImplCore_3298_, 1);
lean_inc(v_name_3299_);
lean_dec_ref(v_toAttributeImplCore_3298_);
v___x_3300_ = 1;
v___x_3301_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3302_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3299_, v___x_3300_);
v___x_3303_ = lean_string_append(v___x_3301_, v___x_3302_);
lean_dec_ref(v___x_3302_);
v___x_3304_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3305_ = lean_string_append(v___x_3303_, v___x_3304_);
v___x_3306_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3269_, v___x_3300_);
v___x_3307_ = lean_string_append(v___x_3305_, v___x_3306_);
lean_dec_ref(v___x_3306_);
v___x_3308_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2));
v___x_3309_ = lean_string_append(v___x_3307_, v___x_3308_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set_tag(v___x_3296_, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3309_);
v___x_3311_ = v___x_3296_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3309_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
}
else
{
lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3335_; 
lean_dec(v_param_3270_);
lean_dec_ref(v_env_3268_);
lean_dec_ref(v_ext_3266_);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3335_ == 0)
{
lean_object* v_unused_3336_; 
v_unused_3336_ = lean_ctor_get(v___x_3271_, 0);
lean_dec(v_unused_3336_);
v___x_3318_ = v___x_3271_;
v_isShared_3319_ = v_isSharedCheck_3335_;
goto v_resetjp_3317_;
}
else
{
lean_dec(v___x_3271_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3335_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v_toAttributeImplCore_3320_; lean_object* v_name_3321_; uint8_t v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3333_; 
v_toAttributeImplCore_3320_ = lean_ctor_get(v_attr_3267_, 0);
lean_inc_ref(v_toAttributeImplCore_3320_);
lean_dec_ref(v_attr_3267_);
v_name_3321_ = lean_ctor_get(v_toAttributeImplCore_3320_, 1);
lean_inc(v_name_3321_);
lean_dec_ref(v_toAttributeImplCore_3320_);
v___x_3322_ = 1;
v___x_3323_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3324_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3321_, v___x_3322_);
v___x_3325_ = lean_string_append(v___x_3323_, v___x_3324_);
lean_dec_ref(v___x_3324_);
v___x_3326_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3327_ = lean_string_append(v___x_3325_, v___x_3326_);
v___x_3328_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3269_, v___x_3322_);
v___x_3329_ = lean_string_append(v___x_3327_, v___x_3328_);
lean_dec_ref(v___x_3328_);
v___x_3330_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3));
v___x_3331_ = lean_string_append(v___x_3329_, v___x_3330_);
if (v_isShared_3319_ == 0)
{
lean_ctor_set_tag(v___x_3318_, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3331_);
v___x_3333_ = v___x_3318_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3331_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object* v_00_u03b1_3337_, lean_object* v_ext_3338_, lean_object* v_attr_3339_, lean_object* v_env_3340_, lean_object* v_decl_3341_, lean_object* v_param_3342_){
_start:
{
lean_object* v___x_3343_; 
v___x_3343_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3338_, v_attr_3339_, v_env_3340_, v_decl_3341_, v_param_3342_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3344_, lean_object* v_env_3345_, lean_object* v_decl_3346_, lean_object* v_param_3347_){
_start:
{
lean_object* v_attr_3348_; lean_object* v_ext_3349_; lean_object* v___x_3350_; 
v_attr_3348_ = lean_ctor_get(v_attr_3344_, 0);
lean_inc_ref(v_attr_3348_);
v_ext_3349_ = lean_ctor_get(v_attr_3344_, 1);
lean_inc_ref(v_ext_3349_);
lean_dec_ref(v_attr_3344_);
v___x_3350_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3349_, v_attr_3348_, v_env_3345_, v_decl_3346_, v_param_3347_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3351_, lean_object* v_attr_3352_, lean_object* v_env_3353_, lean_object* v_decl_3354_, lean_object* v_param_3355_){
_start:
{
lean_object* v___x_3356_; 
v___x_3356_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3352_, v_env_3353_, v_decl_3354_, v_param_3355_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(lean_object* v_x_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0___boxed(lean_object* v_x_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(v_x_3362_, v___y_3363_);
lean_dec_ref(v___y_3363_);
lean_dec_ref(v_x_3362_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(lean_object* v_s_3366_, lean_object* v_x_3367_){
_start:
{
lean_inc(v_s_3366_);
return v_s_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1___boxed(lean_object* v_s_3368_, lean_object* v_x_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(v_s_3368_, v_x_3369_);
lean_dec_ref(v_x_3369_);
lean_dec(v_s_3368_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(lean_object* v_x_3371_, lean_object* v_x_3372_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2___boxed(lean_object* v_x_3374_, lean_object* v_x_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(v_x_3374_, v_x_3375_);
lean_dec(v_x_3375_);
lean_dec_ref(v_x_3374_);
return v_res_3376_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3(void){
_start:
{
lean_object* v___f_3380_; lean_object* v___f_3381_; lean_object* v___f_3382_; lean_object* v___f_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___f_3380_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3381_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2));
v___f_3382_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1));
v___f_3383_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0));
v___x_3384_ = lean_box(0);
v___x_3385_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_3386_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
lean_ctor_set(v___x_3386_, 1, v___x_3384_);
lean_ctor_set(v___x_3386_, 2, v___f_3383_);
lean_ctor_set(v___x_3386_, 3, v___f_3382_);
lean_ctor_set(v___x_3386_, 4, v___f_3381_);
lean_ctor_set(v___x_3386_, 5, v___f_3380_);
return v___x_3386_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3387_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3);
v___x_3388_ = lean_box(0);
v___x_3389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3388_);
lean_ctor_set(v___x_3389_, 1, v___x_3387_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg(){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___boxed(lean_object* v___dummy_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v_res_3393_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__0(void){
_start:
{
lean_object* v___x_3394_; 
v___x_3394_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3395_){
_start:
{
lean_object* v___x_3396_; 
v___x_3396_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg(){
_start:
{
lean_object* v___x_3398_; 
v___x_3398_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg___boxed(lean_object* v___dummy_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l_Lean_instInhabitedEnumAttributes___redArg();
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3401_){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3402_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3403_; 
v___x_3403_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3404_){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3406_);
lean_dec(v_x_3406_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3408_, lean_object* v_x_3409_, lean_object* v_x_3410_){
_start:
{
if (lean_obj_tag(v_x_3410_) == 0)
{
return v_x_3409_;
}
else
{
lean_object* v_head_3411_; lean_object* v_tail_3412_; lean_object* v___x_3413_; 
v_head_3411_ = lean_ctor_get(v_x_3410_, 0);
lean_inc(v_head_3411_);
v_tail_3412_ = lean_ctor_get(v_x_3410_, 1);
lean_inc(v_tail_3412_);
lean_dec_ref_known(v_x_3410_, 2);
v___x_3413_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3408_, v_head_3411_);
if (lean_obj_tag(v___x_3413_) == 1)
{
lean_object* v_val_3414_; lean_object* v___x_3415_; 
v_val_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_val_3414_);
lean_dec_ref_known(v___x_3413_, 1);
v___x_3415_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3411_, v_val_3414_, v_x_3409_);
v_x_3409_ = v___x_3415_;
v_x_3410_ = v_tail_3412_;
goto _start;
}
else
{
lean_dec(v___x_3413_);
lean_dec(v_head_3411_);
v_x_3410_ = v_tail_3412_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3418_, lean_object* v_x_3419_, lean_object* v_x_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3418_, v_x_3419_, v_x_3420_);
lean_dec(v_newState_3418_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3422_, lean_object* v_newState_3423_, lean_object* v_consts_3424_, lean_object* v_st_3425_){
_start:
{
lean_object* v___x_3426_; 
v___x_3426_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3423_, v_st_3425_, v_consts_3424_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3427_, lean_object* v_newState_3428_, lean_object* v_consts_3429_, lean_object* v_st_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3427_, v_newState_3428_, v_consts_3429_, v_st_3430_);
lean_dec(v_newState_3428_);
lean_dec(v_x_3427_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3441_){
_start:
{
lean_object* v___x_3442_; lean_object* v___y_3444_; 
v___x_3442_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3441_) == 0)
{
lean_object* v_size_3448_; 
v_size_3448_ = lean_ctor_get(v_s_3441_, 0);
lean_inc(v_size_3448_);
lean_dec_ref_known(v_s_3441_, 5);
v___y_3444_ = v_size_3448_;
goto v___jp_3443_;
}
else
{
lean_object* v___x_3449_; 
v___x_3449_ = lean_unsigned_to_nat(0u);
v___y_3444_ = v___x_3449_;
goto v___jp_3443_;
}
v___jp_3443_:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3445_ = l_Nat_reprFast(v___y_3444_);
v___x_3446_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3445_);
v___x_3447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3442_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
return v___x_3447_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3450_, lean_object* v_as_3451_, size_t v_i_3452_, size_t v_stop_3453_, lean_object* v_b_3454_){
_start:
{
lean_object* v___y_3456_; uint8_t v___x_3460_; 
v___x_3460_ = lean_usize_dec_eq(v_i_3452_, v_stop_3453_);
if (v___x_3460_ == 0)
{
lean_object* v___x_3461_; lean_object* v_fst_3462_; uint8_t v___x_3463_; lean_object* v___x_3464_; uint8_t v___x_3465_; 
v___x_3461_ = lean_array_uget_borrowed(v_as_3451_, v_i_3452_);
v_fst_3462_ = lean_ctor_get(v___x_3461_, 0);
v___x_3463_ = 1;
lean_inc_ref(v_env_3450_);
v___x_3464_ = l_Lean_Environment_setExporting(v_env_3450_, v___x_3463_);
lean_inc(v_fst_3462_);
v___x_3465_ = l_Lean_Environment_contains(v___x_3464_, v_fst_3462_, v___x_3460_);
if (v___x_3465_ == 0)
{
v___y_3456_ = v_b_3454_;
goto v___jp_3455_;
}
else
{
lean_object* v___x_3466_; 
lean_inc(v___x_3461_);
v___x_3466_ = lean_array_push(v_b_3454_, v___x_3461_);
v___y_3456_ = v___x_3466_;
goto v___jp_3455_;
}
}
else
{
lean_dec_ref(v_env_3450_);
return v_b_3454_;
}
v___jp_3455_:
{
size_t v___x_3457_; size_t v___x_3458_; 
v___x_3457_ = ((size_t)1ULL);
v___x_3458_ = lean_usize_add(v_i_3452_, v___x_3457_);
v_i_3452_ = v___x_3458_;
v_b_3454_ = v___y_3456_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3467_, lean_object* v_as_3468_, lean_object* v_i_3469_, lean_object* v_stop_3470_, lean_object* v_b_3471_){
_start:
{
size_t v_i_boxed_3472_; size_t v_stop_boxed_3473_; lean_object* v_res_3474_; 
v_i_boxed_3472_ = lean_unbox_usize(v_i_3469_);
lean_dec(v_i_3469_);
v_stop_boxed_3473_ = lean_unbox_usize(v_stop_3470_);
lean_dec(v_stop_3470_);
v_res_3474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3467_, v_as_3468_, v_i_boxed_3472_, v_stop_boxed_3473_, v_b_3471_);
lean_dec_ref(v_as_3468_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3475_, lean_object* v_m_3476_){
_start:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___y_3480_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___y_3497_; lean_object* v___y_3498_; uint8_t v___x_3500_; 
v___x_3477_ = lean_unsigned_to_nat(0u);
v___x_3478_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_3494_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_3478_, v_m_3476_);
v___x_3495_ = lean_array_get_size(v___x_3494_);
v___x_3500_ = lean_nat_dec_eq(v___x_3495_, v___x_3477_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___y_3504_; uint8_t v___x_3506_; 
v___x_3501_ = lean_unsigned_to_nat(1u);
v___x_3502_ = lean_nat_sub(v___x_3495_, v___x_3501_);
v___x_3506_ = lean_nat_dec_le(v___x_3477_, v___x_3502_);
if (v___x_3506_ == 0)
{
lean_inc(v___x_3502_);
v___y_3504_ = v___x_3502_;
goto v___jp_3503_;
}
else
{
v___y_3504_ = v___x_3477_;
goto v___jp_3503_;
}
v___jp_3503_:
{
uint8_t v___x_3505_; 
v___x_3505_ = lean_nat_dec_le(v___y_3504_, v___x_3502_);
if (v___x_3505_ == 0)
{
lean_dec(v___x_3502_);
lean_inc(v___y_3504_);
v___y_3497_ = v___y_3504_;
v___y_3498_ = v___y_3504_;
goto v___jp_3496_;
}
else
{
v___y_3497_ = v___y_3504_;
v___y_3498_ = v___x_3502_;
goto v___jp_3496_;
}
}
}
else
{
v___y_3480_ = v___x_3494_;
goto v___jp_3479_;
}
v___jp_3479_:
{
lean_object* v___x_3481_; uint8_t v___x_3482_; 
v___x_3481_ = lean_array_get_size(v___y_3480_);
v___x_3482_ = lean_nat_dec_lt(v___x_3477_, v___x_3481_);
if (v___x_3482_ == 0)
{
lean_object* v___x_3483_; 
lean_dec_ref(v_env_3475_);
v___x_3483_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3478_);
lean_ctor_set(v___x_3483_, 1, v___x_3478_);
lean_ctor_set(v___x_3483_, 2, v___y_3480_);
return v___x_3483_;
}
else
{
uint8_t v___x_3484_; 
v___x_3484_ = lean_nat_dec_le(v___x_3481_, v___x_3481_);
if (v___x_3484_ == 0)
{
if (v___x_3482_ == 0)
{
lean_object* v___x_3485_; 
lean_dec_ref(v_env_3475_);
v___x_3485_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3478_);
lean_ctor_set(v___x_3485_, 1, v___x_3478_);
lean_ctor_set(v___x_3485_, 2, v___y_3480_);
return v___x_3485_;
}
else
{
size_t v___x_3486_; size_t v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3486_ = ((size_t)0ULL);
v___x_3487_ = lean_usize_of_nat(v___x_3481_);
v___x_3488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3475_, v___y_3480_, v___x_3486_, v___x_3487_, v___x_3478_);
lean_inc_ref(v___x_3488_);
v___x_3489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
lean_ctor_set(v___x_3489_, 1, v___x_3488_);
lean_ctor_set(v___x_3489_, 2, v___y_3480_);
return v___x_3489_;
}
}
else
{
size_t v___x_3490_; size_t v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3490_ = ((size_t)0ULL);
v___x_3491_ = lean_usize_of_nat(v___x_3481_);
v___x_3492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3475_, v___y_3480_, v___x_3490_, v___x_3491_, v___x_3478_);
lean_inc_ref(v___x_3492_);
v___x_3493_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3492_);
lean_ctor_set(v___x_3493_, 1, v___x_3492_);
lean_ctor_set(v___x_3493_, 2, v___y_3480_);
return v___x_3493_;
}
}
}
v___jp_3496_:
{
lean_object* v___x_3499_; 
v___x_3499_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_3495_, v___x_3494_, v___y_3497_, v___y_3498_);
lean_dec(v___y_3498_);
v___y_3480_ = v___x_3499_;
goto v___jp_3479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3507_, lean_object* v_m_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3507_, v_m_3508_);
lean_dec(v_m_3508_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3510_, lean_object* v_p_3511_){
_start:
{
lean_object* v_fst_3512_; lean_object* v_snd_3513_; lean_object* v___x_3514_; 
v_fst_3512_ = lean_ctor_get(v_p_3511_, 0);
lean_inc(v_fst_3512_);
v_snd_3513_ = lean_ctor_get(v_p_3511_, 1);
lean_inc(v_snd_3513_);
lean_dec_ref(v_p_3511_);
v___x_3514_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3512_, v_snd_3513_, v_s_3510_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3515_, lean_object* v_x_3516_, lean_object* v_x_3517_){
_start:
{
lean_object* v___x_3519_; 
v___x_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3515_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3520_, lean_object* v_x_3521_, lean_object* v_x_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3520_, v_x_3521_, v_x_3522_);
lean_dec_ref(v_x_3522_);
lean_dec_ref(v_x_3521_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3525_){
_start:
{
if (lean_obj_tag(v_as_3525_) == 0)
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3527_ = lean_box(0);
v___x_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3527_);
return v___x_3528_;
}
else
{
lean_object* v_head_3529_; lean_object* v_tail_3530_; lean_object* v___x_3531_; 
v_head_3529_ = lean_ctor_get(v_as_3525_, 0);
lean_inc(v_head_3529_);
v_tail_3530_ = lean_ctor_get(v_as_3525_, 1);
lean_inc(v_tail_3530_);
lean_dec_ref_known(v_as_3525_, 2);
v___x_3531_ = l_Lean_registerBuiltinAttribute(v_head_3529_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_dec_ref_known(v___x_3531_, 1);
v_as_3525_ = v_tail_3530_;
goto _start;
}
else
{
lean_dec(v_tail_3530_);
return v___x_3531_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3533_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_addEntryFn_3536_, lean_object* v___x_3537_, lean_object* v_s_3538_){
_start:
{
lean_object* v_importedEntries_3539_; lean_object* v_state_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3548_; 
v_importedEntries_3539_ = lean_ctor_get(v_s_3538_, 0);
v_state_3540_ = lean_ctor_get(v_s_3538_, 1);
v_isSharedCheck_3548_ = !lean_is_exclusive(v_s_3538_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3542_ = v_s_3538_;
v_isShared_3543_ = v_isSharedCheck_3548_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_state_3540_);
lean_inc(v_importedEntries_3539_);
lean_dec(v_s_3538_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3548_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v_state_3544_; lean_object* v___x_3546_; 
v_state_3544_ = lean_apply_2(v_addEntryFn_3536_, v_state_3540_, v___x_3537_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 1, v_state_3544_);
v___x_3546_ = v___x_3542_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_importedEntries_3539_);
lean_ctor_set(v_reuseFailAlloc_3547_, 1, v_state_3544_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2(lean_object* v_validate_3549_, lean_object* v_snd_3550_, lean_object* v_a_3551_, lean_object* v_fst_3552_, lean_object* v_decl_3553_, lean_object* v_stx_3554_, uint8_t v_kind_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
lean_object* v_nextMacroScope_3560_; lean_object* v_ngen_3561_; lean_object* v_auxDeclNGen_3562_; lean_object* v_traceState_3563_; lean_object* v_recordedDeps_3564_; lean_object* v_messages_3565_; lean_object* v_infoState_3566_; lean_object* v_snapshotTasks_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___x_3605_; 
v___x_3605_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3554_, v___y_3556_, v___y_3557_);
if (lean_obj_tag(v___x_3605_) == 0)
{
uint8_t v___x_3606_; uint8_t v___x_3607_; 
lean_dec_ref_known(v___x_3605_, 1);
v___x_3606_ = 0;
v___x_3607_ = l_Lean_instBEqAttributeKind_beq(v_kind_3555_, v___x_3606_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; 
lean_dec(v_decl_3553_);
lean_dec_ref(v_a_3551_);
lean_dec(v_snd_3550_);
lean_dec_ref(v_validate_3549_);
v___x_3608_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3552_, v_kind_3555_, v___y_3556_, v___y_3557_);
return v___x_3608_;
}
else
{
goto v___jp_3600_;
}
}
else
{
lean_dec(v_decl_3553_);
lean_dec(v_fst_3552_);
lean_dec_ref(v_a_3551_);
lean_dec(v_snd_3550_);
lean_dec_ref(v_validate_3549_);
return v___x_3605_;
}
v___jp_3559_:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3571_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_3572_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3572_, 0, v___y_3570_);
lean_ctor_set(v___x_3572_, 1, v_nextMacroScope_3560_);
lean_ctor_set(v___x_3572_, 2, v_ngen_3561_);
lean_ctor_set(v___x_3572_, 3, v_auxDeclNGen_3562_);
lean_ctor_set(v___x_3572_, 4, v_traceState_3563_);
lean_ctor_set(v___x_3572_, 5, v___x_3571_);
lean_ctor_set(v___x_3572_, 6, v_recordedDeps_3564_);
lean_ctor_set(v___x_3572_, 7, v_messages_3565_);
lean_ctor_set(v___x_3572_, 8, v_infoState_3566_);
lean_ctor_set(v___x_3572_, 9, v_snapshotTasks_3567_);
v___x_3573_ = lean_st_ref_put(v___y_3569_, v___x_3572_);
v___x_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3574_, 0, v___y_3568_);
return v___x_3574_;
}
v___jp_3575_:
{
lean_object* v___x_3578_; 
lean_inc(v___y_3577_);
lean_inc_ref(v___y_3576_);
lean_inc(v_snd_3550_);
lean_inc(v_decl_3553_);
v___x_3578_ = lean_apply_5(v_validate_3549_, v_decl_3553_, v_snd_3550_, v___y_3576_, v___y_3577_, lean_box(0));
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_object* v___x_3579_; lean_object* v_toEnvExtension_3580_; lean_object* v_env_3581_; lean_object* v_nextMacroScope_3582_; lean_object* v_ngen_3583_; lean_object* v_auxDeclNGen_3584_; lean_object* v_traceState_3585_; lean_object* v_recordedDeps_3586_; lean_object* v_messages_3587_; lean_object* v_infoState_3588_; lean_object* v_snapshotTasks_3589_; lean_object* v_addEntryFn_3590_; lean_object* v_asyncMode_3591_; uint8_t v_logWrites_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___f_3595_; uint8_t v___x_3596_; 
lean_dec_ref_known(v___x_3578_, 1);
v___x_3579_ = lean_st_ref_take(v___y_3577_);
v_toEnvExtension_3580_ = lean_ctor_get(v_a_3551_, 0);
lean_inc_ref(v_toEnvExtension_3580_);
v_env_3581_ = lean_ctor_get(v___x_3579_, 0);
lean_inc_ref(v_env_3581_);
v_nextMacroScope_3582_ = lean_ctor_get(v___x_3579_, 1);
lean_inc(v_nextMacroScope_3582_);
v_ngen_3583_ = lean_ctor_get(v___x_3579_, 2);
lean_inc_ref(v_ngen_3583_);
v_auxDeclNGen_3584_ = lean_ctor_get(v___x_3579_, 3);
lean_inc_ref(v_auxDeclNGen_3584_);
v_traceState_3585_ = lean_ctor_get(v___x_3579_, 4);
lean_inc_ref(v_traceState_3585_);
v_recordedDeps_3586_ = lean_ctor_get(v___x_3579_, 6);
lean_inc_ref(v_recordedDeps_3586_);
v_messages_3587_ = lean_ctor_get(v___x_3579_, 7);
lean_inc_ref(v_messages_3587_);
v_infoState_3588_ = lean_ctor_get(v___x_3579_, 8);
lean_inc_ref(v_infoState_3588_);
v_snapshotTasks_3589_ = lean_ctor_get(v___x_3579_, 9);
lean_inc_ref(v_snapshotTasks_3589_);
lean_dec(v___x_3579_);
v_addEntryFn_3590_ = lean_ctor_get(v_a_3551_, 3);
lean_inc(v_addEntryFn_3590_);
lean_dec_ref(v_a_3551_);
v_asyncMode_3591_ = lean_ctor_get(v_toEnvExtension_3580_, 2);
lean_inc(v_asyncMode_3591_);
v_logWrites_3592_ = lean_ctor_get_uint8(v_toEnvExtension_3580_, sizeof(void*)*6);
v___x_3593_ = lean_box(0);
lean_inc(v_decl_3553_);
v___x_3594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3594_, 0, v_decl_3553_);
lean_ctor_set(v___x_3594_, 1, v_snd_3550_);
v___f_3595_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3595_, 0, v_addEntryFn_3590_);
lean_closure_set(v___f_3595_, 1, v___x_3594_);
v___x_3596_ = 1;
if (v_logWrites_3592_ == 0)
{
lean_object* v___x_3597_; 
v___x_3597_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3580_, v_env_3581_, v___f_3595_, v_asyncMode_3591_, v_decl_3553_, v___x_3596_);
lean_dec(v_asyncMode_3591_);
v_nextMacroScope_3560_ = v_nextMacroScope_3582_;
v_ngen_3561_ = v_ngen_3583_;
v_auxDeclNGen_3562_ = v_auxDeclNGen_3584_;
v_traceState_3563_ = v_traceState_3585_;
v_recordedDeps_3564_ = v_recordedDeps_3586_;
v_messages_3565_ = v_messages_3587_;
v_infoState_3566_ = v_infoState_3588_;
v_snapshotTasks_3567_ = v_snapshotTasks_3589_;
v___y_3568_ = v___x_3593_;
v___y_3569_ = v___y_3577_;
v___y_3570_ = v___x_3597_;
goto v___jp_3559_;
}
else
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
lean_inc_ref(v_toEnvExtension_3580_);
v___x_3598_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3580_, v_env_3581_);
lean_dec_ref(v_env_3581_);
v___x_3599_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3580_, v___x_3598_, v___f_3595_, v_asyncMode_3591_, v_decl_3553_, v___x_3596_);
lean_dec(v_asyncMode_3591_);
v_nextMacroScope_3560_ = v_nextMacroScope_3582_;
v_ngen_3561_ = v_ngen_3583_;
v_auxDeclNGen_3562_ = v_auxDeclNGen_3584_;
v_traceState_3563_ = v_traceState_3585_;
v_recordedDeps_3564_ = v_recordedDeps_3586_;
v_messages_3565_ = v_messages_3587_;
v_infoState_3566_ = v_infoState_3588_;
v_snapshotTasks_3567_ = v_snapshotTasks_3589_;
v___y_3568_ = v___x_3593_;
v___y_3569_ = v___y_3577_;
v___y_3570_ = v___x_3599_;
goto v___jp_3559_;
}
}
else
{
lean_dec(v_decl_3553_);
lean_dec_ref(v_a_3551_);
lean_dec(v_snd_3550_);
return v___x_3578_;
}
}
v___jp_3600_:
{
lean_object* v___x_3601_; lean_object* v_env_3602_; lean_object* v___x_3603_; 
v___x_3601_ = lean_st_ref_get(v___y_3557_);
v_env_3602_ = lean_ctor_get(v___x_3601_, 0);
lean_inc_ref(v_env_3602_);
lean_dec(v___x_3601_);
v___x_3603_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3602_, v_decl_3553_);
lean_dec_ref(v_env_3602_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_dec(v_fst_3552_);
v___y_3576_ = v___y_3556_;
v___y_3577_ = v___y_3557_;
goto v___jp_3575_;
}
else
{
lean_object* v___x_3604_; 
lean_dec_ref_known(v___x_3603_, 1);
lean_dec_ref(v_a_3551_);
lean_dec(v_snd_3550_);
lean_dec_ref(v_validate_3549_);
v___x_3604_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3552_, v_decl_3553_, v___y_3556_, v___y_3557_);
return v___x_3604_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2___boxed(lean_object* v_validate_3609_, lean_object* v_snd_3610_, lean_object* v_a_3611_, lean_object* v_fst_3612_, lean_object* v_decl_3613_, lean_object* v_stx_3614_, lean_object* v_kind_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
uint8_t v_kind_boxed_3619_; lean_object* v_res_3620_; 
v_kind_boxed_3619_ = lean_unbox(v_kind_3615_);
v_res_3620_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2(v_validate_3609_, v_snd_3610_, v_a_3611_, v_fst_3612_, v_decl_3613_, v_stx_3614_, v_kind_boxed_3619_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3621_, lean_object* v_decl_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3626_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3627_ = l_Lean_MessageData_ofName(v_fst_3621_);
v___x_3628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3626_);
lean_ctor_set(v___x_3628_, 1, v___x_3627_);
v___x_3629_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3628_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
v___x_3631_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3630_, v___y_3623_, v___y_3624_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3632_, lean_object* v_decl_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3632_, v_decl_3633_, v___y_3634_, v___y_3635_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v_decl_3633_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3638_, lean_object* v_a_3639_, lean_object* v_ref_3640_, uint8_t v_applicationTime_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_){
_start:
{
if (lean_obj_tag(v_a_3642_) == 0)
{
lean_object* v___x_3644_; 
lean_dec(v_ref_3640_);
lean_dec_ref(v_a_3639_);
lean_dec_ref(v_validate_3638_);
v___x_3644_ = l_List_reverse___redArg(v_a_3643_);
return v___x_3644_;
}
else
{
lean_object* v_head_3645_; lean_object* v_snd_3646_; lean_object* v_tail_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3662_; 
v_head_3645_ = lean_ctor_get(v_a_3642_, 0);
lean_inc(v_head_3645_);
v_snd_3646_ = lean_ctor_get(v_head_3645_, 1);
lean_inc(v_snd_3646_);
v_tail_3647_ = lean_ctor_get(v_a_3642_, 1);
v_isSharedCheck_3662_ = !lean_is_exclusive(v_a_3642_);
if (v_isSharedCheck_3662_ == 0)
{
lean_object* v_unused_3663_; 
v_unused_3663_ = lean_ctor_get(v_a_3642_, 0);
lean_dec(v_unused_3663_);
v___x_3649_ = v_a_3642_;
v_isShared_3650_ = v_isSharedCheck_3662_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_tail_3647_);
lean_dec(v_a_3642_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3662_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v_fst_3651_; lean_object* v_fst_3652_; lean_object* v_snd_3653_; lean_object* v___f_3654_; lean_object* v___f_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3659_; 
v_fst_3651_ = lean_ctor_get(v_head_3645_, 0);
lean_inc_n(v_fst_3651_, 3);
lean_dec(v_head_3645_);
v_fst_3652_ = lean_ctor_get(v_snd_3646_, 0);
lean_inc(v_fst_3652_);
v_snd_3653_ = lean_ctor_get(v_snd_3646_, 1);
lean_inc(v_snd_3653_);
lean_dec(v_snd_3646_);
v___f_3654_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3654_, 0, v_fst_3651_);
lean_inc_ref(v_a_3639_);
lean_inc_ref(v_validate_3638_);
v___f_3655_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2___boxed), 10, 4);
lean_closure_set(v___f_3655_, 0, v_validate_3638_);
lean_closure_set(v___f_3655_, 1, v_snd_3653_);
lean_closure_set(v___f_3655_, 2, v_a_3639_);
lean_closure_set(v___f_3655_, 3, v_fst_3651_);
lean_inc(v_ref_3640_);
v___x_3656_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3656_, 0, v_ref_3640_);
lean_ctor_set(v___x_3656_, 1, v_fst_3651_);
lean_ctor_set(v___x_3656_, 2, v_fst_3652_);
lean_ctor_set_uint8(v___x_3656_, sizeof(void*)*3, v_applicationTime_3641_);
v___x_3657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3656_);
lean_ctor_set(v___x_3657_, 1, v___f_3655_);
lean_ctor_set(v___x_3657_, 2, v___f_3654_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 1, v_a_3643_);
lean_ctor_set(v___x_3649_, 0, v___x_3657_);
v___x_3659_ = v___x_3649_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3657_);
lean_ctor_set(v_reuseFailAlloc_3661_, 1, v_a_3643_);
v___x_3659_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
v_a_3642_ = v_tail_3647_;
v_a_3643_ = v___x_3659_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3664_, lean_object* v_a_3665_, lean_object* v_ref_3666_, lean_object* v_applicationTime_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_){
_start:
{
uint8_t v_applicationTime_boxed_3670_; lean_object* v_res_3671_; 
v_applicationTime_boxed_3670_ = lean_unbox(v_applicationTime_3667_);
v_res_3671_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3664_, v_a_3665_, v_ref_3666_, v_applicationTime_boxed_3670_, v_a_3668_, v_a_3669_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3685_, lean_object* v_validate_3686_, uint8_t v_applicationTime_3687_, lean_object* v_ref_3688_){
_start:
{
lean_object* v___f_3690_; lean_object* v___f_3691_; lean_object* v___f_3692_; lean_object* v___f_3693_; lean_object* v___f_3694_; lean_object* v___f_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; uint8_t v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___f_3690_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3691_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3692_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3693_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3694_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3695_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3696_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3697_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
v___x_3698_ = 0;
lean_inc(v_ref_3688_);
v___x_3699_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_3699_, 0, v_ref_3688_);
lean_ctor_set(v___x_3699_, 1, v___f_3694_);
lean_ctor_set(v___x_3699_, 2, v___f_3695_);
lean_ctor_set(v___x_3699_, 3, v___f_3693_);
lean_ctor_set(v___x_3699_, 4, v___f_3692_);
lean_ctor_set(v___x_3699_, 5, v___f_3691_);
lean_ctor_set(v___x_3699_, 6, v___x_3696_);
lean_ctor_set(v___x_3699_, 7, v___x_3697_);
lean_ctor_set_uint8(v___x_3699_, sizeof(void*)*8, v___x_3698_);
lean_ctor_set_uint8(v___x_3699_, sizeof(void*)*8 + 1, v___x_3698_);
v___x_3700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3699_);
lean_ctor_set(v___x_3700_, 1, v___f_3690_);
v___x_3701_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3700_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
lean_inc_n(v_a_3702_, 2);
lean_dec_ref_known(v___x_3701_, 1);
v___x_3703_ = lean_box(0);
v___x_3704_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3686_, v_a_3702_, v_ref_3688_, v_applicationTime_3687_, v_attrDescrs_3685_, v___x_3703_);
lean_inc(v___x_3704_);
v___x_3705_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3704_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3713_; 
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3713_ == 0)
{
lean_object* v_unused_3714_; 
v_unused_3714_ = lean_ctor_get(v___x_3705_, 0);
lean_dec(v_unused_3714_);
v___x_3707_ = v___x_3705_;
v_isShared_3708_ = v_isSharedCheck_3713_;
goto v_resetjp_3706_;
}
else
{
lean_dec(v___x_3705_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3713_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
lean_object* v___x_3709_; lean_object* v___x_3711_; 
v___x_3709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3704_);
lean_ctor_set(v___x_3709_, 1, v_a_3702_);
if (v_isShared_3708_ == 0)
{
lean_ctor_set(v___x_3707_, 0, v___x_3709_);
v___x_3711_ = v___x_3707_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3709_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
else
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
lean_dec(v___x_3704_);
lean_dec(v_a_3702_);
v_a_3715_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3705_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3705_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_dec(v_ref_3688_);
lean_dec_ref(v_validate_3686_);
lean_dec(v_attrDescrs_3685_);
v_a_3723_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3701_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3701_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3731_, lean_object* v_validate_3732_, lean_object* v_applicationTime_3733_, lean_object* v_ref_3734_, lean_object* v_a_3735_){
_start:
{
uint8_t v_applicationTime_boxed_3736_; lean_object* v_res_3737_; 
v_applicationTime_boxed_3736_ = lean_unbox(v_applicationTime_3733_);
v_res_3737_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3731_, v_validate_3732_, v_applicationTime_boxed_3736_, v_ref_3734_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3738_, lean_object* v_attrDescrs_3739_, lean_object* v_validate_3740_, uint8_t v_applicationTime_3741_, lean_object* v_ref_3742_){
_start:
{
lean_object* v___x_3744_; 
v___x_3744_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3739_, v_validate_3740_, v_applicationTime_3741_, v_ref_3742_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3745_, lean_object* v_attrDescrs_3746_, lean_object* v_validate_3747_, lean_object* v_applicationTime_3748_, lean_object* v_ref_3749_, lean_object* v_a_3750_){
_start:
{
uint8_t v_applicationTime_boxed_3751_; lean_object* v_res_3752_; 
v_applicationTime_boxed_3751_ = lean_unbox(v_applicationTime_3748_);
v_res_3752_ = l_Lean_registerEnumAttributes(v_00_u03b1_3745_, v_attrDescrs_3746_, v_validate_3747_, v_applicationTime_boxed_3751_, v_ref_3749_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3753_, lean_object* v_env_3754_, lean_object* v_as_3755_, size_t v_i_3756_, size_t v_stop_3757_, lean_object* v_b_3758_){
_start:
{
lean_object* v___x_3759_; 
v___x_3759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3754_, v_as_3755_, v_i_3756_, v_stop_3757_, v_b_3758_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3760_, lean_object* v_env_3761_, lean_object* v_as_3762_, lean_object* v_i_3763_, lean_object* v_stop_3764_, lean_object* v_b_3765_){
_start:
{
size_t v_i_boxed_3766_; size_t v_stop_boxed_3767_; lean_object* v_res_3768_; 
v_i_boxed_3766_ = lean_unbox_usize(v_i_3763_);
lean_dec(v_i_3763_);
v_stop_boxed_3767_ = lean_unbox_usize(v_stop_3764_);
lean_dec(v_stop_3764_);
v_res_3768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3760_, v_env_3761_, v_as_3762_, v_i_boxed_3766_, v_stop_boxed_3767_, v_b_3765_);
lean_dec_ref(v_as_3762_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3769_, lean_object* v_newState_3770_, lean_object* v_x_3771_, lean_object* v_x_3772_){
_start:
{
lean_object* v___x_3773_; 
v___x_3773_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3770_, v_x_3771_, v_x_3772_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3774_, lean_object* v_newState_3775_, lean_object* v_x_3776_, lean_object* v_x_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3774_, v_newState_3775_, v_x_3776_, v_x_3777_);
lean_dec(v_newState_3775_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3779_, lean_object* v_validate_3780_, lean_object* v_a_3781_, lean_object* v_ref_3782_, uint8_t v_applicationTime_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3780_, v_a_3781_, v_ref_3782_, v_applicationTime_3783_, v_a_3784_, v_a_3785_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3787_, lean_object* v_validate_3788_, lean_object* v_a_3789_, lean_object* v_ref_3790_, lean_object* v_applicationTime_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_){
_start:
{
uint8_t v_applicationTime_boxed_3794_; lean_object* v_res_3795_; 
v_applicationTime_boxed_3794_ = lean_unbox(v_applicationTime_3791_);
v_res_3795_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3787_, v_validate_3788_, v_a_3789_, v_ref_3790_, v_applicationTime_boxed_3794_, v_a_3792_, v_a_3793_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3796_, lean_object* v_attr_3797_, lean_object* v_env_3798_, lean_object* v_decl_3799_){
_start:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3800_ = lean_box(1);
v___x_3801_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3798_, v_decl_3799_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_ext_3802_; lean_object* v_toEnvExtension_3803_; lean_object* v_asyncMode_3804_; uint8_t v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; 
lean_dec(v_inst_3796_);
v_ext_3802_ = lean_ctor_get(v_attr_3797_, 1);
lean_inc_ref(v_ext_3802_);
lean_dec_ref(v_attr_3797_);
v_toEnvExtension_3803_ = lean_ctor_get(v_ext_3802_, 0);
v_asyncMode_3804_ = lean_ctor_get(v_toEnvExtension_3803_, 2);
lean_inc(v_asyncMode_3804_);
v___x_3805_ = 0;
lean_inc(v_decl_3799_);
v___x_3806_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3800_, v_ext_3802_, v_env_3798_, v_asyncMode_3804_, v_decl_3799_, v___x_3805_);
lean_dec(v_asyncMode_3804_);
lean_dec_ref(v_ext_3802_);
v___x_3807_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3806_, v_decl_3799_);
lean_dec(v_decl_3799_);
lean_dec(v___x_3806_);
return v___x_3807_;
}
else
{
lean_object* v_val_3808_; lean_object* v_ext_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3839_; 
v_val_3808_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_val_3808_);
lean_dec_ref_known(v___x_3801_, 1);
v_ext_3809_ = lean_ctor_get(v_attr_3797_, 1);
v_isSharedCheck_3839_ = !lean_is_exclusive(v_attr_3797_);
if (v_isSharedCheck_3839_ == 0)
{
lean_object* v_unused_3840_; 
v_unused_3840_ = lean_ctor_get(v_attr_3797_, 0);
lean_dec(v_unused_3840_);
v___x_3811_ = v_attr_3797_;
v_isShared_3812_ = v_isSharedCheck_3839_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_ext_3809_);
lean_dec(v_attr_3797_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3839_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
uint8_t v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; 
v___x_3813_ = 0;
v___x_3814_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3800_, v_ext_3809_, v_env_3798_, v_val_3808_, v___x_3813_);
lean_dec(v_val_3808_);
lean_dec_ref(v_env_3798_);
lean_dec_ref(v_ext_3809_);
v___x_3815_ = lean_unsigned_to_nat(0u);
v___x_3816_ = lean_array_get_size(v___x_3814_);
v___x_3817_ = lean_nat_dec_lt(v___x_3815_, v___x_3816_);
if (v___x_3817_ == 0)
{
lean_object* v___x_3818_; 
lean_dec_ref(v___x_3814_);
lean_del_object(v___x_3811_);
lean_dec(v_decl_3799_);
lean_dec(v_inst_3796_);
v___x_3818_ = lean_box(0);
return v___x_3818_;
}
else
{
lean_object* v___x_3819_; lean_object* v___x_3820_; uint8_t v___x_3821_; 
v___x_3819_ = lean_unsigned_to_nat(1u);
v___x_3820_ = lean_nat_sub(v___x_3816_, v___x_3819_);
v___x_3821_ = lean_nat_dec_le(v___x_3815_, v___x_3820_);
if (v___x_3821_ == 0)
{
lean_object* v___x_3822_; 
lean_dec(v___x_3820_);
lean_dec_ref(v___x_3814_);
lean_del_object(v___x_3811_);
lean_dec(v_decl_3799_);
lean_dec(v_inst_3796_);
v___x_3822_ = lean_box(0);
return v___x_3822_;
}
else
{
lean_object* v___f_3823_; lean_object* v___x_3825_; 
v___f_3823_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 1, v_inst_3796_);
lean_ctor_set(v___x_3811_, 0, v_decl_3799_);
v___x_3825_ = v___x_3811_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_decl_3799_);
lean_ctor_set(v_reuseFailAlloc_3838_, 1, v_inst_3796_);
v___x_3825_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3826_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3827_ = l_Array_binSearchAux___redArg(v___f_3823_, v___x_3826_, v___x_3814_, v___x_3825_, v___x_3815_, v___x_3820_);
lean_dec_ref(v___x_3814_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v___x_3828_; 
v___x_3828_ = lean_box(0);
return v___x_3828_;
}
else
{
lean_object* v_val_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3837_; 
v_val_3829_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3831_ = v___x_3827_;
v_isShared_3832_ = v_isSharedCheck_3837_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_val_3829_);
lean_dec(v___x_3827_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3837_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v_snd_3833_; lean_object* v___x_3835_; 
v_snd_3833_ = lean_ctor_get(v_val_3829_, 1);
lean_inc(v_snd_3833_);
lean_dec(v_val_3829_);
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 0, v_snd_3833_);
v___x_3835_ = v___x_3831_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_snd_3833_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3841_, lean_object* v_inst_3842_, lean_object* v_attr_3843_, lean_object* v_env_3844_, lean_object* v_decl_3845_){
_start:
{
lean_object* v___x_3846_; 
v___x_3846_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3842_, v_attr_3843_, v_env_3844_, v_decl_3845_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3855_, lean_object* v_env_3856_, lean_object* v_decl_3857_, lean_object* v_val_3858_){
_start:
{
lean_object* v_ext_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3929_; 
v_ext_3859_ = lean_ctor_get(v_attrs_3855_, 1);
v_isSharedCheck_3929_ = !lean_is_exclusive(v_attrs_3855_);
if (v_isSharedCheck_3929_ == 0)
{
lean_object* v_unused_3930_; 
v_unused_3930_ = lean_ctor_get(v_attrs_3855_, 0);
lean_dec(v_unused_3930_);
v___x_3861_ = v_attrs_3855_;
v_isShared_3862_ = v_isSharedCheck_3929_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_ext_3859_);
lean_dec(v_attrs_3855_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3929_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v_toEnvExtension_3863_; lean_object* v_name_3864_; lean_object* v_addEntryFn_3865_; lean_object* v___x_3866_; uint8_t v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v_pfx_3875_; lean_object* v___x_3876_; 
v_toEnvExtension_3863_ = lean_ctor_get(v_ext_3859_, 0);
lean_inc_ref(v_toEnvExtension_3863_);
v_name_3864_ = lean_ctor_get(v_ext_3859_, 1);
v_addEntryFn_3865_ = lean_ctor_get(v_ext_3859_, 3);
lean_inc(v_addEntryFn_3865_);
v___x_3866_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3867_ = 1;
lean_inc(v_name_3864_);
v___x_3868_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3864_, v___x_3867_);
v___x_3869_ = lean_string_append(v___x_3866_, v___x_3868_);
lean_dec_ref(v___x_3868_);
v___x_3870_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3871_ = lean_string_append(v___x_3869_, v___x_3870_);
lean_inc(v_decl_3857_);
v___x_3872_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3857_, v___x_3867_);
v___x_3873_ = lean_string_append(v___x_3871_, v___x_3872_);
lean_dec_ref(v___x_3872_);
v___x_3874_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3875_ = lean_string_append(v___x_3873_, v___x_3874_);
v___x_3876_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3856_, v_decl_3857_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_asyncMode_3877_; uint8_t v_logWrites_3878_; uint8_t v___x_3879_; 
v_asyncMode_3877_ = lean_ctor_get(v_toEnvExtension_3863_, 2);
lean_inc(v_asyncMode_3877_);
v_logWrites_3878_ = lean_ctor_get_uint8(v_toEnvExtension_3863_, sizeof(void*)*6);
lean_inc(v_decl_3857_);
lean_inc_ref(v_env_3856_);
v___x_3879_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3856_, v_decl_3857_, v_asyncMode_3877_);
if (v___x_3879_ == 0)
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___y_3883_; lean_object* v___x_3887_; 
lean_dec(v_asyncMode_3877_);
lean_dec(v_addEntryFn_3865_);
lean_dec_ref(v_toEnvExtension_3863_);
lean_del_object(v___x_3861_);
lean_dec_ref(v_ext_3859_);
lean_dec(v_val_3858_);
lean_dec(v_decl_3857_);
v___x_3880_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3881_ = lean_string_append(v_pfx_3875_, v___x_3880_);
v___x_3887_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3856_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v___x_3888_; 
v___x_3888_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3883_ = v___x_3888_;
goto v___jp_3882_;
}
else
{
lean_object* v_val_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v_val_3889_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_val_3889_);
lean_dec_ref_known(v___x_3887_, 1);
v___x_3890_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3891_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3889_, v___x_3867_);
v___x_3892_ = l_addParenHeuristic(v___x_3891_);
v___x_3893_ = lean_string_append(v___x_3890_, v___x_3892_);
lean_dec_ref(v___x_3892_);
v___x_3894_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3895_ = lean_string_append(v___x_3893_, v___x_3894_);
v___y_3883_ = v___x_3895_;
goto v___jp_3882_;
}
v___jp_3882_:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3884_ = lean_string_append(v___x_3881_, v___y_3883_);
lean_dec_ref(v___y_3883_);
v___x_3885_ = lean_string_append(v___x_3884_, v___x_3874_);
v___x_3886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3885_);
return v___x_3886_;
}
}
else
{
lean_object* v___x_3896_; uint8_t v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3896_ = lean_box(1);
v___x_3897_ = 0;
lean_inc(v_decl_3857_);
lean_inc_ref(v_env_3856_);
v___x_3898_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3896_, v_ext_3859_, v_env_3856_, v_asyncMode_3877_, v_decl_3857_, v___x_3897_);
lean_dec_ref(v_ext_3859_);
v___x_3899_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3898_, v_decl_3857_);
lean_dec(v___x_3898_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v___x_3901_; 
lean_dec_ref(v_pfx_3875_);
lean_inc(v_decl_3857_);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 1, v_val_3858_);
lean_ctor_set(v___x_3861_, 0, v_decl_3857_);
v___x_3901_ = v___x_3861_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_decl_3857_);
lean_ctor_set(v_reuseFailAlloc_3908_, 1, v_val_3858_);
v___x_3901_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
lean_object* v___f_3902_; 
v___f_3902_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3902_, 0, v_addEntryFn_3865_);
lean_closure_set(v___f_3902_, 1, v___x_3901_);
if (v_logWrites_3878_ == 0)
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3903_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3863_, v_env_3856_, v___f_3902_, v_asyncMode_3877_, v_decl_3857_, v___x_3879_);
lean_dec(v_asyncMode_3877_);
v___x_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3903_);
return v___x_3904_;
}
else
{
lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
lean_inc_ref(v_toEnvExtension_3863_);
v___x_3905_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3863_, v_env_3856_);
lean_dec_ref(v_env_3856_);
v___x_3906_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3863_, v___x_3905_, v___f_3902_, v_asyncMode_3877_, v_decl_3857_, v___x_3879_);
lean_dec(v_asyncMode_3877_);
v___x_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3906_);
return v___x_3907_;
}
}
}
else
{
lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3917_; 
lean_dec(v_asyncMode_3877_);
lean_dec(v_addEntryFn_3865_);
lean_dec_ref(v_toEnvExtension_3863_);
lean_del_object(v___x_3861_);
lean_dec(v_val_3858_);
lean_dec(v_decl_3857_);
lean_dec_ref(v_env_3856_);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3917_ == 0)
{
lean_object* v_unused_3918_; 
v_unused_3918_ = lean_ctor_get(v___x_3899_, 0);
lean_dec(v_unused_3918_);
v___x_3910_ = v___x_3899_;
v_isShared_3911_ = v_isSharedCheck_3917_;
goto v_resetjp_3909_;
}
else
{
lean_dec(v___x_3899_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3917_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3915_; 
v___x_3912_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3913_ = lean_string_append(v_pfx_3875_, v___x_3912_);
if (v_isShared_3911_ == 0)
{
lean_ctor_set_tag(v___x_3910_, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3913_);
v___x_3915_ = v___x_3910_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3913_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
}
else
{
lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3927_; 
lean_dec(v_addEntryFn_3865_);
lean_dec_ref(v_toEnvExtension_3863_);
lean_del_object(v___x_3861_);
lean_dec_ref(v_ext_3859_);
lean_dec(v_val_3858_);
lean_dec(v_decl_3857_);
lean_dec_ref(v_env_3856_);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3927_ == 0)
{
lean_object* v_unused_3928_; 
v_unused_3928_ = lean_ctor_get(v___x_3876_, 0);
lean_dec(v_unused_3928_);
v___x_3920_ = v___x_3876_;
v_isShared_3921_ = v_isSharedCheck_3927_;
goto v_resetjp_3919_;
}
else
{
lean_dec(v___x_3876_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3927_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3925_; 
v___x_3922_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3923_ = lean_string_append(v_pfx_3875_, v___x_3922_);
if (v_isShared_3921_ == 0)
{
lean_ctor_set_tag(v___x_3920_, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3923_);
v___x_3925_ = v___x_3920_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3923_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3931_, lean_object* v_attrs_3932_, lean_object* v_env_3933_, lean_object* v_decl_3934_, lean_object* v_val_3935_){
_start:
{
lean_object* v___x_3936_; 
v___x_3936_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3932_, v_env_3933_, v_decl_3934_, v_val_3935_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3938_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3939_ = lean_st_mk_ref(v___x_3938_);
v___x_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3939_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3945_, lean_object* v_builder_3946_){
_start:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; uint8_t v___x_3950_; 
v___x_3948_ = l_Lean_attributeImplBuilderTableRef;
v___x_3949_ = lean_st_ref_get(v___x_3948_);
v___x_3950_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3949_, v_builderId_3945_);
lean_dec(v___x_3949_);
if (v___x_3950_ == 0)
{
lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3951_ = lean_st_ref_take(v___x_3948_);
v___x_3952_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3951_, v_builderId_3945_, v_builder_3946_);
v___x_3953_ = lean_st_ref_put(v___x_3948_, v___x_3952_);
v___x_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3953_);
return v___x_3954_;
}
else
{
lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
lean_dec_ref(v_builder_3946_);
v___x_3955_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3956_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3945_, v___x_3950_);
v___x_3957_ = lean_string_append(v___x_3955_, v___x_3956_);
lean_dec_ref(v___x_3956_);
v___x_3958_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3959_ = lean_string_append(v___x_3957_, v___x_3958_);
v___x_3960_ = lean_mk_io_user_error(v___x_3959_);
v___x_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3960_);
return v___x_3961_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3962_, lean_object* v_builder_3963_, lean_object* v_a_3964_){
_start:
{
lean_object* v_res_3965_; 
v_res_3965_ = l_Lean_registerAttributeImplBuilder(v_builderId_3962_, v_builder_3963_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3966_){
_start:
{
if (lean_obj_tag(v_e_3966_) == 0)
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3976_; 
v_a_3968_ = lean_ctor_get(v_e_3966_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v_e_3966_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3970_ = v_e_3966_;
v_isShared_3971_ = v_isSharedCheck_3976_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v_e_3966_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3976_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3972_; lean_object* v___x_3974_; 
v___x_3972_ = lean_mk_io_user_error(v_a_3968_);
if (v_isShared_3971_ == 0)
{
lean_ctor_set_tag(v___x_3970_, 1);
lean_ctor_set(v___x_3970_, 0, v___x_3972_);
v___x_3974_ = v___x_3970_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3972_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
else
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
v_a_3977_ = lean_ctor_get(v_e_3966_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v_e_3966_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v_e_3966_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v_e_3966_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
lean_ctor_set_tag(v___x_3979_, 0);
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3977_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3985_, lean_object* v_a_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3985_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3988_, lean_object* v_e_3989_){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3989_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3992_, lean_object* v_e_3993_, lean_object* v_a_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3992_, v_e_3993_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3996_, lean_object* v_x_3997_){
_start:
{
if (lean_obj_tag(v_x_3997_) == 0)
{
lean_object* v___x_3998_; 
v___x_3998_ = lean_box(0);
return v___x_3998_;
}
else
{
lean_object* v_key_3999_; lean_object* v_value_4000_; lean_object* v_tail_4001_; uint8_t v___x_4002_; 
v_key_3999_ = lean_ctor_get(v_x_3997_, 0);
v_value_4000_ = lean_ctor_get(v_x_3997_, 1);
v_tail_4001_ = lean_ctor_get(v_x_3997_, 2);
v___x_4002_ = lean_name_eq(v_key_3999_, v_a_3996_);
if (v___x_4002_ == 0)
{
v_x_3997_ = v_tail_4001_;
goto _start;
}
else
{
lean_object* v___x_4004_; 
lean_inc(v_value_4000_);
v___x_4004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4004_, 0, v_value_4000_);
return v___x_4004_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_4005_, lean_object* v_x_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_4005_, v_x_4006_);
lean_dec(v_x_4006_);
lean_dec(v_a_4005_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_4008_, lean_object* v_a_4009_){
_start:
{
lean_object* v_buckets_4010_; lean_object* v___x_4011_; uint64_t v___y_4013_; 
v_buckets_4010_ = lean_ctor_get(v_m_4008_, 1);
v___x_4011_ = lean_array_get_size(v_buckets_4010_);
if (lean_obj_tag(v_a_4009_) == 0)
{
uint64_t v___x_4027_; 
v___x_4027_ = 1723ULL;
v___y_4013_ = v___x_4027_;
goto v___jp_4012_;
}
else
{
uint64_t v_hash_4028_; 
v_hash_4028_ = lean_ctor_get_uint64(v_a_4009_, sizeof(void*)*2);
v___y_4013_ = v_hash_4028_;
goto v___jp_4012_;
}
v___jp_4012_:
{
uint64_t v___x_4014_; uint64_t v___x_4015_; uint64_t v_fold_4016_; uint64_t v___x_4017_; uint64_t v___x_4018_; uint64_t v___x_4019_; size_t v___x_4020_; size_t v___x_4021_; size_t v___x_4022_; size_t v___x_4023_; size_t v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4014_ = 32ULL;
v___x_4015_ = lean_uint64_shift_right(v___y_4013_, v___x_4014_);
v_fold_4016_ = lean_uint64_xor(v___y_4013_, v___x_4015_);
v___x_4017_ = 16ULL;
v___x_4018_ = lean_uint64_shift_right(v_fold_4016_, v___x_4017_);
v___x_4019_ = lean_uint64_xor(v_fold_4016_, v___x_4018_);
v___x_4020_ = lean_uint64_to_usize(v___x_4019_);
v___x_4021_ = lean_usize_of_nat(v___x_4011_);
v___x_4022_ = ((size_t)1ULL);
v___x_4023_ = lean_usize_sub(v___x_4021_, v___x_4022_);
v___x_4024_ = lean_usize_land(v___x_4020_, v___x_4023_);
v___x_4025_ = lean_array_uget_borrowed(v_buckets_4010_, v___x_4024_);
v___x_4026_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_4009_, v___x_4025_);
return v___x_4026_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_4029_, lean_object* v_a_4030_){
_start:
{
lean_object* v_res_4031_; 
v_res_4031_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_4029_, v_a_4030_);
lean_dec(v_a_4030_);
lean_dec_ref(v_m_4029_);
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_4033_){
_start:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v_builderId_4037_; lean_object* v_ref_4038_; lean_object* v_args_4039_; lean_object* v___x_4040_; 
v___x_4035_ = l_Lean_attributeImplBuilderTableRef;
v___x_4036_ = lean_st_ref_get(v___x_4035_);
v_builderId_4037_ = lean_ctor_get(v_e_4033_, 0);
lean_inc(v_builderId_4037_);
v_ref_4038_ = lean_ctor_get(v_e_4033_, 1);
lean_inc(v_ref_4038_);
v_args_4039_ = lean_ctor_get(v_e_4033_, 2);
lean_inc(v_args_4039_);
lean_dec_ref(v_e_4033_);
v___x_4040_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4036_, v_builderId_4037_);
lean_dec(v___x_4036_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v___x_4041_; uint8_t v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
lean_dec(v_args_4039_);
lean_dec(v_ref_4038_);
v___x_4041_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_4042_ = 1;
v___x_4043_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_4037_, v___x_4042_);
v___x_4044_ = lean_string_append(v___x_4041_, v___x_4043_);
lean_dec_ref(v___x_4043_);
v___x_4045_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4046_ = lean_string_append(v___x_4044_, v___x_4045_);
v___x_4047_ = lean_mk_io_user_error(v___x_4046_);
v___x_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4047_);
return v___x_4048_;
}
else
{
lean_object* v_val_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
lean_dec(v_builderId_4037_);
v_val_4049_ = lean_ctor_get(v___x_4040_, 0);
lean_inc(v_val_4049_);
lean_dec_ref_known(v___x_4040_, 1);
v___x_4050_ = lean_apply_2(v_val_4049_, v_ref_4038_, v_args_4039_);
v___x_4051_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_4050_);
return v___x_4051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_4052_, lean_object* v_a_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l_Lean_mkAttributeImplOfEntry(v_e_4052_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_4055_, lean_object* v_m_4056_, lean_object* v_a_4057_){
_start:
{
lean_object* v___x_4058_; 
v___x_4058_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_4056_, v_a_4057_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_4059_, lean_object* v_m_4060_, lean_object* v_a_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_4059_, v_m_4060_, v_a_4061_);
lean_dec(v_a_4061_);
lean_dec_ref(v_m_4060_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_4063_, lean_object* v_a_4064_, lean_object* v_x_4065_){
_start:
{
lean_object* v___x_4066_; 
v___x_4066_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_4064_, v_x_4065_);
return v___x_4066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4067_, lean_object* v_a_4068_, lean_object* v_x_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_4067_, v_a_4068_, v_x_4069_);
lean_dec(v_x_4069_);
lean_dec(v_a_4068_);
return v_res_4070_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4071_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_4072_ = lean_box(0);
v___x_4073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4072_);
lean_ctor_set(v___x_4073_, 1, v___x_4071_);
return v___x_4073_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_4074_; 
v___x_4074_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_4074_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4077_ = l_Lean_attributeMapRef;
v___x_4078_ = lean_st_ref_get(v___x_4077_);
v___x_4079_ = lean_box(0);
v___x_4080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4079_);
lean_ctor_set(v___x_4080_, 1, v___x_4078_);
v___x_4081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_4082_){
_start:
{
lean_object* v_res_4083_; 
v_res_4083_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_4089_, lean_object* v_opts_4090_, lean_object* v_declName_4091_){
_start:
{
uint8_t v___x_4094_; lean_object* v___x_4095_; 
v___x_4094_ = 0;
lean_inc(v_declName_4091_);
lean_inc_ref(v_env_4089_);
v___x_4095_ = l_Lean_Environment_find_x3f(v_env_4089_, v_declName_4091_, v___x_4094_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v___x_4096_; uint8_t v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
lean_dec_ref(v_env_4089_);
v___x_4096_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_4097_ = 1;
v___x_4098_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_4091_, v___x_4097_);
v___x_4099_ = lean_string_append(v___x_4096_, v___x_4098_);
lean_dec_ref(v___x_4098_);
v___x_4100_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4101_ = lean_string_append(v___x_4099_, v___x_4100_);
v___x_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4101_);
return v___x_4102_;
}
else
{
lean_object* v_val_4103_; lean_object* v___x_4104_; 
v_val_4103_ = lean_ctor_get(v___x_4095_, 0);
lean_inc(v_val_4103_);
lean_dec_ref_known(v___x_4095_, 1);
v___x_4104_ = l_Lean_ConstantInfo_type(v_val_4103_);
lean_dec(v_val_4103_);
if (lean_obj_tag(v___x_4104_) == 4)
{
lean_object* v_declName_4105_; 
v_declName_4105_ = lean_ctor_get(v___x_4104_, 0);
lean_inc(v_declName_4105_);
lean_dec_ref_known(v___x_4104_, 2);
if (lean_obj_tag(v_declName_4105_) == 1)
{
lean_object* v_pre_4106_; 
v_pre_4106_ = lean_ctor_get(v_declName_4105_, 0);
lean_inc(v_pre_4106_);
if (lean_obj_tag(v_pre_4106_) == 1)
{
lean_object* v_pre_4107_; 
v_pre_4107_ = lean_ctor_get(v_pre_4106_, 0);
if (lean_obj_tag(v_pre_4107_) == 0)
{
lean_object* v_str_4108_; lean_object* v_str_4109_; lean_object* v___x_4110_; uint8_t v___x_4111_; 
v_str_4108_ = lean_ctor_get(v_declName_4105_, 1);
lean_inc_ref(v_str_4108_);
lean_dec_ref_known(v_declName_4105_, 2);
v_str_4109_ = lean_ctor_get(v_pre_4106_, 1);
lean_inc_ref(v_str_4109_);
lean_dec_ref_known(v_pre_4106_, 2);
v___x_4110_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_4111_ = lean_string_dec_eq(v_str_4109_, v___x_4110_);
lean_dec_ref(v_str_4109_);
if (v___x_4111_ == 0)
{
lean_dec_ref(v_str_4108_);
lean_dec(v_declName_4091_);
lean_dec_ref(v_env_4089_);
goto v___jp_4092_;
}
else
{
lean_object* v___x_4112_; uint8_t v___x_4113_; 
v___x_4112_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_4113_ = lean_string_dec_eq(v_str_4108_, v___x_4112_);
lean_dec_ref(v_str_4108_);
if (v___x_4113_ == 0)
{
lean_dec(v_declName_4091_);
lean_dec_ref(v_env_4089_);
goto v___jp_4092_;
}
else
{
lean_object* v___x_4114_; 
v___x_4114_ = l_Lean_Environment_evalConst___redArg(v_env_4089_, v_opts_4090_, v_declName_4091_, v___x_4113_);
lean_dec(v_declName_4091_);
lean_dec_ref(v_env_4089_);
return v___x_4114_;
}
}
}
else
{
lean_dec_ref_known(v_pre_4106_, 2);
lean_dec_ref_known(v_declName_4105_, 2);
lean_dec(v_declName_4091_);
lean_dec_ref(v_env_4089_);
goto v___jp_4092_;
}
}
else
{
lean_dec(v_pre_4106_);
lean_dec_ref_known(v_declName_4105_, 2);
lean_dec(v_declName_4091_);
lean_dec_ref(v_env_4089_);
goto v___jp_4092_;
}
}
else
{
lean_dec(v_declName_4105_);
lean_dec(v_declName_4091_);
lean_dec_ref(v_env_4089_);
goto v___jp_4092_;
}
}
else
{
lean_dec_ref(v___x_4104_);
lean_dec(v_declName_4091_);
lean_dec_ref(v_env_4089_);
goto v___jp_4092_;
}
}
v___jp_4092_:
{
lean_object* v___x_4093_; 
v___x_4093_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_4093_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_4115_, lean_object* v_opts_4116_, lean_object* v_declName_4117_){
_start:
{
lean_object* v_res_4118_; 
v_res_4118_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_4115_, v_opts_4116_, v_declName_4117_);
lean_dec_ref(v_opts_4116_);
return v_res_4118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_4119_, size_t v_i_4120_, size_t v_stop_4121_, lean_object* v_b_4122_){
_start:
{
uint8_t v___x_4124_; 
v___x_4124_ = lean_usize_dec_eq(v_i_4120_, v_stop_4121_);
if (v___x_4124_ == 0)
{
lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4125_ = lean_array_uget_borrowed(v_as_4119_, v_i_4120_);
lean_inc(v___x_4125_);
v___x_4126_ = l_Lean_mkAttributeImplOfEntry(v___x_4125_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; lean_object* v_toAttributeImplCore_4128_; lean_object* v_name_4129_; lean_object* v___x_4130_; size_t v___x_4131_; size_t v___x_4132_; 
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
lean_inc(v_a_4127_);
lean_dec_ref_known(v___x_4126_, 1);
v_toAttributeImplCore_4128_ = lean_ctor_get(v_a_4127_, 0);
v_name_4129_ = lean_ctor_get(v_toAttributeImplCore_4128_, 1);
lean_inc(v_name_4129_);
v___x_4130_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_4122_, v_name_4129_, v_a_4127_);
v___x_4131_ = ((size_t)1ULL);
v___x_4132_ = lean_usize_add(v_i_4120_, v___x_4131_);
v_i_4120_ = v___x_4132_;
v_b_4122_ = v___x_4130_;
goto _start;
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
lean_dec_ref(v_b_4122_);
v_a_4134_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___x_4126_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4126_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
else
{
lean_object* v___x_4142_; 
v___x_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4142_, 0, v_b_4122_);
return v___x_4142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_4143_, lean_object* v_i_4144_, lean_object* v_stop_4145_, lean_object* v_b_4146_, lean_object* v___y_4147_){
_start:
{
size_t v_i_boxed_4148_; size_t v_stop_boxed_4149_; lean_object* v_res_4150_; 
v_i_boxed_4148_ = lean_unbox_usize(v_i_4144_);
lean_dec(v_i_4144_);
v_stop_boxed_4149_ = lean_unbox_usize(v_stop_4145_);
lean_dec(v_stop_4145_);
v_res_4150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4143_, v_i_boxed_4148_, v_stop_boxed_4149_, v_b_4146_);
lean_dec_ref(v_as_4143_);
return v_res_4150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_4151_, size_t v_i_4152_, size_t v_stop_4153_, lean_object* v_b_4154_, lean_object* v___y_4155_){
_start:
{
lean_object* v_a_4158_; lean_object* v___y_4163_; uint8_t v___x_4165_; 
v___x_4165_ = lean_usize_dec_eq(v_i_4152_, v_stop_4153_);
if (v___x_4165_ == 0)
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; uint8_t v___x_4169_; 
v___x_4166_ = lean_array_uget_borrowed(v_as_4151_, v_i_4152_);
v___x_4167_ = lean_unsigned_to_nat(0u);
v___x_4168_ = lean_array_get_size(v___x_4166_);
v___x_4169_ = lean_nat_dec_lt(v___x_4167_, v___x_4168_);
if (v___x_4169_ == 0)
{
v_a_4158_ = v_b_4154_;
goto v___jp_4157_;
}
else
{
uint8_t v___x_4170_; 
v___x_4170_ = lean_nat_dec_le(v___x_4168_, v___x_4168_);
if (v___x_4170_ == 0)
{
if (v___x_4169_ == 0)
{
v_a_4158_ = v_b_4154_;
goto v___jp_4157_;
}
else
{
size_t v___x_4171_; size_t v___x_4172_; lean_object* v___x_4173_; 
v___x_4171_ = ((size_t)0ULL);
v___x_4172_ = lean_usize_of_nat(v___x_4168_);
v___x_4173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4166_, v___x_4171_, v___x_4172_, v_b_4154_);
v___y_4163_ = v___x_4173_;
goto v___jp_4162_;
}
}
else
{
size_t v___x_4174_; size_t v___x_4175_; lean_object* v___x_4176_; 
v___x_4174_ = ((size_t)0ULL);
v___x_4175_ = lean_usize_of_nat(v___x_4168_);
v___x_4176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4166_, v___x_4174_, v___x_4175_, v_b_4154_);
v___y_4163_ = v___x_4176_;
goto v___jp_4162_;
}
}
}
else
{
lean_object* v___x_4177_; 
v___x_4177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4177_, 0, v_b_4154_);
return v___x_4177_;
}
v___jp_4157_:
{
size_t v___x_4159_; size_t v___x_4160_; 
v___x_4159_ = ((size_t)1ULL);
v___x_4160_ = lean_usize_add(v_i_4152_, v___x_4159_);
v_i_4152_ = v___x_4160_;
v_b_4154_ = v_a_4158_;
goto _start;
}
v___jp_4162_:
{
if (lean_obj_tag(v___y_4163_) == 0)
{
lean_object* v_a_4164_; 
v_a_4164_ = lean_ctor_get(v___y_4163_, 0);
lean_inc(v_a_4164_);
lean_dec_ref_known(v___y_4163_, 1);
v_a_4158_ = v_a_4164_;
goto v___jp_4157_;
}
else
{
return v___y_4163_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4178_, lean_object* v_i_4179_, lean_object* v_stop_4180_, lean_object* v_b_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_){
_start:
{
size_t v_i_boxed_4184_; size_t v_stop_boxed_4185_; lean_object* v_res_4186_; 
v_i_boxed_4184_ = lean_unbox_usize(v_i_4179_);
lean_dec(v_i_4179_);
v_stop_boxed_4185_ = lean_unbox_usize(v_stop_4180_);
lean_dec(v_stop_4180_);
v_res_4186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4178_, v_i_boxed_4184_, v_stop_boxed_4185_, v_b_4181_, v___y_4182_);
lean_dec_ref(v___y_4182_);
lean_dec_ref(v_as_4178_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4187_, lean_object* v_a_4188_){
_start:
{
lean_object* v_a_4191_; lean_object* v___y_4196_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; uint8_t v___x_4210_; 
v___x_4206_ = l_Lean_attributeMapRef;
v___x_4207_ = lean_st_ref_get(v___x_4206_);
v___x_4208_ = lean_unsigned_to_nat(0u);
v___x_4209_ = lean_array_get_size(v_es_4187_);
v___x_4210_ = lean_nat_dec_lt(v___x_4208_, v___x_4209_);
if (v___x_4210_ == 0)
{
v_a_4191_ = v___x_4207_;
goto v___jp_4190_;
}
else
{
uint8_t v___x_4211_; 
v___x_4211_ = lean_nat_dec_le(v___x_4209_, v___x_4209_);
if (v___x_4211_ == 0)
{
if (v___x_4210_ == 0)
{
v_a_4191_ = v___x_4207_;
goto v___jp_4190_;
}
else
{
size_t v___x_4212_; size_t v___x_4213_; lean_object* v___x_4214_; 
v___x_4212_ = ((size_t)0ULL);
v___x_4213_ = lean_usize_of_nat(v___x_4209_);
v___x_4214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4187_, v___x_4212_, v___x_4213_, v___x_4207_, v_a_4188_);
v___y_4196_ = v___x_4214_;
goto v___jp_4195_;
}
}
else
{
size_t v___x_4215_; size_t v___x_4216_; lean_object* v___x_4217_; 
v___x_4215_ = ((size_t)0ULL);
v___x_4216_ = lean_usize_of_nat(v___x_4209_);
v___x_4217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4187_, v___x_4215_, v___x_4216_, v___x_4207_, v_a_4188_);
v___y_4196_ = v___x_4217_;
goto v___jp_4195_;
}
}
v___jp_4190_:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4192_ = lean_box(0);
v___x_4193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4192_);
lean_ctor_set(v___x_4193_, 1, v_a_4191_);
v___x_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4193_);
return v___x_4194_;
}
v___jp_4195_:
{
if (lean_obj_tag(v___y_4196_) == 0)
{
lean_object* v_a_4197_; 
v_a_4197_ = lean_ctor_get(v___y_4196_, 0);
lean_inc(v_a_4197_);
lean_dec_ref_known(v___y_4196_, 1);
v_a_4191_ = v_a_4197_;
goto v___jp_4190_;
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
v_a_4198_ = lean_ctor_get(v___y_4196_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___y_4196_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___y_4196_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___y_4196_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4218_, v_a_4219_);
lean_dec_ref(v_a_4219_);
lean_dec_ref(v_es_4218_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4222_, size_t v_i_4223_, size_t v_stop_4224_, lean_object* v_b_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v___x_4228_; 
v___x_4228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4222_, v_i_4223_, v_stop_4224_, v_b_4225_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4229_, lean_object* v_i_4230_, lean_object* v_stop_4231_, lean_object* v_b_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
size_t v_i_boxed_4235_; size_t v_stop_boxed_4236_; lean_object* v_res_4237_; 
v_i_boxed_4235_ = lean_unbox_usize(v_i_4230_);
lean_dec(v_i_4230_);
v_stop_boxed_4236_ = lean_unbox_usize(v_stop_4231_);
lean_dec(v_stop_4231_);
v_res_4237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4229_, v_i_boxed_4235_, v_stop_boxed_4236_, v_b_4232_, v___y_4233_);
lean_dec_ref(v___y_4233_);
lean_dec_ref(v_as_4229_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4238_, lean_object* v_e_4239_){
_start:
{
lean_object* v_snd_4240_; lean_object* v_toAttributeImplCore_4241_; lean_object* v_fst_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4260_; 
v_snd_4240_ = lean_ctor_get(v_e_4239_, 1);
lean_inc(v_snd_4240_);
v_toAttributeImplCore_4241_ = lean_ctor_get(v_snd_4240_, 0);
v_fst_4242_ = lean_ctor_get(v_e_4239_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v_e_4239_);
if (v_isSharedCheck_4260_ == 0)
{
lean_object* v_unused_4261_; 
v_unused_4261_ = lean_ctor_get(v_e_4239_, 1);
lean_dec(v_unused_4261_);
v___x_4244_ = v_e_4239_;
v_isShared_4245_ = v_isSharedCheck_4260_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_fst_4242_);
lean_dec(v_e_4239_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4260_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v_newEntries_4246_; lean_object* v_map_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4259_; 
v_newEntries_4246_ = lean_ctor_get(v_s_4238_, 0);
v_map_4247_ = lean_ctor_get(v_s_4238_, 1);
v_isSharedCheck_4259_ = !lean_is_exclusive(v_s_4238_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4249_ = v_s_4238_;
v_isShared_4250_ = v_isSharedCheck_4259_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_map_4247_);
lean_inc(v_newEntries_4246_);
lean_dec(v_s_4238_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4259_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v_name_4251_; lean_object* v___x_4253_; 
v_name_4251_ = lean_ctor_get(v_toAttributeImplCore_4241_, 1);
lean_inc(v_name_4251_);
if (v_isShared_4245_ == 0)
{
lean_ctor_set_tag(v___x_4244_, 1);
lean_ctor_set(v___x_4244_, 1, v_newEntries_4246_);
v___x_4253_ = v___x_4244_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_fst_4242_);
lean_ctor_set(v_reuseFailAlloc_4258_, 1, v_newEntries_4246_);
v___x_4253_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
lean_object* v___x_4254_; lean_object* v___x_4256_; 
v___x_4254_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4247_, v_name_4251_, v_snd_4240_);
if (v_isShared_4250_ == 0)
{
lean_ctor_set(v___x_4249_, 1, v___x_4254_);
lean_ctor_set(v___x_4249_, 0, v___x_4253_);
v___x_4256_ = v___x_4249_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v___x_4253_);
lean_ctor_set(v_reuseFailAlloc_4257_, 1, v___x_4254_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4262_, lean_object* v_s_4263_){
_start:
{
lean_object* v_newEntries_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
v_newEntries_4264_ = lean_ctor_get(v_s_4263_, 0);
lean_inc(v_newEntries_4264_);
lean_dec_ref(v_s_4263_);
v___x_4265_ = l_List_reverse___redArg(v_newEntries_4264_);
v___x_4266_ = lean_array_mk(v___x_4265_);
lean_inc_ref_n(v___x_4266_, 2);
v___x_4267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4266_);
lean_ctor_set(v___x_4267_, 1, v___x_4266_);
lean_ctor_set(v___x_4267_, 2, v___x_4266_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4268_, lean_object* v_s_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4268_, v_s_4269_);
lean_dec_ref(v_x_4268_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4271_){
_start:
{
lean_object* v_newEntries_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4283_; 
v_newEntries_4272_ = lean_ctor_get(v_s_4271_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v_s_4271_);
if (v_isSharedCheck_4283_ == 0)
{
lean_object* v_unused_4284_; 
v_unused_4284_ = lean_ctor_get(v_s_4271_, 1);
lean_dec(v_unused_4284_);
v___x_4274_ = v_s_4271_;
v_isShared_4275_ = v_isSharedCheck_4283_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_newEntries_4272_);
lean_dec(v_s_4271_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4283_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4281_; 
v___x_4276_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4277_ = l_List_lengthTR___redArg(v_newEntries_4272_);
lean_dec(v_newEntries_4272_);
v___x_4278_ = l_Nat_reprFast(v___x_4277_);
v___x_4279_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4278_);
if (v_isShared_4275_ == 0)
{
lean_ctor_set_tag(v___x_4274_, 5);
lean_ctor_set(v___x_4274_, 1, v___x_4279_);
lean_ctor_set(v___x_4274_, 0, v___x_4276_);
v___x_4281_ = v___x_4274_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v___x_4276_);
lean_ctor_set(v_reuseFailAlloc_4282_, 1, v___x_4279_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
return v___x_4281_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4285_){
_start:
{
lean_object* v_newEntries_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; 
v_newEntries_4286_ = lean_ctor_get(v_s_4285_, 0);
lean_inc(v_newEntries_4286_);
lean_dec_ref(v_s_4285_);
v___x_4287_ = l_List_reverse___redArg(v_newEntries_4286_);
v___x_4288_ = lean_array_mk(v___x_4287_);
return v___x_4288_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___f_4301_; lean_object* v___f_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v___x_4298_ = 0;
v___x_4299_ = lean_box(0);
v___x_4300_ = lean_box(2);
v___f_4301_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4302_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4303_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4304_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4305_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4306_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4307_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_4307_, 0, v___x_4306_);
lean_ctor_set(v___x_4307_, 1, v___x_4305_);
lean_ctor_set(v___x_4307_, 2, v___x_4304_);
lean_ctor_set(v___x_4307_, 3, v___x_4303_);
lean_ctor_set(v___x_4307_, 4, v___f_4302_);
lean_ctor_set(v___x_4307_, 5, v___f_4301_);
lean_ctor_set(v___x_4307_, 6, v___x_4300_);
lean_ctor_set(v___x_4307_, 7, v___x_4299_);
lean_ctor_set_uint8(v___x_4307_, sizeof(void*)*8, v___x_4298_);
lean_ctor_set_uint8(v___x_4307_, sizeof(void*)*8 + 1, v___x_4298_);
return v___x_4307_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
v___f_4308_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4309_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4310_, 0, v___x_4309_);
lean_ctor_set(v___x_4310_, 1, v___f_4308_);
return v___x_4310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; 
v___x_4312_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4313_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4312_);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4314_){
_start:
{
lean_object* v_res_4315_; 
v_res_4315_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4316_){
_start:
{
lean_object* v___x_4318_; lean_object* v___x_4319_; uint8_t v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; 
v___x_4318_ = l_Lean_attributeMapRef;
v___x_4319_ = lean_st_ref_get(v___x_4318_);
v___x_4320_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4319_, v_n_4316_);
lean_dec(v___x_4319_);
v___x_4321_ = lean_box(v___x_4320_);
v___x_4322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4321_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4323_, lean_object* v_a_4324_){
_start:
{
lean_object* v_res_4325_; 
v_res_4325_ = l_Lean_isBuiltinAttribute(v_n_4323_);
lean_dec(v_n_4323_);
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4326_, lean_object* v_x_4327_){
_start:
{
if (lean_obj_tag(v_x_4327_) == 0)
{
return v_x_4326_;
}
else
{
lean_object* v_key_4328_; lean_object* v_tail_4329_; lean_object* v___x_4330_; 
v_key_4328_ = lean_ctor_get(v_x_4327_, 0);
v_tail_4329_ = lean_ctor_get(v_x_4327_, 2);
lean_inc(v_key_4328_);
v___x_4330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4330_, 0, v_key_4328_);
lean_ctor_set(v___x_4330_, 1, v_x_4326_);
v_x_4326_ = v___x_4330_;
v_x_4327_ = v_tail_4329_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4332_, lean_object* v_x_4333_){
_start:
{
lean_object* v_res_4334_; 
v_res_4334_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4332_, v_x_4333_);
lean_dec(v_x_4333_);
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4335_, size_t v_i_4336_, size_t v_stop_4337_, lean_object* v_b_4338_){
_start:
{
uint8_t v___x_4339_; 
v___x_4339_ = lean_usize_dec_eq(v_i_4336_, v_stop_4337_);
if (v___x_4339_ == 0)
{
lean_object* v___x_4340_; lean_object* v___x_4341_; size_t v___x_4342_; size_t v___x_4343_; 
v___x_4340_ = lean_array_uget_borrowed(v_as_4335_, v_i_4336_);
v___x_4341_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4338_, v___x_4340_);
v___x_4342_ = ((size_t)1ULL);
v___x_4343_ = lean_usize_add(v_i_4336_, v___x_4342_);
v_i_4336_ = v___x_4343_;
v_b_4338_ = v___x_4341_;
goto _start;
}
else
{
return v_b_4338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4345_, lean_object* v_i_4346_, lean_object* v_stop_4347_, lean_object* v_b_4348_){
_start:
{
size_t v_i_boxed_4349_; size_t v_stop_boxed_4350_; lean_object* v_res_4351_; 
v_i_boxed_4349_ = lean_unbox_usize(v_i_4346_);
lean_dec(v_i_4346_);
v_stop_boxed_4350_ = lean_unbox_usize(v_stop_4347_);
lean_dec(v_stop_4347_);
v_res_4351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4345_, v_i_boxed_4349_, v_stop_boxed_4350_, v_b_4348_);
lean_dec_ref(v_as_4345_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v_buckets_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; uint8_t v___x_4359_; 
v___x_4353_ = l_Lean_attributeMapRef;
v___x_4354_ = lean_st_ref_get(v___x_4353_);
v_buckets_4355_ = lean_ctor_get(v___x_4354_, 1);
lean_inc_ref(v_buckets_4355_);
lean_dec(v___x_4354_);
v___x_4356_ = lean_box(0);
v___x_4357_ = lean_unsigned_to_nat(0u);
v___x_4358_ = lean_array_get_size(v_buckets_4355_);
v___x_4359_ = lean_nat_dec_lt(v___x_4357_, v___x_4358_);
if (v___x_4359_ == 0)
{
lean_object* v___x_4360_; 
lean_dec_ref(v_buckets_4355_);
v___x_4360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4356_);
return v___x_4360_;
}
else
{
size_t v___x_4361_; size_t v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4361_ = ((size_t)0ULL);
v___x_4362_ = lean_usize_of_nat(v___x_4358_);
v___x_4363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4355_, v___x_4361_, v___x_4362_, v___x_4356_);
lean_dec_ref(v_buckets_4355_);
v___x_4364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4363_);
return v___x_4364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4365_){
_start:
{
lean_object* v_res_4366_; 
v_res_4366_ = l_Lean_getBuiltinAttributeNames();
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4368_){
_start:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; 
v___x_4370_ = l_Lean_attributeMapRef;
v___x_4371_ = lean_st_ref_get(v___x_4370_);
v___x_4372_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4371_, v_attrName_4368_);
lean_dec(v___x_4371_);
if (lean_obj_tag(v___x_4372_) == 0)
{
lean_object* v___x_4373_; uint8_t v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4373_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4374_ = 1;
v___x_4375_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4368_, v___x_4374_);
v___x_4376_ = lean_string_append(v___x_4373_, v___x_4375_);
lean_dec_ref(v___x_4375_);
v___x_4377_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4378_ = lean_string_append(v___x_4376_, v___x_4377_);
v___x_4379_ = lean_mk_io_user_error(v___x_4378_);
v___x_4380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4379_);
return v___x_4380_;
}
else
{
lean_object* v_val_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4388_; 
lean_dec(v_attrName_4368_);
v_val_4381_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4383_ = v___x_4372_;
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_val_4381_);
lean_dec(v___x_4372_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4386_; 
if (v_isShared_4384_ == 0)
{
lean_ctor_set_tag(v___x_4383_, 0);
v___x_4386_ = v___x_4383_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_val_4381_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4389_, lean_object* v_a_4390_){
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4389_);
return v_res_4391_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4392_, lean_object* v_attrName_4393_){
_start:
{
lean_object* v___x_4394_; lean_object* v_toEnvExtension_4395_; lean_object* v_asyncMode_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; uint8_t v___x_4399_; lean_object* v___x_4400_; lean_object* v_map_4401_; uint8_t v___x_4402_; 
v___x_4394_ = l_Lean_attributeExtension;
v_toEnvExtension_4395_ = lean_ctor_get(v___x_4394_, 0);
v_asyncMode_4396_ = lean_ctor_get(v_toEnvExtension_4395_, 2);
v___x_4397_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4398_ = lean_box(0);
v___x_4399_ = 0;
v___x_4400_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4397_, v___x_4394_, v_env_4392_, v_asyncMode_4396_, v___x_4398_, v___x_4399_);
v_map_4401_ = lean_ctor_get(v___x_4400_, 1);
lean_inc_ref(v_map_4401_);
lean_dec(v___x_4400_);
v___x_4402_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4401_, v_attrName_4393_);
lean_dec_ref(v_map_4401_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4403_, lean_object* v_attrName_4404_){
_start:
{
uint8_t v_res_4405_; lean_object* v_r_4406_; 
v_res_4405_ = l_Lean_isAttribute(v_env_4403_, v_attrName_4404_);
lean_dec(v_attrName_4404_);
v_r_4406_ = lean_box(v_res_4405_);
return v_r_4406_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4407_){
_start:
{
lean_object* v___x_4408_; lean_object* v_toEnvExtension_4409_; lean_object* v_asyncMode_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; uint8_t v___x_4413_; lean_object* v___x_4414_; lean_object* v_map_4415_; lean_object* v_buckets_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; uint8_t v___x_4420_; 
v___x_4408_ = l_Lean_attributeExtension;
v_toEnvExtension_4409_ = lean_ctor_get(v___x_4408_, 0);
v_asyncMode_4410_ = lean_ctor_get(v_toEnvExtension_4409_, 2);
v___x_4411_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4412_ = lean_box(0);
v___x_4413_ = 0;
v___x_4414_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4411_, v___x_4408_, v_env_4407_, v_asyncMode_4410_, v___x_4412_, v___x_4413_);
v_map_4415_ = lean_ctor_get(v___x_4414_, 1);
lean_inc_ref(v_map_4415_);
lean_dec(v___x_4414_);
v_buckets_4416_ = lean_ctor_get(v_map_4415_, 1);
lean_inc_ref(v_buckets_4416_);
lean_dec_ref(v_map_4415_);
v___x_4417_ = lean_box(0);
v___x_4418_ = lean_unsigned_to_nat(0u);
v___x_4419_ = lean_array_get_size(v_buckets_4416_);
v___x_4420_ = lean_nat_dec_lt(v___x_4418_, v___x_4419_);
if (v___x_4420_ == 0)
{
lean_dec_ref(v_buckets_4416_);
return v___x_4417_;
}
else
{
size_t v___x_4421_; size_t v___x_4422_; lean_object* v___x_4423_; 
v___x_4421_ = ((size_t)0ULL);
v___x_4422_ = lean_usize_of_nat(v___x_4419_);
v___x_4423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4416_, v___x_4421_, v___x_4422_, v___x_4417_);
lean_dec_ref(v_buckets_4416_);
return v___x_4423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4424_, lean_object* v_attrName_4425_){
_start:
{
lean_object* v___x_4426_; lean_object* v_toEnvExtension_4427_; lean_object* v_asyncMode_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; uint8_t v___x_4431_; lean_object* v___x_4432_; lean_object* v_map_4433_; lean_object* v___x_4434_; 
v___x_4426_ = l_Lean_attributeExtension;
v_toEnvExtension_4427_ = lean_ctor_get(v___x_4426_, 0);
v_asyncMode_4428_ = lean_ctor_get(v_toEnvExtension_4427_, 2);
v___x_4429_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4430_ = lean_box(0);
v___x_4431_ = 0;
v___x_4432_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4429_, v___x_4426_, v_env_4424_, v_asyncMode_4428_, v___x_4430_, v___x_4431_);
v_map_4433_ = lean_ctor_get(v___x_4432_, 1);
lean_inc_ref(v_map_4433_);
lean_dec(v___x_4432_);
v___x_4434_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4433_, v_attrName_4425_);
lean_dec_ref(v_map_4433_);
if (lean_obj_tag(v___x_4434_) == 0)
{
lean_object* v___x_4435_; uint8_t v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
v___x_4435_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4436_ = 1;
v___x_4437_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4425_, v___x_4436_);
v___x_4438_ = lean_string_append(v___x_4435_, v___x_4437_);
lean_dec_ref(v___x_4437_);
v___x_4439_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4440_ = lean_string_append(v___x_4438_, v___x_4439_);
v___x_4441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4441_, 0, v___x_4440_);
return v___x_4441_;
}
else
{
lean_object* v_val_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4449_; 
lean_dec(v_attrName_4425_);
v_val_4442_ = lean_ctor_get(v___x_4434_, 0);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_4434_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4444_ = v___x_4434_;
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_val_4442_);
lean_dec(v___x_4434_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4447_; 
if (v_isShared_4445_ == 0)
{
v___x_4447_ = v___x_4444_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_val_4442_);
v___x_4447_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
return v___x_4447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___lam__0(lean_object* v___x_4450_, lean_object* v___x_4451_, lean_object* v_s_4452_){
_start:
{
lean_object* v_addEntryFn_4453_; lean_object* v_importedEntries_4454_; lean_object* v_state_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4463_; 
v_addEntryFn_4453_ = lean_ctor_get(v___x_4450_, 3);
lean_inc(v_addEntryFn_4453_);
lean_dec_ref(v___x_4450_);
v_importedEntries_4454_ = lean_ctor_get(v_s_4452_, 0);
v_state_4455_ = lean_ctor_get(v_s_4452_, 1);
v_isSharedCheck_4463_ = !lean_is_exclusive(v_s_4452_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4457_ = v_s_4452_;
v_isShared_4458_ = v_isSharedCheck_4463_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_state_4455_);
lean_inc(v_importedEntries_4454_);
lean_dec(v_s_4452_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4463_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v_state_4459_; lean_object* v___x_4461_; 
v_state_4459_ = lean_apply_2(v_addEntryFn_4453_, v_state_4455_, v___x_4451_);
if (v_isShared_4458_ == 0)
{
lean_ctor_set(v___x_4457_, 1, v_state_4459_);
v___x_4461_ = v___x_4457_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v_importedEntries_4454_);
lean_ctor_set(v_reuseFailAlloc_4462_, 1, v_state_4459_);
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
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4464_, lean_object* v_builderId_4465_, lean_object* v_ref_4466_, lean_object* v_args_4467_){
_start:
{
lean_object* v_entry_4469_; lean_object* v___x_4470_; 
v_entry_4469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4469_, 0, v_builderId_4465_);
lean_ctor_set(v_entry_4469_, 1, v_ref_4466_);
lean_ctor_set(v_entry_4469_, 2, v_args_4467_);
lean_inc_ref(v_entry_4469_);
v___x_4470_ = l_Lean_mkAttributeImplOfEntry(v_entry_4469_);
if (lean_obj_tag(v___x_4470_) == 0)
{
lean_object* v_a_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4504_; 
v_a_4471_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4504_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4504_ == 0)
{
v___x_4473_ = v___x_4470_;
v_isShared_4474_ = v_isSharedCheck_4504_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_a_4471_);
lean_dec(v___x_4470_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4504_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v_toAttributeImplCore_4475_; lean_object* v_name_4476_; uint8_t v___x_4477_; 
v_toAttributeImplCore_4475_ = lean_ctor_get(v_a_4471_, 0);
v_name_4476_ = lean_ctor_get(v_toAttributeImplCore_4475_, 1);
lean_inc_ref(v_env_4464_);
v___x_4477_ = l_Lean_isAttribute(v_env_4464_, v_name_4476_);
if (v___x_4477_ == 0)
{
lean_object* v___x_4478_; lean_object* v_toEnvExtension_4479_; lean_object* v_asyncMode_4480_; uint8_t v_logWrites_4481_; lean_object* v___x_4482_; lean_object* v___f_4483_; lean_object* v___x_4484_; uint8_t v___x_4485_; 
v___x_4478_ = l_Lean_attributeExtension;
v_toEnvExtension_4479_ = lean_ctor_get(v___x_4478_, 0);
v_asyncMode_4480_ = lean_ctor_get(v_toEnvExtension_4479_, 2);
v_logWrites_4481_ = lean_ctor_get_uint8(v_toEnvExtension_4479_, sizeof(void*)*6);
v___x_4482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4482_, 0, v_entry_4469_);
lean_ctor_set(v___x_4482_, 1, v_a_4471_);
v___f_4483_ = lean_alloc_closure((void*)(l_Lean_registerAttributeOfBuilder___lam__0), 3, 2);
lean_closure_set(v___f_4483_, 0, v___x_4478_);
lean_closure_set(v___f_4483_, 1, v___x_4482_);
v___x_4484_ = lean_box(0);
v___x_4485_ = 1;
if (v_logWrites_4481_ == 0)
{
lean_object* v___x_4486_; lean_object* v___x_4488_; 
lean_inc_ref(v_toEnvExtension_4479_);
v___x_4486_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4479_, v_env_4464_, v___f_4483_, v_asyncMode_4480_, v___x_4484_, v___x_4485_);
if (v_isShared_4474_ == 0)
{
lean_ctor_set(v___x_4473_, 0, v___x_4486_);
v___x_4488_ = v___x_4473_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v___x_4486_);
v___x_4488_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
return v___x_4488_;
}
}
else
{
lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4493_; 
lean_inc_ref_n(v_toEnvExtension_4479_, 2);
v___x_4490_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4479_, v_env_4464_);
lean_dec_ref(v_env_4464_);
v___x_4491_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4479_, v___x_4490_, v___f_4483_, v_asyncMode_4480_, v___x_4484_, v___x_4485_);
if (v_isShared_4474_ == 0)
{
lean_ctor_set(v___x_4473_, 0, v___x_4491_);
v___x_4493_ = v___x_4473_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v___x_4491_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
return v___x_4493_;
}
}
}
else
{
lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4502_; 
lean_inc(v_name_4476_);
lean_dec(v_a_4471_);
lean_dec_ref_known(v_entry_4469_, 3);
lean_dec_ref(v_env_4464_);
v___x_4495_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4496_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4476_, v___x_4477_);
v___x_4497_ = lean_string_append(v___x_4495_, v___x_4496_);
lean_dec_ref(v___x_4496_);
v___x_4498_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4499_ = lean_string_append(v___x_4497_, v___x_4498_);
v___x_4500_ = lean_mk_io_user_error(v___x_4499_);
if (v_isShared_4474_ == 0)
{
lean_ctor_set_tag(v___x_4473_, 1);
lean_ctor_set(v___x_4473_, 0, v___x_4500_);
v___x_4502_ = v___x_4473_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v___x_4500_);
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
else
{
lean_object* v_a_4505_; lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4512_; 
lean_dec_ref_known(v_entry_4469_, 3);
lean_dec_ref(v_env_4464_);
v_a_4505_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4507_ = v___x_4470_;
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
else
{
lean_inc(v_a_4505_);
lean_dec(v___x_4470_);
v___x_4507_ = lean_box(0);
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
v_resetjp_4506_:
{
lean_object* v___x_4510_; 
if (v_isShared_4508_ == 0)
{
v___x_4510_ = v___x_4507_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4505_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
return v___x_4510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4513_, lean_object* v_builderId_4514_, lean_object* v_ref_4515_, lean_object* v_args_4516_, lean_object* v_a_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l_Lean_registerAttributeOfBuilder(v_env_4513_, v_builderId_4514_, v_ref_4515_, v_args_4516_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
if (lean_obj_tag(v_x_4519_) == 0)
{
lean_object* v_a_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; 
v_a_4523_ = lean_ctor_get(v_x_4519_, 0);
lean_inc(v_a_4523_);
lean_dec_ref_known(v_x_4519_, 1);
v___x_4524_ = l_Lean_stringToMessageData(v_a_4523_);
v___x_4525_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4524_, v___y_4520_, v___y_4521_);
return v___x_4525_;
}
else
{
lean_object* v_a_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4533_; 
v_a_4526_ = lean_ctor_get(v_x_4519_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v_x_4519_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4528_ = v_x_4519_;
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_a_4526_);
lean_dec(v_x_4519_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4531_; 
if (v_isShared_4529_ == 0)
{
lean_ctor_set_tag(v___x_4528_, 0);
v___x_4531_ = v___x_4528_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_a_4526_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_){
_start:
{
lean_object* v_res_4538_; 
v_res_4538_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4534_, v___y_4535_, v___y_4536_);
lean_dec(v___y_4536_);
lean_dec_ref(v___y_4535_);
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4539_, lean_object* v_attrName_4540_, lean_object* v_stx_4541_, uint8_t v_kind_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_){
_start:
{
lean_object* v___x_4546_; lean_object* v_env_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4546_ = lean_st_ref_get(v_a_4544_);
v_env_4547_ = lean_ctor_get(v___x_4546_, 0);
lean_inc_ref(v_env_4547_);
lean_dec(v___x_4546_);
v___x_4548_ = l_Lean_getAttributeImpl(v_env_4547_, v_attrName_4540_);
v___x_4549_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4548_, v_a_4543_, v_a_4544_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v_a_4550_; lean_object* v_add_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; 
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
lean_inc(v_a_4550_);
lean_dec_ref_known(v___x_4549_, 1);
v_add_4551_ = lean_ctor_get(v_a_4550_, 1);
lean_inc_ref(v_add_4551_);
lean_dec(v_a_4550_);
v___x_4552_ = lean_box(v_kind_4542_);
lean_inc(v_a_4544_);
lean_inc_ref(v_a_4543_);
v___x_4553_ = lean_apply_6(v_add_4551_, v_declName_4539_, v_stx_4541_, v___x_4552_, v_a_4543_, v_a_4544_, lean_box(0));
return v___x_4553_;
}
else
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4561_; 
lean_dec(v_stx_4541_);
lean_dec(v_declName_4539_);
v_a_4554_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4556_ = v___x_4549_;
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v___x_4549_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4554_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4562_, lean_object* v_attrName_4563_, lean_object* v_stx_4564_, lean_object* v_kind_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_){
_start:
{
uint8_t v_kind_boxed_4569_; lean_object* v_res_4570_; 
v_kind_boxed_4569_ = lean_unbox(v_kind_4565_);
v_res_4570_ = l_Lean_Attribute_add(v_declName_4562_, v_attrName_4563_, v_stx_4564_, v_kind_boxed_4569_, v_a_4566_, v_a_4567_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4571_, lean_object* v_x_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_){
_start:
{
lean_object* v___x_4576_; 
v___x_4576_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4572_, v___y_4573_, v___y_4574_);
return v___x_4576_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4577_, lean_object* v_x_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_){
_start:
{
lean_object* v_res_4582_; 
v_res_4582_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4577_, v_x_4578_, v___y_4579_, v___y_4580_);
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
return v_res_4582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4583_, lean_object* v_attrName_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_){
_start:
{
lean_object* v___x_4588_; lean_object* v_env_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
v___x_4588_ = lean_st_ref_get(v_a_4586_);
v_env_4589_ = lean_ctor_get(v___x_4588_, 0);
lean_inc_ref(v_env_4589_);
lean_dec(v___x_4588_);
v___x_4590_ = l_Lean_getAttributeImpl(v_env_4589_, v_attrName_4584_);
v___x_4591_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4590_, v_a_4585_, v_a_4586_);
if (lean_obj_tag(v___x_4591_) == 0)
{
lean_object* v_a_4592_; lean_object* v_erase_4593_; lean_object* v___x_4594_; 
v_a_4592_ = lean_ctor_get(v___x_4591_, 0);
lean_inc(v_a_4592_);
lean_dec_ref_known(v___x_4591_, 1);
v_erase_4593_ = lean_ctor_get(v_a_4592_, 2);
lean_inc_ref(v_erase_4593_);
lean_dec(v_a_4592_);
lean_inc(v_a_4586_);
lean_inc_ref(v_a_4585_);
v___x_4594_ = lean_apply_4(v_erase_4593_, v_declName_4583_, v_a_4585_, v_a_4586_, lean_box(0));
return v___x_4594_;
}
else
{
lean_object* v_a_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4602_; 
lean_dec(v_declName_4583_);
v_a_4595_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4602_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4597_ = v___x_4591_;
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_a_4595_);
lean_dec(v___x_4591_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
lean_object* v___x_4600_; 
if (v_isShared_4598_ == 0)
{
v___x_4600_ = v___x_4597_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_a_4595_);
v___x_4600_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
return v___x_4600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4603_, lean_object* v_attrName_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_){
_start:
{
lean_object* v_res_4608_; 
v_res_4608_ = l_Lean_Attribute_erase(v_declName_4603_, v_attrName_4604_, v_a_4605_, v_a_4606_);
lean_dec(v_a_4606_);
lean_dec_ref(v_a_4605_);
return v_res_4608_;
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___lam__0(lean_object* v___y_4609_, lean_object* v_ps_4610_){
_start:
{
lean_object* v_importedEntries_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4618_; 
v_importedEntries_4611_ = lean_ctor_get(v_ps_4610_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v_ps_4610_);
if (v_isSharedCheck_4618_ == 0)
{
lean_object* v_unused_4619_; 
v_unused_4619_ = lean_ctor_get(v_ps_4610_, 1);
lean_dec(v_unused_4619_);
v___x_4613_ = v_ps_4610_;
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_importedEntries_4611_);
lean_dec(v_ps_4610_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4616_; 
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 1, v___y_4609_);
v___x_4616_ = v___x_4613_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_importedEntries_4611_);
lean_ctor_set(v_reuseFailAlloc_4617_, 1, v___y_4609_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
return v___x_4616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4620_, lean_object* v_x_4621_){
_start:
{
if (lean_obj_tag(v_x_4621_) == 0)
{
return v_x_4620_;
}
else
{
lean_object* v_key_4622_; lean_object* v_value_4623_; lean_object* v_tail_4624_; lean_object* v_newEntries_4625_; lean_object* v_map_4626_; uint8_t v___x_4627_; 
v_key_4622_ = lean_ctor_get(v_x_4621_, 0);
lean_inc(v_key_4622_);
v_value_4623_ = lean_ctor_get(v_x_4621_, 1);
lean_inc(v_value_4623_);
v_tail_4624_ = lean_ctor_get(v_x_4621_, 2);
lean_inc(v_tail_4624_);
lean_dec_ref_known(v_x_4621_, 3);
v_newEntries_4625_ = lean_ctor_get(v_x_4620_, 0);
v_map_4626_ = lean_ctor_get(v_x_4620_, 1);
v___x_4627_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4626_, v_key_4622_);
if (v___x_4627_ == 0)
{
lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4636_; 
lean_inc_ref(v_map_4626_);
lean_inc(v_newEntries_4625_);
v_isSharedCheck_4636_ = !lean_is_exclusive(v_x_4620_);
if (v_isSharedCheck_4636_ == 0)
{
lean_object* v_unused_4637_; lean_object* v_unused_4638_; 
v_unused_4637_ = lean_ctor_get(v_x_4620_, 1);
lean_dec(v_unused_4637_);
v_unused_4638_ = lean_ctor_get(v_x_4620_, 0);
lean_dec(v_unused_4638_);
v___x_4629_ = v_x_4620_;
v_isShared_4630_ = v_isSharedCheck_4636_;
goto v_resetjp_4628_;
}
else
{
lean_dec(v_x_4620_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4636_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v___x_4631_; lean_object* v___x_4633_; 
v___x_4631_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4626_, v_key_4622_, v_value_4623_);
if (v_isShared_4630_ == 0)
{
lean_ctor_set(v___x_4629_, 1, v___x_4631_);
v___x_4633_ = v___x_4629_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v_newEntries_4625_);
lean_ctor_set(v_reuseFailAlloc_4635_, 1, v___x_4631_);
v___x_4633_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
v_x_4620_ = v___x_4633_;
v_x_4621_ = v_tail_4624_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4623_);
lean_dec(v_key_4622_);
v_x_4621_ = v_tail_4624_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4640_, size_t v_i_4641_, size_t v_stop_4642_, lean_object* v_b_4643_){
_start:
{
uint8_t v___x_4644_; 
v___x_4644_ = lean_usize_dec_eq(v_i_4641_, v_stop_4642_);
if (v___x_4644_ == 0)
{
lean_object* v___x_4645_; lean_object* v___x_4646_; size_t v___x_4647_; size_t v___x_4648_; 
v___x_4645_ = lean_array_uget_borrowed(v_as_4640_, v_i_4641_);
lean_inc(v___x_4645_);
v___x_4646_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4643_, v___x_4645_);
v___x_4647_ = ((size_t)1ULL);
v___x_4648_ = lean_usize_add(v_i_4641_, v___x_4647_);
v_i_4641_ = v___x_4648_;
v_b_4643_ = v___x_4646_;
goto _start;
}
else
{
return v_b_4643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4650_, lean_object* v_i_4651_, lean_object* v_stop_4652_, lean_object* v_b_4653_){
_start:
{
size_t v_i_boxed_4654_; size_t v_stop_boxed_4655_; lean_object* v_res_4656_; 
v_i_boxed_4654_ = lean_unbox_usize(v_i_4651_);
lean_dec(v_i_4651_);
v_stop_boxed_4655_ = lean_unbox_usize(v_stop_4652_);
lean_dec(v_stop_4652_);
v_res_4656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4650_, v_i_boxed_4654_, v_stop_boxed_4655_, v_b_4653_);
lean_dec_ref(v_as_4650_);
return v_res_4656_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4657_){
_start:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___y_4664_; lean_object* v_toEnvExtension_4676_; lean_object* v_asyncMode_4677_; lean_object* v_buckets_4678_; lean_object* v___x_4679_; uint8_t v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; uint8_t v___x_4684_; 
v___x_4659_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4660_ = l_Lean_attributeMapRef;
v___x_4661_ = lean_st_ref_get(v___x_4660_);
v___x_4662_ = l_Lean_attributeExtension;
v_toEnvExtension_4676_ = lean_ctor_get(v___x_4662_, 0);
v_asyncMode_4677_ = lean_ctor_get(v_toEnvExtension_4676_, 2);
v_buckets_4678_ = lean_ctor_get(v___x_4661_, 1);
lean_inc_ref(v_buckets_4678_);
lean_dec(v___x_4661_);
v___x_4679_ = lean_box(0);
v___x_4680_ = 0;
lean_inc_ref(v_env_4657_);
v___x_4681_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4659_, v___x_4662_, v_env_4657_, v_asyncMode_4677_, v___x_4679_, v___x_4680_);
v___x_4682_ = lean_unsigned_to_nat(0u);
v___x_4683_ = lean_array_get_size(v_buckets_4678_);
v___x_4684_ = lean_nat_dec_lt(v___x_4682_, v___x_4683_);
if (v___x_4684_ == 0)
{
lean_dec_ref(v_buckets_4678_);
v___y_4664_ = v___x_4681_;
goto v___jp_4663_;
}
else
{
size_t v___x_4685_; size_t v___x_4686_; lean_object* v___x_4687_; 
v___x_4685_ = ((size_t)0ULL);
v___x_4686_ = lean_usize_of_nat(v___x_4683_);
v___x_4687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4678_, v___x_4685_, v___x_4686_, v___x_4681_);
lean_dec_ref(v_buckets_4678_);
v___y_4664_ = v___x_4687_;
goto v___jp_4663_;
}
v___jp_4663_:
{
lean_object* v_toEnvExtension_4665_; lean_object* v_asyncMode_4666_; uint8_t v_logWrites_4667_; lean_object* v___f_4668_; lean_object* v___x_4669_; uint8_t v___x_4670_; 
v_toEnvExtension_4665_ = lean_ctor_get(v___x_4662_, 0);
v_asyncMode_4666_ = lean_ctor_get(v_toEnvExtension_4665_, 2);
v_logWrites_4667_ = lean_ctor_get_uint8(v_toEnvExtension_4665_, sizeof(void*)*6);
v___f_4668_ = lean_alloc_closure((void*)(l_Lean_updateEnvAttributesImpl___lam__0), 2, 1);
lean_closure_set(v___f_4668_, 0, v___y_4664_);
v___x_4669_ = lean_box(0);
v___x_4670_ = 1;
if (v_logWrites_4667_ == 0)
{
lean_object* v___x_4671_; lean_object* v___x_4672_; 
lean_inc_ref(v_toEnvExtension_4665_);
v___x_4671_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4665_, v_env_4657_, v___f_4668_, v_asyncMode_4666_, v___x_4669_, v___x_4670_);
v___x_4672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4672_, 0, v___x_4671_);
return v___x_4672_;
}
else
{
lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; 
lean_inc_ref_n(v_toEnvExtension_4665_, 2);
v___x_4673_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4665_, v_env_4657_);
lean_dec_ref(v_env_4657_);
v___x_4674_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4665_, v___x_4673_, v___f_4668_, v_asyncMode_4666_, v___x_4669_, v___x_4670_);
v___x_4675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4675_, 0, v___x_4674_);
return v___x_4675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4688_, lean_object* v_a_4689_){
_start:
{
lean_object* v_res_4690_; 
v_res_4690_ = lean_update_env_attributes(v_env_4688_);
return v_res_4690_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v_size_4694_; lean_object* v___x_4695_; 
v___x_4692_ = l_Lean_attributeMapRef;
v___x_4693_ = lean_st_ref_get(v___x_4692_);
v_size_4694_ = lean_ctor_get(v___x_4693_, 0);
lean_inc(v_size_4694_);
lean_dec(v___x_4693_);
v___x_4695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4695_, 0, v_size_4694_);
return v___x_4695_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = lean_get_num_attributes();
return v_res_4697_;
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
