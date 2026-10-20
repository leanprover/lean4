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
uint8_t v___y_1034__boxed_314_; lean_object* v_res_315_; 
v___y_1034__boxed_314_ = lean_unbox(v___y_310_);
v_res_315_ = l_Lean_instInhabitedAttributeImpl_default___lam__0(v_x_308_, v___y_309_, v___y_1034__boxed_314_, v___y_311_, v___y_312_);
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
lean_object* v_toCold_664_; lean_object* v_currRecDepth_665_; lean_object* v_ref_666_; uint16_t v_optionFlags_667_; uint8_t v_suppressElabErrors_668_; uint8_t v_isRecordingDeps_669_; lean_object* v_ref_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_toCold_664_ = lean_ctor_get(v___y_661_, 0);
v_currRecDepth_665_ = lean_ctor_get(v___y_661_, 1);
v_ref_666_ = lean_ctor_get(v___y_661_, 2);
v_optionFlags_667_ = lean_ctor_get_uint16(v___y_661_, sizeof(void*)*3);
v_suppressElabErrors_668_ = lean_ctor_get_uint8(v___y_661_, sizeof(void*)*3 + 2);
v_isRecordingDeps_669_ = lean_ctor_get_uint8(v___y_661_, sizeof(void*)*3 + 3);
v_ref_670_ = l_Lean_replaceRef(v_ref_659_, v_ref_666_);
lean_inc(v_currRecDepth_665_);
lean_inc_ref(v_toCold_664_);
v___x_671_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_671_, 0, v_toCold_664_);
lean_ctor_set(v___x_671_, 1, v_currRecDepth_665_);
lean_ctor_set(v___x_671_, 2, v_ref_670_);
lean_ctor_set_uint16(v___x_671_, sizeof(void*)*3, v_optionFlags_667_);
lean_ctor_set_uint8(v___x_671_, sizeof(void*)*3 + 2, v_suppressElabErrors_668_);
lean_ctor_set_uint8(v___x_671_, sizeof(void*)*3 + 3, v_isRecordingDeps_669_);
v___x_672_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_660_, v___x_671_, v___y_662_);
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
lean_object* v___y_1327_; uint8_t v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; uint8_t v___y_1332_; lean_object* v___y_1333_; lean_object* v_toCold_1334_; lean_object* v___y_1335_; lean_object* v___y_1364_; lean_object* v___y_1365_; uint8_t v___y_1366_; uint8_t v___y_1367_; lean_object* v___y_1368_; uint8_t v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; uint8_t v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; uint8_t v___y_1394_; lean_object* v___y_1395_; uint8_t v___y_1396_; lean_object* v___y_1397_; uint8_t v___y_1401_; uint8_t v___y_1402_; uint8_t v___x_1412_; uint8_t v___y_1414_; uint8_t v___x_1420_; 
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
lean_ctor_set(v___x_1339_, 1, v___y_1333_);
lean_inc_ref(v___y_1329_);
lean_inc_ref(v___y_1330_);
v___x_1340_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1340_, 0, v___y_1330_);
lean_ctor_set(v___x_1340_, 1, v___y_1331_);
lean_ctor_set(v___x_1340_, 2, v___y_1327_);
lean_ctor_set(v___x_1340_, 3, v___y_1329_);
lean_ctor_set(v___x_1340_, 4, v___x_1339_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*5, v___y_1328_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*5 + 1, v___y_1332_);
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
v_fileName_1372_ = lean_ctor_get(v___y_1370_, 0);
v_fileMap_1373_ = lean_ctor_get(v___y_1370_, 1);
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
v___x_1380_ = l_Lean_FileMap_toPosition(v_fileMap_1373_, v___y_1368_);
lean_dec(v___y_1368_);
v___x_1381_ = l_Lean_FileMap_toPosition(v_fileMap_1373_, v___y_1371_);
lean_dec(v___y_1371_);
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
v___x_1383_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1367_ == 0)
{
lean_del_object(v___x_1378_);
lean_dec_ref(v___y_1364_);
v___y_1327_ = v___x_1382_;
v___y_1328_ = v___y_1366_;
v___y_1329_ = v___x_1383_;
v___y_1330_ = v_fileName_1372_;
v___y_1331_ = v___x_1380_;
v___y_1332_ = v___y_1369_;
v___y_1333_ = v_a_1376_;
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
v___y_1327_ = v___x_1382_;
v___y_1328_ = v___y_1366_;
v___y_1329_ = v___x_1383_;
v___y_1330_ = v_fileName_1372_;
v___y_1331_ = v___x_1380_;
v___y_1332_ = v___y_1369_;
v___y_1333_ = v_a_1376_;
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
v___x_1398_ = l_Lean_Syntax_getTailPos_x3f(v___y_1395_, v___y_1394_);
lean_dec(v___y_1395_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_inc(v___y_1397_);
v___y_1364_ = v___y_1392_;
v___y_1365_ = v___y_1393_;
v___y_1366_ = v___y_1394_;
v___y_1367_ = v___y_1391_;
v___y_1368_ = v___y_1397_;
v___y_1369_ = v___y_1396_;
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
v___y_1364_ = v___y_1392_;
v___y_1365_ = v___y_1393_;
v___y_1366_ = v___y_1394_;
v___y_1367_ = v___y_1391_;
v___y_1368_ = v___y_1397_;
v___y_1369_ = v___y_1396_;
v___y_1370_ = v___y_1393_;
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
v___y_1391_ = v_suppressElabErrors_1405_;
v___y_1392_ = v___f_1407_;
v___y_1393_ = v_toCold_1403_;
v___y_1394_ = v___y_1401_;
v___y_1395_ = v_ref_1408_;
v___y_1396_ = v___y_1402_;
v___y_1397_ = v___x_1410_;
goto v___jp_1390_;
}
else
{
lean_object* v_val_1411_; 
v_val_1411_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_val_1411_);
lean_dec_ref_known(v___x_1409_, 1);
v___y_1391_ = v_suppressElabErrors_1405_;
v___y_1392_ = v___f_1407_;
v___y_1393_ = v_toCold_1403_;
v___y_1394_ = v___y_1401_;
v___y_1395_ = v_ref_1408_;
v___y_1396_ = v___y_1402_;
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
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v___y_2304_, lean_object* v_as_2305_, lean_object* v_k_2306_, lean_object* v_x_2307_, lean_object* v_x_2308_){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v_m_2311_; lean_object* v_a_2312_; uint8_t v___x_2313_; 
v___x_2309_ = lean_nat_add(v_x_2307_, v_x_2308_);
v___x_2310_ = lean_unsigned_to_nat(1u);
v_m_2311_ = lean_nat_shiftr(v___x_2309_, v___x_2310_);
lean_dec(v___x_2309_);
v_a_2312_ = lean_array_fget_borrowed(v_as_2305_, v_m_2311_);
v___x_2313_ = l_Lean_Name_quickLt(v_a_2312_, v_k_2306_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; uint8_t v___x_2315_; 
lean_dec(v_x_2308_);
v___x_2314_ = lean_unsigned_to_nat(0u);
v___x_2315_ = l_Lean_Name_quickLt(v_k_2306_, v_a_2312_);
if (v___x_2315_ == 0)
{
uint8_t v___x_2316_; 
lean_dec(v_m_2311_);
lean_dec(v_x_2307_);
v___x_2316_ = lean_nat_dec_le(v___x_2314_, v___y_2304_);
return v___x_2316_;
}
else
{
uint8_t v___x_2317_; 
v___x_2317_ = lean_nat_dec_eq(v_m_2311_, v___x_2314_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___x_2318_ = lean_nat_sub(v_m_2311_, v___x_2310_);
lean_dec(v_m_2311_);
v___x_2319_ = lean_nat_dec_lt(v___x_2318_, v_x_2307_);
if (v___x_2319_ == 0)
{
v_x_2308_ = v___x_2318_;
goto _start;
}
else
{
lean_dec(v___x_2318_);
lean_dec(v_x_2307_);
return v___x_2317_;
}
}
else
{
lean_dec(v_m_2311_);
lean_dec(v_x_2307_);
return v___x_2313_;
}
}
}
else
{
lean_object* v___x_2321_; uint8_t v___x_2322_; 
lean_dec(v_x_2307_);
v___x_2321_ = lean_nat_add(v_m_2311_, v___x_2310_);
lean_dec(v_m_2311_);
v___x_2322_ = lean_nat_dec_le(v___x_2321_, v_x_2308_);
if (v___x_2322_ == 0)
{
lean_dec(v___x_2321_);
lean_dec(v_x_2308_);
return v___x_2322_;
}
else
{
v_x_2307_ = v___x_2321_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v___y_2324_, lean_object* v_as_2325_, lean_object* v_k_2326_, lean_object* v_x_2327_, lean_object* v_x_2328_){
_start:
{
uint8_t v_res_2329_; lean_object* v_r_2330_; 
v_res_2329_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2324_, v_as_2325_, v_k_2326_, v_x_2327_, v_x_2328_);
lean_dec(v_k_2326_);
lean_dec_ref(v_as_2325_);
lean_dec(v___y_2324_);
v_r_2330_ = lean_box(v_res_2329_);
return v_r_2330_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2331_, lean_object* v_env_2332_, lean_object* v_decl_2333_){
_start:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = lean_box(1);
v___x_2335_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2332_, v_decl_2333_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_ext_2336_; lean_object* v_toEnvExtension_2337_; lean_object* v_asyncMode_2338_; uint8_t v___x_2339_; lean_object* v___x_2340_; uint8_t v___x_2341_; 
v_ext_2336_ = lean_ctor_get(v_attr_2331_, 1);
v_toEnvExtension_2337_ = lean_ctor_get(v_ext_2336_, 0);
v_asyncMode_2338_ = lean_ctor_get(v_toEnvExtension_2337_, 2);
v___x_2339_ = 0;
lean_inc(v_decl_2333_);
v___x_2340_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2334_, v_ext_2336_, v_env_2332_, v_asyncMode_2338_, v_decl_2333_, v___x_2339_);
v___x_2341_ = l_Lean_NameSet_contains(v___x_2340_, v_decl_2333_);
lean_dec(v_decl_2333_);
lean_dec(v___x_2340_);
return v___x_2341_;
}
else
{
lean_object* v_val_2342_; lean_object* v_ext_2343_; uint8_t v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
v_val_2342_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_val_2342_);
lean_dec_ref_known(v___x_2335_, 1);
v_ext_2343_ = lean_ctor_get(v_attr_2331_, 1);
v___x_2344_ = 0;
v___x_2345_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2334_, v_ext_2343_, v_env_2332_, v_val_2342_, v___x_2344_);
lean_dec(v_val_2342_);
lean_dec_ref(v_env_2332_);
v___x_2346_ = lean_unsigned_to_nat(0u);
v___x_2347_ = lean_array_get_size(v___x_2345_);
v___x_2348_ = lean_nat_dec_lt(v___x_2346_, v___x_2347_);
if (v___x_2348_ == 0)
{
lean_dec_ref(v___x_2345_);
lean_dec(v_decl_2333_);
return v___x_2348_;
}
else
{
lean_object* v___x_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
v___x_2349_ = lean_unsigned_to_nat(1u);
v___x_2350_ = lean_nat_sub(v___x_2347_, v___x_2349_);
v___x_2351_ = lean_nat_dec_le(v___x_2346_, v___x_2350_);
if (v___x_2351_ == 0)
{
lean_dec(v___x_2350_);
lean_dec_ref(v___x_2345_);
lean_dec(v_decl_2333_);
return v___x_2351_;
}
else
{
uint8_t v___x_2352_; 
lean_inc(v___x_2350_);
v___x_2352_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2350_, v___x_2345_, v_decl_2333_, v___x_2346_, v___x_2350_);
lean_dec(v_decl_2333_);
lean_dec_ref(v___x_2345_);
lean_dec(v___x_2350_);
return v___x_2352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2353_, lean_object* v_env_2354_, lean_object* v_decl_2355_){
_start:
{
uint8_t v_res_2356_; lean_object* v_r_2357_; 
v_res_2356_ = l_Lean_TagAttribute_hasTag(v_attr_2353_, v_env_2354_, v_decl_2355_);
lean_dec_ref(v_attr_2353_);
v_r_2357_ = lean_box(v_res_2356_);
return v_r_2357_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v___y_2358_, lean_object* v_as_2359_, lean_object* v_k_2360_, lean_object* v_x_2361_, lean_object* v_x_2362_, lean_object* v_x_2363_){
_start:
{
uint8_t v___x_2364_; 
v___x_2364_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2358_, v_as_2359_, v_k_2360_, v_x_2361_, v_x_2362_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v___y_2365_, lean_object* v_as_2366_, lean_object* v_k_2367_, lean_object* v_x_2368_, lean_object* v_x_2369_, lean_object* v_x_2370_){
_start:
{
uint8_t v_res_2371_; lean_object* v_r_2372_; 
v_res_2371_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v___y_2365_, v_as_2366_, v_k_2367_, v_x_2368_, v_x_2369_, v_x_2370_);
lean_dec(v_k_2367_);
lean_dec_ref(v_as_2366_);
lean_dec(v___y_2365_);
v_r_2372_ = lean_box(v_res_2371_);
return v_r_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(lean_object* v_x_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0___boxed(lean_object* v_x_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(v_x_2378_, v___y_2379_);
lean_dec_ref(v___y_2379_);
lean_dec_ref(v_x_2378_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(lean_object* v_s_2382_, lean_object* v_x_2383_){
_start:
{
lean_inc_ref(v_s_2382_);
return v_s_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1___boxed(lean_object* v_s_2384_, lean_object* v_x_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(v_s_2384_, v_x_2385_);
lean_dec_ref(v_x_2385_);
lean_dec_ref(v_s_2384_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(lean_object* v_x_2391_, lean_object* v_x_2392_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___boxed(lean_object* v_x_2394_, lean_object* v_x_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(v_x_2394_, v_x_2395_);
lean_dec_ref(v_x_2395_);
lean_dec_ref(v_x_2394_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(lean_object* v_x_2397_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_box(0);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3___boxed(lean_object* v_x_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(v_x_2399_);
lean_dec_ref(v_x_2399_);
return v_res_2400_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4(void){
_start:
{
lean_object* v___f_2405_; lean_object* v___f_2406_; lean_object* v___f_2407_; lean_object* v___f_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___f_2405_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3));
v___f_2406_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2));
v___f_2407_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1));
v___f_2408_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0));
v___x_2409_ = lean_box(0);
v___x_2410_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_2411_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
lean_ctor_set(v___x_2411_, 1, v___x_2409_);
lean_ctor_set(v___x_2411_, 2, v___f_2408_);
lean_ctor_set(v___x_2411_, 3, v___f_2407_);
lean_ctor_set(v___x_2411_, 4, v___f_2406_);
lean_ctor_set(v___x_2411_, 5, v___f_2405_);
return v___x_2411_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5(void){
_start:
{
uint8_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2412_ = 0;
v___x_2413_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4);
v___x_2414_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2415_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
lean_ctor_set(v___x_2415_, 1, v___x_2413_);
lean_ctor_set_uint8(v___x_2415_, sizeof(void*)*2, v___x_2412_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg(){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___boxed(lean_object* v___dummy_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v_res_2419_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__0(void){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2421_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg(){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg___boxed(lean_object* v___dummy_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_instInhabitedParametricAttribute___redArg();
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2427_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object* v_x_2429_, lean_object* v_p_2430_){
_start:
{
lean_object* v_fst_2431_; lean_object* v_snd_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2449_; 
v_fst_2431_ = lean_ctor_get(v_x_2429_, 0);
v_snd_2432_ = lean_ctor_get(v_x_2429_, 1);
v_isSharedCheck_2449_ = !lean_is_exclusive(v_x_2429_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2434_ = v_x_2429_;
v_isShared_2435_ = v_isSharedCheck_2449_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_snd_2432_);
lean_inc(v_fst_2431_);
lean_dec(v_x_2429_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2449_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v_fst_2436_; lean_object* v_snd_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2448_; 
v_fst_2436_ = lean_ctor_get(v_p_2430_, 0);
v_snd_2437_ = lean_ctor_get(v_p_2430_, 1);
v_isSharedCheck_2448_ = !lean_is_exclusive(v_p_2430_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2439_ = v_p_2430_;
v_isShared_2440_ = v_isSharedCheck_2448_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_snd_2437_);
lean_inc(v_fst_2436_);
lean_dec(v_p_2430_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2448_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
lean_inc(v_fst_2436_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set_tag(v___x_2434_, 1);
lean_ctor_set(v___x_2434_, 1, v_fst_2431_);
lean_ctor_set(v___x_2434_, 0, v_fst_2436_);
v___x_2442_ = v___x_2434_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_fst_2436_);
lean_ctor_set(v_reuseFailAlloc_2447_, 1, v_fst_2431_);
v___x_2442_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
lean_object* v___x_2443_; lean_object* v___x_2445_; 
v___x_2443_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2436_, v_snd_2437_, v_snd_2432_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 1, v___x_2443_);
lean_ctor_set(v___x_2439_, 0, v___x_2442_);
v___x_2445_ = v___x_2439_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2442_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v___x_2443_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object* v_init_2450_, lean_object* v_x_2451_){
_start:
{
if (lean_obj_tag(v_x_2451_) == 0)
{
lean_object* v_k_2452_; lean_object* v_v_2453_; lean_object* v_l_2454_; lean_object* v_r_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v_k_2452_ = lean_ctor_get(v_x_2451_, 1);
v_v_2453_ = lean_ctor_get(v_x_2451_, 2);
v_l_2454_ = lean_ctor_get(v_x_2451_, 3);
v_r_2455_ = lean_ctor_get(v_x_2451_, 4);
v___x_2456_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2450_, v_l_2454_);
lean_inc(v_v_2453_);
lean_inc(v_k_2452_);
v___x_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2457_, 0, v_k_2452_);
lean_ctor_set(v___x_2457_, 1, v_v_2453_);
v___x_2458_ = lean_array_push(v___x_2456_, v___x_2457_);
v_init_2450_ = v___x_2458_;
v_x_2451_ = v_r_2455_;
goto _start;
}
else
{
return v_init_2450_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object* v_init_2460_, lean_object* v_x_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2460_, v_x_2461_);
lean_dec(v_x_2461_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object* v_snd_2463_, lean_object* v_as_2464_, size_t v_i_2465_, size_t v_stop_2466_, lean_object* v_b_2467_){
_start:
{
lean_object* v___y_2469_; uint8_t v___x_2473_; 
v___x_2473_ = lean_usize_dec_eq(v_i_2465_, v_stop_2466_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = lean_array_uget_borrowed(v_as_2464_, v_i_2465_);
v___x_2475_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2463_, v___x_2474_);
if (lean_obj_tag(v___x_2475_) == 0)
{
v___y_2469_ = v_b_2467_;
goto v___jp_2468_;
}
else
{
lean_object* v_val_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v_val_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_val_2476_);
lean_dec_ref_known(v___x_2475_, 1);
lean_inc(v___x_2474_);
v___x_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2474_);
lean_ctor_set(v___x_2477_, 1, v_val_2476_);
v___x_2478_ = lean_array_push(v_b_2467_, v___x_2477_);
v___y_2469_ = v___x_2478_;
goto v___jp_2468_;
}
}
else
{
return v_b_2467_;
}
v___jp_2468_:
{
size_t v___x_2470_; size_t v___x_2471_; 
v___x_2470_ = ((size_t)1ULL);
v___x_2471_ = lean_usize_add(v_i_2465_, v___x_2470_);
v_i_2465_ = v___x_2471_;
v_b_2467_ = v___y_2469_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2479_, lean_object* v_as_2480_, lean_object* v_i_2481_, lean_object* v_stop_2482_, lean_object* v_b_2483_){
_start:
{
size_t v_i_boxed_2484_; size_t v_stop_boxed_2485_; lean_object* v_res_2486_; 
v_i_boxed_2484_ = lean_unbox_usize(v_i_2481_);
lean_dec(v_i_2481_);
v_stop_boxed_2485_ = lean_unbox_usize(v_stop_2482_);
lean_dec(v_stop_2482_);
v_res_2486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2479_, v_as_2480_, v_i_boxed_2484_, v_stop_boxed_2485_, v_b_2483_);
lean_dec_ref(v_as_2480_);
lean_dec(v_snd_2479_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object* v_snd_2487_, lean_object* v_as_2488_, lean_object* v_start_2489_, lean_object* v_stop_2490_){
_start:
{
lean_object* v___x_2491_; uint8_t v___x_2492_; 
v___x_2491_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2492_ = lean_nat_dec_lt(v_start_2489_, v_stop_2490_);
if (v___x_2492_ == 0)
{
return v___x_2491_;
}
else
{
lean_object* v___x_2493_; uint8_t v___x_2494_; 
v___x_2493_ = lean_array_get_size(v_as_2488_);
v___x_2494_ = lean_nat_dec_le(v_stop_2490_, v___x_2493_);
if (v___x_2494_ == 0)
{
uint8_t v___x_2495_; 
v___x_2495_ = lean_nat_dec_lt(v_start_2489_, v___x_2493_);
if (v___x_2495_ == 0)
{
return v___x_2491_;
}
else
{
size_t v___x_2496_; size_t v___x_2497_; lean_object* v___x_2498_; 
v___x_2496_ = lean_usize_of_nat(v_start_2489_);
v___x_2497_ = lean_usize_of_nat(v___x_2493_);
v___x_2498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2487_, v_as_2488_, v___x_2496_, v___x_2497_, v___x_2491_);
return v___x_2498_;
}
}
else
{
size_t v___x_2499_; size_t v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = lean_usize_of_nat(v_start_2489_);
v___x_2500_ = lean_usize_of_nat(v_stop_2490_);
v___x_2501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2487_, v_as_2488_, v___x_2499_, v___x_2500_, v___x_2491_);
return v___x_2501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object* v_snd_2502_, lean_object* v_as_2503_, lean_object* v_start_2504_, lean_object* v_stop_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2502_, v_as_2503_, v_start_2504_, v_stop_2505_);
lean_dec(v_stop_2505_);
lean_dec(v_start_2504_);
lean_dec_ref(v_as_2503_);
lean_dec(v_snd_2502_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object* v_hi_2507_, lean_object* v_pivot_2508_, lean_object* v_as_2509_, lean_object* v_i_2510_, lean_object* v_k_2511_){
_start:
{
uint8_t v___x_2512_; 
v___x_2512_ = lean_nat_dec_lt(v_k_2511_, v_hi_2507_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
lean_dec(v_k_2511_);
v___x_2513_ = lean_array_fswap(v_as_2509_, v_i_2510_, v_hi_2507_);
v___x_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2514_, 0, v_i_2510_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
return v___x_2514_;
}
else
{
lean_object* v___x_2515_; lean_object* v_fst_2516_; lean_object* v_fst_2517_; uint8_t v___x_2518_; 
v___x_2515_ = lean_array_fget_borrowed(v_as_2509_, v_k_2511_);
v_fst_2516_ = lean_ctor_get(v___x_2515_, 0);
v_fst_2517_ = lean_ctor_get(v_pivot_2508_, 0);
v___x_2518_ = l_Lean_Name_quickLt(v_fst_2516_, v_fst_2517_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = lean_unsigned_to_nat(1u);
v___x_2520_ = lean_nat_add(v_k_2511_, v___x_2519_);
lean_dec(v_k_2511_);
v_k_2511_ = v___x_2520_;
goto _start;
}
else
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2522_ = lean_array_fswap(v_as_2509_, v_i_2510_, v_k_2511_);
v___x_2523_ = lean_unsigned_to_nat(1u);
v___x_2524_ = lean_nat_add(v_i_2510_, v___x_2523_);
lean_dec(v_i_2510_);
v___x_2525_ = lean_nat_add(v_k_2511_, v___x_2523_);
lean_dec(v_k_2511_);
v_as_2509_ = v___x_2522_;
v_i_2510_ = v___x_2524_;
v_k_2511_ = v___x_2525_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2527_, lean_object* v_pivot_2528_, lean_object* v_as_2529_, lean_object* v_i_2530_, lean_object* v_k_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2527_, v_pivot_2528_, v_as_2529_, v_i_2530_, v_k_2531_);
lean_dec_ref(v_pivot_2528_);
lean_dec(v_hi_2527_);
return v_res_2532_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object* v_a_2533_, lean_object* v_b_2534_){
_start:
{
lean_object* v_fst_2535_; lean_object* v_fst_2536_; uint8_t v___x_2537_; 
v_fst_2535_ = lean_ctor_get(v_a_2533_, 0);
v_fst_2536_ = lean_ctor_get(v_b_2534_, 0);
v___x_2537_ = l_Lean_Name_quickLt(v_fst_2535_, v_fst_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object* v_a_2538_, lean_object* v_b_2539_){
_start:
{
uint8_t v_res_2540_; lean_object* v_r_2541_; 
v_res_2540_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2538_, v_b_2539_);
lean_dec_ref(v_b_2539_);
lean_dec_ref(v_a_2538_);
v_r_2541_ = lean_box(v_res_2540_);
return v_r_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object* v_n_2542_, lean_object* v_as_2543_, lean_object* v_lo_2544_, lean_object* v_hi_2545_){
_start:
{
lean_object* v___y_2547_; uint8_t v___x_2557_; 
v___x_2557_ = lean_nat_dec_lt(v_lo_2544_, v_hi_2545_);
if (v___x_2557_ == 0)
{
lean_dec(v_lo_2544_);
return v_as_2543_;
}
else
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v_mid_2560_; lean_object* v___y_2562_; lean_object* v___y_2568_; lean_object* v___x_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v___x_2558_ = lean_nat_add(v_lo_2544_, v_hi_2545_);
v___x_2559_ = lean_unsigned_to_nat(1u);
v_mid_2560_ = lean_nat_shiftr(v___x_2558_, v___x_2559_);
lean_dec(v___x_2558_);
v___x_2573_ = lean_array_fget_borrowed(v_as_2543_, v_mid_2560_);
v___x_2574_ = lean_array_fget_borrowed(v_as_2543_, v_lo_2544_);
v___x_2575_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2573_, v___x_2574_);
if (v___x_2575_ == 0)
{
v___y_2568_ = v_as_2543_;
goto v___jp_2567_;
}
else
{
lean_object* v___x_2576_; 
v___x_2576_ = lean_array_fswap(v_as_2543_, v_lo_2544_, v_mid_2560_);
v___y_2568_ = v___x_2576_;
goto v___jp_2567_;
}
v___jp_2561_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
v___x_2563_ = lean_array_fget_borrowed(v___y_2562_, v_mid_2560_);
v___x_2564_ = lean_array_fget_borrowed(v___y_2562_, v_hi_2545_);
v___x_2565_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2563_, v___x_2564_);
if (v___x_2565_ == 0)
{
lean_dec(v_mid_2560_);
v___y_2547_ = v___y_2562_;
goto v___jp_2546_;
}
else
{
lean_object* v___x_2566_; 
v___x_2566_ = lean_array_fswap(v___y_2562_, v_mid_2560_, v_hi_2545_);
lean_dec(v_mid_2560_);
v___y_2547_ = v___x_2566_;
goto v___jp_2546_;
}
}
v___jp_2567_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v___x_2569_ = lean_array_fget_borrowed(v___y_2568_, v_hi_2545_);
v___x_2570_ = lean_array_fget_borrowed(v___y_2568_, v_lo_2544_);
v___x_2571_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2569_, v___x_2570_);
if (v___x_2571_ == 0)
{
v___y_2562_ = v___y_2568_;
goto v___jp_2561_;
}
else
{
lean_object* v___x_2572_; 
v___x_2572_ = lean_array_fswap(v___y_2568_, v_lo_2544_, v_hi_2545_);
v___y_2562_ = v___x_2572_;
goto v___jp_2561_;
}
}
}
v___jp_2546_:
{
lean_object* v_pivot_2548_; lean_object* v___x_2549_; lean_object* v_fst_2550_; lean_object* v_snd_2551_; uint8_t v___x_2552_; 
v_pivot_2548_ = lean_array_fget(v___y_2547_, v_hi_2545_);
lean_inc_n(v_lo_2544_, 2);
v___x_2549_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2545_, v_pivot_2548_, v___y_2547_, v_lo_2544_, v_lo_2544_);
lean_dec(v_pivot_2548_);
v_fst_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_fst_2550_);
v_snd_2551_ = lean_ctor_get(v___x_2549_, 1);
lean_inc(v_snd_2551_);
lean_dec_ref(v___x_2549_);
v___x_2552_ = lean_nat_dec_le(v_hi_2545_, v_fst_2550_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2553_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2542_, v_snd_2551_, v_lo_2544_, v_fst_2550_);
v___x_2554_ = lean_unsigned_to_nat(1u);
v___x_2555_ = lean_nat_add(v_fst_2550_, v___x_2554_);
lean_dec(v_fst_2550_);
v_as_2543_ = v___x_2553_;
v_lo_2544_ = v___x_2555_;
goto _start;
}
else
{
lean_dec(v_fst_2550_);
lean_dec(v_lo_2544_);
return v_snd_2551_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object* v_n_2577_, lean_object* v_as_2578_, lean_object* v_lo_2579_, lean_object* v_hi_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2577_, v_as_2578_, v_lo_2579_, v_hi_2580_);
lean_dec(v_hi_2580_);
lean_dec(v_n_2577_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object* v_filterExport_2582_, lean_object* v_env_2583_, lean_object* v_as_2584_, size_t v_i_2585_, size_t v_stop_2586_, lean_object* v_b_2587_){
_start:
{
lean_object* v___y_2589_; uint8_t v___x_2593_; 
v___x_2593_ = lean_usize_dec_eq(v_i_2585_, v_stop_2586_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; lean_object* v_fst_2595_; lean_object* v_snd_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; 
v___x_2594_ = lean_array_uget_borrowed(v_as_2584_, v_i_2585_);
v_fst_2595_ = lean_ctor_get(v___x_2594_, 0);
v_snd_2596_ = lean_ctor_get(v___x_2594_, 1);
lean_inc_ref(v_filterExport_2582_);
lean_inc(v_snd_2596_);
lean_inc(v_fst_2595_);
lean_inc_ref(v_env_2583_);
v___x_2597_ = lean_apply_3(v_filterExport_2582_, v_env_2583_, v_fst_2595_, v_snd_2596_);
v___x_2598_ = lean_unbox(v___x_2597_);
if (v___x_2598_ == 0)
{
v___y_2589_ = v_b_2587_;
goto v___jp_2588_;
}
else
{
lean_object* v___x_2599_; 
lean_inc(v___x_2594_);
v___x_2599_ = lean_array_push(v_b_2587_, v___x_2594_);
v___y_2589_ = v___x_2599_;
goto v___jp_2588_;
}
}
else
{
lean_dec_ref(v_env_2583_);
lean_dec_ref(v_filterExport_2582_);
return v_b_2587_;
}
v___jp_2588_:
{
size_t v___x_2590_; size_t v___x_2591_; 
v___x_2590_ = ((size_t)1ULL);
v___x_2591_ = lean_usize_add(v_i_2585_, v___x_2590_);
v_i_2585_ = v___x_2591_;
v_b_2587_ = v___y_2589_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object* v_filterExport_2600_, lean_object* v_env_2601_, lean_object* v_as_2602_, lean_object* v_i_2603_, lean_object* v_stop_2604_, lean_object* v_b_2605_){
_start:
{
size_t v_i_boxed_2606_; size_t v_stop_boxed_2607_; lean_object* v_res_2608_; 
v_i_boxed_2606_ = lean_unbox_usize(v_i_2603_);
lean_dec(v_i_2603_);
v_stop_boxed_2607_ = lean_unbox_usize(v_stop_2604_);
lean_dec(v_stop_2604_);
v_res_2608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2600_, v_env_2601_, v_as_2602_, v_i_boxed_2606_, v_stop_boxed_2607_, v_b_2605_);
lean_dec_ref(v_as_2602_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object* v_filterExport_2609_, uint8_t v_preserveOrder_2610_, lean_object* v_env_2611_, lean_object* v_x_2612_){
_start:
{
lean_object* v___y_2614_; 
if (v_preserveOrder_2610_ == 0)
{
lean_object* v_snd_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v_r_2627_; lean_object* v___x_2628_; lean_object* v___y_2630_; lean_object* v___y_2631_; uint8_t v___x_2633_; 
v_snd_2624_ = lean_ctor_get(v_x_2612_, 1);
lean_inc(v_snd_2624_);
lean_dec_ref(v_x_2612_);
v___x_2625_ = lean_unsigned_to_nat(0u);
v___x_2626_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v_r_2627_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_2626_, v_snd_2624_);
lean_dec(v_snd_2624_);
v___x_2628_ = lean_array_get_size(v_r_2627_);
v___x_2633_ = lean_nat_dec_eq(v___x_2628_, v___x_2625_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___y_2637_; uint8_t v___x_2639_; 
v___x_2634_ = lean_unsigned_to_nat(1u);
v___x_2635_ = lean_nat_sub(v___x_2628_, v___x_2634_);
v___x_2639_ = lean_nat_dec_le(v___x_2625_, v___x_2635_);
if (v___x_2639_ == 0)
{
lean_inc(v___x_2635_);
v___y_2637_ = v___x_2635_;
goto v___jp_2636_;
}
else
{
v___y_2637_ = v___x_2625_;
goto v___jp_2636_;
}
v___jp_2636_:
{
uint8_t v___x_2638_; 
v___x_2638_ = lean_nat_dec_le(v___y_2637_, v___x_2635_);
if (v___x_2638_ == 0)
{
lean_dec(v___x_2635_);
lean_inc(v___y_2637_);
v___y_2630_ = v___y_2637_;
v___y_2631_ = v___y_2637_;
goto v___jp_2629_;
}
else
{
v___y_2630_ = v___y_2637_;
v___y_2631_ = v___x_2635_;
goto v___jp_2629_;
}
}
}
else
{
v___y_2614_ = v_r_2627_;
goto v___jp_2613_;
}
v___jp_2629_:
{
lean_object* v___x_2632_; 
v___x_2632_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_2628_, v_r_2627_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
v___y_2614_ = v___x_2632_;
goto v___jp_2613_;
}
}
else
{
lean_object* v_fst_2640_; lean_object* v_snd_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v_fst_2640_ = lean_ctor_get(v_x_2612_, 0);
lean_inc(v_fst_2640_);
v_snd_2641_ = lean_ctor_get(v_x_2612_, 1);
lean_inc(v_snd_2641_);
lean_dec_ref(v_x_2612_);
v___x_2642_ = lean_array_mk(v_fst_2640_);
v___x_2643_ = l_Array_reverse___redArg(v___x_2642_);
v___x_2644_ = lean_unsigned_to_nat(0u);
v___x_2645_ = lean_array_get_size(v___x_2643_);
v___x_2646_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2641_, v___x_2643_, v___x_2644_, v___x_2645_);
lean_dec_ref(v___x_2643_);
lean_dec(v_snd_2641_);
v___y_2614_ = v___x_2646_;
goto v___jp_2613_;
}
v___jp_2613_:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2615_ = lean_unsigned_to_nat(0u);
v___x_2616_ = lean_array_get_size(v___y_2614_);
v___x_2617_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2618_ = lean_nat_dec_lt(v___x_2615_, v___x_2616_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; 
lean_dec_ref(v_env_2611_);
lean_dec_ref(v_filterExport_2609_);
v___x_2619_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2617_);
lean_ctor_set(v___x_2619_, 1, v___x_2617_);
lean_ctor_set(v___x_2619_, 2, v___y_2614_);
return v___x_2619_;
}
else
{
size_t v___x_2620_; size_t v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2620_ = ((size_t)0ULL);
v___x_2621_ = lean_usize_of_nat(v___x_2616_);
v___x_2622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2609_, v_env_2611_, v___y_2614_, v___x_2620_, v___x_2621_, v___x_2617_);
lean_inc_ref(v___x_2622_);
v___x_2623_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
lean_ctor_set(v___x_2623_, 2, v___y_2614_);
return v___x_2623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object* v_filterExport_2647_, lean_object* v_preserveOrder_2648_, lean_object* v_env_2649_, lean_object* v_x_2650_){
_start:
{
uint8_t v_preserveOrder_boxed_2651_; lean_object* v_res_2652_; 
v_preserveOrder_boxed_2651_ = lean_unbox(v_preserveOrder_2648_);
v_res_2652_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2647_, v_preserveOrder_boxed_2651_, v_env_2649_, v_x_2650_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object* v_x_2662_){
_start:
{
lean_object* v_snd_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2677_; 
v_snd_2663_ = lean_ctor_get(v_x_2662_, 1);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_x_2662_);
if (v_isSharedCheck_2677_ == 0)
{
lean_object* v_unused_2678_; 
v_unused_2678_ = lean_ctor_get(v_x_2662_, 0);
lean_dec(v_unused_2678_);
v___x_2665_ = v_x_2662_;
v_isShared_2666_ = v_isSharedCheck_2677_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_snd_2663_);
lean_dec(v_x_2662_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2677_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; lean_object* v___y_2669_; 
v___x_2667_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2663_) == 0)
{
lean_object* v_size_2675_; 
v_size_2675_ = lean_ctor_get(v_snd_2663_, 0);
lean_inc(v_size_2675_);
lean_dec_ref_known(v_snd_2663_, 5);
v___y_2669_ = v_size_2675_;
goto v___jp_2668_;
}
else
{
lean_object* v___x_2676_; 
v___x_2676_ = lean_unsigned_to_nat(0u);
v___y_2669_ = v___x_2676_;
goto v___jp_2668_;
}
v___jp_2668_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2670_ = l_Nat_reprFast(v___y_2669_);
v___x_2671_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set_tag(v___x_2665_, 5);
lean_ctor_set(v___x_2665_, 1, v___x_2671_);
lean_ctor_set(v___x_2665_, 0, v___x_2667_);
v___x_2673_ = v___x_2665_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object* v_x_2679_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object* v_x_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l_Lean_registerParametricAttributeExt___redArg___lam__3(v_x_2681_);
lean_dec_ref(v_x_2681_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object* v___x_2683_){
_start:
{
lean_object* v___x_2685_; 
v___x_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2683_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object* v___x_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2686_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object* v___x_2689_, lean_object* v_x_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2689_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object* v___x_2694_, lean_object* v_x_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2694_, v_x_2695_, v___y_2696_);
lean_dec_ref(v___y_2696_);
lean_dec_ref(v_x_2695_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object* v_ref_2709_, uint8_t v_preserveOrder_2710_, lean_object* v_filterExport_2711_, uint8_t v_logWrites_2712_){
_start:
{
lean_object* v___f_2714_; lean_object* v___x_2715_; lean_object* v___f_2716_; lean_object* v___f_2717_; lean_object* v___f_2718_; lean_object* v___f_2719_; lean_object* v___f_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; uint8_t v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___f_2714_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__0));
v___x_2715_ = lean_box(v_preserveOrder_2710_);
v___f_2716_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2716_, 0, v_filterExport_2711_);
lean_closure_set(v___f_2716_, 1, v___x_2715_);
v___f_2717_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__1));
v___f_2718_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__2));
v___f_2719_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__4));
v___f_2720_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__5));
v___x_2721_ = lean_box(2);
v___x_2722_ = lean_box(0);
v___x_2723_ = 0;
v___x_2724_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2724_, 0, v_ref_2709_);
lean_ctor_set(v___x_2724_, 1, v___f_2719_);
lean_ctor_set(v___x_2724_, 2, v___f_2720_);
lean_ctor_set(v___x_2724_, 3, v___f_2714_);
lean_ctor_set(v___x_2724_, 4, v___f_2716_);
lean_ctor_set(v___x_2724_, 5, v___f_2717_);
lean_ctor_set(v___x_2724_, 6, v___x_2721_);
lean_ctor_set(v___x_2724_, 7, v___x_2722_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*8, v___x_2723_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*8 + 1, v_logWrites_2712_);
v___x_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
lean_ctor_set(v___x_2725_, 1, v___f_2718_);
v___x_2726_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object* v_ref_2727_, lean_object* v_preserveOrder_2728_, lean_object* v_filterExport_2729_, lean_object* v_logWrites_2730_, lean_object* v_a_2731_){
_start:
{
uint8_t v_preserveOrder_boxed_2732_; uint8_t v_logWrites_boxed_2733_; lean_object* v_res_2734_; 
v_preserveOrder_boxed_2732_ = lean_unbox(v_preserveOrder_2728_);
v_logWrites_boxed_2733_ = lean_unbox(v_logWrites_2730_);
v_res_2734_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2727_, v_preserveOrder_boxed_2732_, v_filterExport_2729_, v_logWrites_boxed_2733_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object* v_00_u03b1_2735_, lean_object* v_ref_2736_, uint8_t v_preserveOrder_2737_, lean_object* v_filterExport_2738_, uint8_t v_logWrites_2739_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2736_, v_preserveOrder_2737_, v_filterExport_2738_, v_logWrites_2739_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object* v_00_u03b1_2742_, lean_object* v_ref_2743_, lean_object* v_preserveOrder_2744_, lean_object* v_filterExport_2745_, lean_object* v_logWrites_2746_, lean_object* v_a_2747_){
_start:
{
uint8_t v_preserveOrder_boxed_2748_; uint8_t v_logWrites_boxed_2749_; lean_object* v_res_2750_; 
v_preserveOrder_boxed_2748_ = lean_unbox(v_preserveOrder_2744_);
v_logWrites_boxed_2749_ = lean_unbox(v_logWrites_2746_);
v_res_2750_ = l_Lean_registerParametricAttributeExt(v_00_u03b1_2742_, v_ref_2743_, v_preserveOrder_boxed_2748_, v_filterExport_2745_, v_logWrites_boxed_2749_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object* v_00_u03b1_2751_, lean_object* v_filterExport_2752_, lean_object* v_env_2753_, lean_object* v_as_2754_, size_t v_i_2755_, size_t v_stop_2756_, lean_object* v_b_2757_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2752_, v_env_2753_, v_as_2754_, v_i_2755_, v_stop_2756_, v_b_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object* v_00_u03b1_2759_, lean_object* v_filterExport_2760_, lean_object* v_env_2761_, lean_object* v_as_2762_, lean_object* v_i_2763_, lean_object* v_stop_2764_, lean_object* v_b_2765_){
_start:
{
size_t v_i_boxed_2766_; size_t v_stop_boxed_2767_; lean_object* v_res_2768_; 
v_i_boxed_2766_ = lean_unbox_usize(v_i_2763_);
lean_dec(v_i_2763_);
v_stop_boxed_2767_ = lean_unbox_usize(v_stop_2764_);
lean_dec(v_stop_2764_);
v_res_2768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(v_00_u03b1_2759_, v_filterExport_2760_, v_env_2761_, v_as_2762_, v_i_boxed_2766_, v_stop_boxed_2767_, v_b_2765_);
lean_dec_ref(v_as_2762_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object* v_init_2769_, lean_object* v_t_2770_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2769_, v_t_2770_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object* v_init_2772_, lean_object* v_t_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(v_init_2772_, v_t_2773_);
lean_dec(v_t_2773_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object* v_00_u03b1_2775_, lean_object* v_init_2776_, lean_object* v_t_2777_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2776_, v_t_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object* v_00_u03b1_2779_, lean_object* v_init_2780_, lean_object* v_t_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(v_00_u03b1_2779_, v_init_2780_, v_t_2781_);
lean_dec(v_t_2781_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object* v_00_u03b1_2783_, lean_object* v_n_2784_, lean_object* v_as_2785_, lean_object* v_lo_2786_, lean_object* v_hi_2787_, lean_object* v_w_2788_, lean_object* v_hlo_2789_, lean_object* v_hhi_2790_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2784_, v_as_2785_, v_lo_2786_, v_hi_2787_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object* v_00_u03b1_2792_, lean_object* v_n_2793_, lean_object* v_as_2794_, lean_object* v_lo_2795_, lean_object* v_hi_2796_, lean_object* v_w_2797_, lean_object* v_hlo_2798_, lean_object* v_hhi_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(v_00_u03b1_2792_, v_n_2793_, v_as_2794_, v_lo_2795_, v_hi_2796_, v_w_2797_, v_hlo_2798_, v_hhi_2799_);
lean_dec(v_hi_2796_);
lean_dec(v_n_2793_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object* v_00_u03b1_2801_, lean_object* v_snd_2802_, lean_object* v_as_2803_, lean_object* v_start_2804_, lean_object* v_stop_2805_){
_start:
{
lean_object* v___x_2806_; 
v___x_2806_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2802_, v_as_2803_, v_start_2804_, v_stop_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object* v_00_u03b1_2807_, lean_object* v_snd_2808_, lean_object* v_as_2809_, lean_object* v_start_2810_, lean_object* v_stop_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(v_00_u03b1_2807_, v_snd_2808_, v_as_2809_, v_start_2810_, v_stop_2811_);
lean_dec(v_stop_2811_);
lean_dec(v_start_2810_);
lean_dec_ref(v_as_2809_);
lean_dec(v_snd_2808_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object* v_00_u03b1_2813_, lean_object* v_init_2814_, lean_object* v_x_2815_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2814_, v_x_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2817_, lean_object* v_init_2818_, lean_object* v_x_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(v_00_u03b1_2817_, v_init_2818_, v_x_2819_);
lean_dec(v_x_2819_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object* v_00_u03b1_2821_, lean_object* v_n_2822_, lean_object* v_lo_2823_, lean_object* v_hi_2824_, lean_object* v_hhi_2825_, lean_object* v_pivot_2826_, lean_object* v_as_2827_, lean_object* v_i_2828_, lean_object* v_k_2829_, lean_object* v_ilo_2830_, lean_object* v_ik_2831_, lean_object* v_w_2832_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2824_, v_pivot_2826_, v_as_2827_, v_i_2828_, v_k_2829_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2834_, lean_object* v_n_2835_, lean_object* v_lo_2836_, lean_object* v_hi_2837_, lean_object* v_hhi_2838_, lean_object* v_pivot_2839_, lean_object* v_as_2840_, lean_object* v_i_2841_, lean_object* v_k_2842_, lean_object* v_ilo_2843_, lean_object* v_ik_2844_, lean_object* v_w_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(v_00_u03b1_2834_, v_n_2835_, v_lo_2836_, v_hi_2837_, v_hhi_2838_, v_pivot_2839_, v_as_2840_, v_i_2841_, v_k_2842_, v_ilo_2843_, v_ik_2844_, v_w_2845_);
lean_dec_ref(v_pivot_2839_);
lean_dec(v_hi_2837_);
lean_dec(v_lo_2836_);
lean_dec(v_n_2835_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object* v_00_u03b1_2847_, lean_object* v_snd_2848_, lean_object* v_as_2849_, size_t v_i_2850_, size_t v_stop_2851_, lean_object* v_b_2852_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2848_, v_as_2849_, v_i_2850_, v_stop_2851_, v_b_2852_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2854_, lean_object* v_snd_2855_, lean_object* v_as_2856_, lean_object* v_i_2857_, lean_object* v_stop_2858_, lean_object* v_b_2859_){
_start:
{
size_t v_i_boxed_2860_; size_t v_stop_boxed_2861_; lean_object* v_res_2862_; 
v_i_boxed_2860_ = lean_unbox_usize(v_i_2857_);
lean_dec(v_i_2857_);
v_stop_boxed_2861_ = lean_unbox_usize(v_stop_2858_);
lean_dec(v_stop_2858_);
v_res_2862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(v_00_u03b1_2854_, v_snd_2855_, v_as_2856_, v_i_boxed_2860_, v_stop_boxed_2861_, v_b_2859_);
lean_dec_ref(v_as_2856_);
lean_dec(v_snd_2855_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object* v_env_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v___x_2866_; lean_object* v_nextMacroScope_2867_; lean_object* v_ngen_2868_; lean_object* v_auxDeclNGen_2869_; lean_object* v_traceState_2870_; lean_object* v_recordedDeps_2871_; lean_object* v_messages_2872_; lean_object* v_infoState_2873_; lean_object* v_snapshotTasks_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2885_; 
v___x_2866_ = lean_st_ref_take(v___y_2864_);
v_nextMacroScope_2867_ = lean_ctor_get(v___x_2866_, 1);
v_ngen_2868_ = lean_ctor_get(v___x_2866_, 2);
v_auxDeclNGen_2869_ = lean_ctor_get(v___x_2866_, 3);
v_traceState_2870_ = lean_ctor_get(v___x_2866_, 4);
v_recordedDeps_2871_ = lean_ctor_get(v___x_2866_, 6);
v_messages_2872_ = lean_ctor_get(v___x_2866_, 7);
v_infoState_2873_ = lean_ctor_get(v___x_2866_, 8);
v_snapshotTasks_2874_ = lean_ctor_get(v___x_2866_, 9);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2885_ == 0)
{
lean_object* v_unused_2886_; lean_object* v_unused_2887_; 
v_unused_2886_ = lean_ctor_get(v___x_2866_, 5);
lean_dec(v_unused_2886_);
v_unused_2887_ = lean_ctor_get(v___x_2866_, 0);
lean_dec(v_unused_2887_);
v___x_2876_ = v___x_2866_;
v_isShared_2877_ = v_isSharedCheck_2885_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_snapshotTasks_2874_);
lean_inc(v_infoState_2873_);
lean_inc(v_messages_2872_);
lean_inc(v_recordedDeps_2871_);
lean_inc(v_traceState_2870_);
lean_inc(v_auxDeclNGen_2869_);
lean_inc(v_ngen_2868_);
lean_inc(v_nextMacroScope_2867_);
lean_dec(v___x_2866_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2885_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2881_; 
v___x_2878_ = lean_box(0);
v___x_2879_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 5, v___x_2879_);
lean_ctor_set(v___x_2876_, 0, v_env_2863_);
v___x_2881_ = v___x_2876_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_env_2863_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v_nextMacroScope_2867_);
lean_ctor_set(v_reuseFailAlloc_2884_, 2, v_ngen_2868_);
lean_ctor_set(v_reuseFailAlloc_2884_, 3, v_auxDeclNGen_2869_);
lean_ctor_set(v_reuseFailAlloc_2884_, 4, v_traceState_2870_);
lean_ctor_set(v_reuseFailAlloc_2884_, 5, v___x_2879_);
lean_ctor_set(v_reuseFailAlloc_2884_, 6, v_recordedDeps_2871_);
lean_ctor_set(v_reuseFailAlloc_2884_, 7, v_messages_2872_);
lean_ctor_set(v_reuseFailAlloc_2884_, 8, v_infoState_2873_);
lean_ctor_set(v_reuseFailAlloc_2884_, 9, v_snapshotTasks_2874_);
v___x_2881_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2882_ = lean_st_ref_put(v___y_2864_, v___x_2881_);
v___x_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2878_);
return v___x_2883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object* v_env_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2888_, v___y_2889_);
lean_dec(v___y_2889_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object* v_env_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v___x_2896_; 
v___x_2896_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2892_, v___y_2894_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object* v_env_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(v_env_2897_, v___y_2898_, v___y_2899_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object* v_addEntryFn_2902_, lean_object* v___x_2903_, lean_object* v_s_2904_){
_start:
{
lean_object* v_importedEntries_2905_; lean_object* v_state_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2914_; 
v_importedEntries_2905_ = lean_ctor_get(v_s_2904_, 0);
v_state_2906_ = lean_ctor_get(v_s_2904_, 1);
v_isSharedCheck_2914_ = !lean_is_exclusive(v_s_2904_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2908_ = v_s_2904_;
v_isShared_2909_ = v_isSharedCheck_2914_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_state_2906_);
lean_inc(v_importedEntries_2905_);
lean_dec(v_s_2904_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2914_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v_state_2910_; lean_object* v___x_2912_; 
v_state_2910_ = lean_apply_2(v_addEntryFn_2902_, v_state_2906_, v___x_2903_);
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 1, v_state_2910_);
v___x_2912_ = v___x_2908_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_importedEntries_2905_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_state_2910_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object* v_afterSet_2915_, lean_object* v_getParam_2916_, lean_object* v_ext_2917_, lean_object* v_toAttributeImplCore_2918_, lean_object* v_decl_2919_, lean_object* v_stx_2920_, uint8_t v_kind_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v___y_2926_; lean_object* v_nextMacroScope_2927_; lean_object* v_ngen_2928_; lean_object* v_auxDeclNGen_2929_; lean_object* v_traceState_2930_; lean_object* v_recordedDeps_2931_; lean_object* v_messages_2932_; lean_object* v_infoState_2933_; lean_object* v_snapshotTasks_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; uint8_t v___x_2987_; uint8_t v___x_2988_; 
v___x_2987_ = 0;
v___x_2988_ = l_Lean_instBEqAttributeKind_beq(v_kind_2921_, v___x_2987_);
if (v___x_2988_ == 0)
{
lean_object* v_name_2989_; lean_object* v___x_2990_; 
lean_dec(v_stx_2920_);
lean_dec(v_decl_2919_);
lean_dec_ref(v_ext_2917_);
lean_dec_ref(v_getParam_2916_);
lean_dec_ref(v_afterSet_2915_);
v_name_2989_ = lean_ctor_get(v_toAttributeImplCore_2918_, 1);
lean_inc(v_name_2989_);
lean_dec_ref(v_toAttributeImplCore_2918_);
v___x_2990_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2989_, v_kind_2921_, v___y_2922_, v___y_2923_);
return v___x_2990_;
}
else
{
goto v___jp_2981_;
}
v___jp_2925_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2939_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_2940_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2940_, 0, v___y_2938_);
lean_ctor_set(v___x_2940_, 1, v_nextMacroScope_2927_);
lean_ctor_set(v___x_2940_, 2, v_ngen_2928_);
lean_ctor_set(v___x_2940_, 3, v_auxDeclNGen_2929_);
lean_ctor_set(v___x_2940_, 4, v_traceState_2930_);
lean_ctor_set(v___x_2940_, 5, v___x_2939_);
lean_ctor_set(v___x_2940_, 6, v_recordedDeps_2931_);
lean_ctor_set(v___x_2940_, 7, v_messages_2932_);
lean_ctor_set(v___x_2940_, 8, v_infoState_2933_);
lean_ctor_set(v___x_2940_, 9, v_snapshotTasks_2934_);
v___x_2941_ = lean_st_ref_put(v___y_2936_, v___x_2940_);
lean_inc(v___y_2936_);
lean_inc_ref(v___y_2937_);
v___x_2942_ = lean_apply_5(v_afterSet_2915_, v_decl_2919_, v___y_2935_, v___y_2937_, v___y_2936_, lean_box(0));
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_dec_ref(v___y_2926_);
return v___x_2942_;
}
else
{
lean_object* v_a_2943_; uint8_t v___x_2944_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
v___x_2944_ = l_Lean_Exception_isInterrupt(v_a_2943_);
if (v___x_2944_ == 0)
{
uint8_t v___x_2945_; 
v___x_2945_ = l_Lean_Exception_isRuntime(v_a_2943_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; 
lean_dec_ref_known(v___x_2942_, 1);
v___x_2946_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v___y_2926_, v___y_2936_);
return v___x_2946_;
}
else
{
lean_dec_ref(v___y_2926_);
return v___x_2942_;
}
}
else
{
lean_dec(v_a_2943_);
lean_dec_ref(v___y_2926_);
return v___x_2942_;
}
}
}
v___jp_2947_:
{
lean_object* v___x_2951_; 
lean_inc(v___y_2950_);
lean_inc_ref(v___y_2949_);
lean_inc(v_decl_2919_);
v___x_2951_ = lean_apply_5(v_getParam_2916_, v_decl_2919_, v_stx_2920_, v___y_2949_, v___y_2950_, lean_box(0));
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2953_; lean_object* v_toEnvExtension_2954_; lean_object* v_env_2955_; lean_object* v_nextMacroScope_2956_; lean_object* v_ngen_2957_; lean_object* v_auxDeclNGen_2958_; lean_object* v_traceState_2959_; lean_object* v_recordedDeps_2960_; lean_object* v_messages_2961_; lean_object* v_infoState_2962_; lean_object* v_snapshotTasks_2963_; lean_object* v_addEntryFn_2964_; lean_object* v_asyncMode_2965_; uint8_t v_logWrites_2966_; lean_object* v___x_2967_; lean_object* v___f_2968_; uint8_t v___x_2969_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc_n(v_a_2952_, 2);
lean_dec_ref_known(v___x_2951_, 1);
v___x_2953_ = lean_st_ref_take(v___y_2950_);
v_toEnvExtension_2954_ = lean_ctor_get(v_ext_2917_, 0);
lean_inc_ref(v_toEnvExtension_2954_);
v_env_2955_ = lean_ctor_get(v___x_2953_, 0);
lean_inc_ref(v_env_2955_);
v_nextMacroScope_2956_ = lean_ctor_get(v___x_2953_, 1);
lean_inc(v_nextMacroScope_2956_);
v_ngen_2957_ = lean_ctor_get(v___x_2953_, 2);
lean_inc_ref(v_ngen_2957_);
v_auxDeclNGen_2958_ = lean_ctor_get(v___x_2953_, 3);
lean_inc_ref(v_auxDeclNGen_2958_);
v_traceState_2959_ = lean_ctor_get(v___x_2953_, 4);
lean_inc_ref(v_traceState_2959_);
v_recordedDeps_2960_ = lean_ctor_get(v___x_2953_, 6);
lean_inc_ref(v_recordedDeps_2960_);
v_messages_2961_ = lean_ctor_get(v___x_2953_, 7);
lean_inc_ref(v_messages_2961_);
v_infoState_2962_ = lean_ctor_get(v___x_2953_, 8);
lean_inc_ref(v_infoState_2962_);
v_snapshotTasks_2963_ = lean_ctor_get(v___x_2953_, 9);
lean_inc_ref(v_snapshotTasks_2963_);
lean_dec(v___x_2953_);
v_addEntryFn_2964_ = lean_ctor_get(v_ext_2917_, 3);
lean_inc(v_addEntryFn_2964_);
lean_dec_ref(v_ext_2917_);
v_asyncMode_2965_ = lean_ctor_get(v_toEnvExtension_2954_, 2);
lean_inc(v_asyncMode_2965_);
v_logWrites_2966_ = lean_ctor_get_uint8(v_toEnvExtension_2954_, sizeof(void*)*6);
lean_inc(v_decl_2919_);
v___x_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2967_, 0, v_decl_2919_);
lean_ctor_set(v___x_2967_, 1, v_a_2952_);
v___f_2968_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2968_, 0, v_addEntryFn_2964_);
lean_closure_set(v___f_2968_, 1, v___x_2967_);
v___x_2969_ = 1;
if (v_logWrites_2966_ == 0)
{
lean_object* v___x_2970_; 
lean_inc(v_decl_2919_);
v___x_2970_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2954_, v_env_2955_, v___f_2968_, v_asyncMode_2965_, v_decl_2919_, v___x_2969_);
lean_dec(v_asyncMode_2965_);
v___y_2926_ = v___y_2948_;
v_nextMacroScope_2927_ = v_nextMacroScope_2956_;
v_ngen_2928_ = v_ngen_2957_;
v_auxDeclNGen_2929_ = v_auxDeclNGen_2958_;
v_traceState_2930_ = v_traceState_2959_;
v_recordedDeps_2931_ = v_recordedDeps_2960_;
v_messages_2932_ = v_messages_2961_;
v_infoState_2933_ = v_infoState_2962_;
v_snapshotTasks_2934_ = v_snapshotTasks_2963_;
v___y_2935_ = v_a_2952_;
v___y_2936_ = v___y_2950_;
v___y_2937_ = v___y_2949_;
v___y_2938_ = v___x_2970_;
goto v___jp_2925_;
}
else
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
lean_inc_n(v_decl_2919_, 2);
v___x_2971_ = l_Lean_Environment_logDeclChange(v_env_2955_, v_decl_2919_);
v___x_2972_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2954_, v___x_2971_, v___f_2968_, v_asyncMode_2965_, v_decl_2919_, v___x_2969_);
lean_dec(v_asyncMode_2965_);
v___y_2926_ = v___y_2948_;
v_nextMacroScope_2927_ = v_nextMacroScope_2956_;
v_ngen_2928_ = v_ngen_2957_;
v_auxDeclNGen_2929_ = v_auxDeclNGen_2958_;
v_traceState_2930_ = v_traceState_2959_;
v_recordedDeps_2931_ = v_recordedDeps_2960_;
v_messages_2932_ = v_messages_2961_;
v_infoState_2933_ = v_infoState_2962_;
v_snapshotTasks_2934_ = v_snapshotTasks_2963_;
v___y_2935_ = v_a_2952_;
v___y_2936_ = v___y_2950_;
v___y_2937_ = v___y_2949_;
v___y_2938_ = v___x_2972_;
goto v___jp_2925_;
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec_ref(v___y_2948_);
lean_dec(v_decl_2919_);
lean_dec_ref(v_ext_2917_);
lean_dec_ref(v_afterSet_2915_);
v_a_2973_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2951_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2951_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
v___jp_2981_:
{
lean_object* v___x_2982_; lean_object* v_env_2983_; lean_object* v___x_2984_; 
v___x_2982_ = lean_st_ref_get(v___y_2923_);
v_env_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc_ref(v_env_2983_);
lean_dec(v___x_2982_);
v___x_2984_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2983_, v_decl_2919_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_dec_ref(v_toAttributeImplCore_2918_);
v___y_2948_ = v_env_2983_;
v___y_2949_ = v___y_2922_;
v___y_2950_ = v___y_2923_;
goto v___jp_2947_;
}
else
{
lean_object* v_name_2985_; lean_object* v___x_2986_; 
lean_dec_ref_known(v___x_2984_, 1);
lean_dec_ref(v_env_2983_);
lean_dec(v_stx_2920_);
lean_dec_ref(v_ext_2917_);
lean_dec_ref(v_getParam_2916_);
lean_dec_ref(v_afterSet_2915_);
v_name_2985_ = lean_ctor_get(v_toAttributeImplCore_2918_, 1);
lean_inc(v_name_2985_);
lean_dec_ref(v_toAttributeImplCore_2918_);
v___x_2986_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2985_, v_decl_2919_, v___y_2922_, v___y_2923_);
return v___x_2986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object* v_afterSet_2991_, lean_object* v_getParam_2992_, lean_object* v_ext_2993_, lean_object* v_toAttributeImplCore_2994_, lean_object* v_decl_2995_, lean_object* v_stx_2996_, lean_object* v_kind_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
uint8_t v_kind_boxed_3001_; lean_object* v_res_3002_; 
v_kind_boxed_3001_ = lean_unbox(v_kind_2997_);
v_res_3002_ = l_Lean_registerParametricAttributeForExt___redArg___lam__1(v_afterSet_2991_, v_getParam_2992_, v_ext_2993_, v_toAttributeImplCore_2994_, v_decl_2995_, v_stx_2996_, v_kind_boxed_3001_, v___y_2998_, v___y_2999_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__2(lean_object* v_toAttributeImplCore_3003_, lean_object* v_decl_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v_name_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v_name_3008_ = lean_ctor_get(v_toAttributeImplCore_3003_, 1);
lean_inc(v_name_3008_);
lean_dec_ref(v_toAttributeImplCore_3003_);
v___x_3009_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3010_ = l_Lean_MessageData_ofName(v_name_3008_);
v___x_3011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3009_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
v___x_3012_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3011_);
lean_ctor_set(v___x_3013_, 1, v___x_3012_);
v___x_3014_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3013_, v___y_3005_, v___y_3006_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__2___boxed(lean_object* v_toAttributeImplCore_3015_, lean_object* v_decl_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_Lean_registerParametricAttributeForExt___redArg___lam__2(v_toAttributeImplCore_3015_, v_decl_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v_decl_3016_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object* v_impl_3021_, lean_object* v_ext_3022_){
_start:
{
lean_object* v_toAttributeImplCore_3024_; lean_object* v_getParam_3025_; lean_object* v_afterSet_3026_; uint8_t v_preserveOrder_3027_; lean_object* v___f_3028_; lean_object* v___f_3029_; lean_object* v_attrImpl_3030_; lean_object* v___x_3031_; 
v_toAttributeImplCore_3024_ = lean_ctor_get(v_impl_3021_, 0);
lean_inc_ref_n(v_toAttributeImplCore_3024_, 3);
v_getParam_3025_ = lean_ctor_get(v_impl_3021_, 1);
lean_inc_ref(v_getParam_3025_);
v_afterSet_3026_ = lean_ctor_get(v_impl_3021_, 2);
lean_inc_ref(v_afterSet_3026_);
v_preserveOrder_3027_ = lean_ctor_get_uint8(v_impl_3021_, sizeof(void*)*4);
lean_dec_ref(v_impl_3021_);
lean_inc_ref(v_ext_3022_);
v___f_3028_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3028_, 0, v_afterSet_3026_);
lean_closure_set(v___f_3028_, 1, v_getParam_3025_);
lean_closure_set(v___f_3028_, 2, v_ext_3022_);
lean_closure_set(v___f_3028_, 3, v_toAttributeImplCore_3024_);
v___f_3029_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__2___boxed), 5, 1);
lean_closure_set(v___f_3029_, 0, v_toAttributeImplCore_3024_);
v_attrImpl_3030_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_attrImpl_3030_, 0, v_toAttributeImplCore_3024_);
lean_ctor_set(v_attrImpl_3030_, 1, v___f_3028_);
lean_ctor_set(v_attrImpl_3030_, 2, v___f_3029_);
lean_inc_ref(v_attrImpl_3030_);
v___x_3031_ = l_Lean_registerBuiltinAttribute(v_attrImpl_3030_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3039_; 
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3039_ == 0)
{
lean_object* v_unused_3040_; 
v_unused_3040_ = lean_ctor_get(v___x_3031_, 0);
lean_dec(v_unused_3040_);
v___x_3033_ = v___x_3031_;
v_isShared_3034_ = v_isSharedCheck_3039_;
goto v_resetjp_3032_;
}
else
{
lean_dec(v___x_3031_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3039_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3035_; lean_object* v___x_3037_; 
v___x_3035_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3035_, 0, v_attrImpl_3030_);
lean_ctor_set(v___x_3035_, 1, v_ext_3022_);
lean_ctor_set_uint8(v___x_3035_, sizeof(void*)*2, v_preserveOrder_3027_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v___x_3035_);
v___x_3037_ = v___x_3033_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3035_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
else
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_dec_ref_known(v_attrImpl_3030_, 3);
lean_dec_ref(v_ext_3022_);
v_a_3041_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_3031_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3031_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object* v_impl_3049_, lean_object* v_ext_3050_, lean_object* v_a_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3049_, v_ext_3050_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object* v_00_u03b1_3053_, lean_object* v_impl_3054_, lean_object* v_ext_3055_){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3054_, v_ext_3055_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object* v_00_u03b1_3058_, lean_object* v_impl_3059_, lean_object* v_ext_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_Lean_registerParametricAttributeForExt(v_00_u03b1_3058_, v_impl_3059_, v_ext_3060_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_3063_){
_start:
{
lean_object* v_toAttributeImplCore_3065_; uint8_t v_preserveOrder_3066_; lean_object* v_filterExport_3067_; lean_object* v_ref_3068_; uint8_t v___x_3069_; lean_object* v___x_3070_; 
v_toAttributeImplCore_3065_ = lean_ctor_get(v_impl_3063_, 0);
v_preserveOrder_3066_ = lean_ctor_get_uint8(v_impl_3063_, sizeof(void*)*4);
v_filterExport_3067_ = lean_ctor_get(v_impl_3063_, 3);
v_ref_3068_ = lean_ctor_get(v_toAttributeImplCore_3065_, 0);
v___x_3069_ = 0;
lean_inc_ref(v_filterExport_3067_);
lean_inc(v_ref_3068_);
v___x_3070_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_3068_, v_preserveOrder_3066_, v_filterExport_3067_, v___x_3069_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; lean_object* v___x_3072_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3071_);
lean_dec_ref_known(v___x_3070_, 1);
v___x_3072_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3063_, v_a_3071_);
return v___x_3072_;
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_dec_ref(v_impl_3063_);
v_a_3073_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3070_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3070_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_3081_, lean_object* v_a_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l_Lean_registerParametricAttribute___redArg(v_impl_3081_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_3084_, lean_object* v_impl_3085_){
_start:
{
lean_object* v___x_3087_; 
v___x_3087_ = l_Lean_registerParametricAttribute___redArg(v_impl_3085_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_3088_, lean_object* v_impl_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lean_registerParametricAttribute(v_00_u03b1_3088_, v_impl_3089_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(lean_object* v_decl_3092_, lean_object* v___x_3093_, lean_object* v___x_3094_, lean_object* v_a_3095_, lean_object* v_x_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v_fst_3098_; uint8_t v___x_3099_; 
v_fst_3098_ = lean_ctor_get(v_a_3095_, 0);
v___x_3099_ = lean_name_eq(v_fst_3098_, v_decl_3092_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; 
lean_dec_ref(v_a_3095_);
v___x_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3093_);
return v___x_3100_;
}
else
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
lean_dec_ref(v___x_3093_);
v___x_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3101_, 0, v_a_3095_);
v___x_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3101_);
v___x_3103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
lean_ctor_set(v___x_3103_, 1, v___x_3094_);
v___x_3104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3103_);
return v___x_3104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed(lean_object* v_decl_3105_, lean_object* v___x_3106_, lean_object* v___x_3107_, lean_object* v_a_3108_, lean_object* v_x_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(v_decl_3105_, v___x_3106_, v___x_3107_, v_a_3108_, v_x_3109_, v___y_3110_);
lean_dec_ref(v___y_3110_);
lean_dec(v_decl_3105_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object* v_inst_3139_, lean_object* v_ext_3140_, uint8_t v_preserveOrder_3141_, lean_object* v_env_3142_, lean_object* v_decl_3143_){
_start:
{
lean_object* v___y_3145_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3156_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3157_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3142_, v_decl_3143_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_toEnvExtension_3158_; lean_object* v_asyncMode_3159_; lean_object* v___x_3160_; uint8_t v___x_3161_; lean_object* v___x_3162_; lean_object* v_snd_3163_; lean_object* v___x_3164_; 
lean_dec(v_inst_3139_);
v_toEnvExtension_3158_ = lean_ctor_get(v_ext_3140_, 0);
v_asyncMode_3159_ = lean_ctor_get(v_toEnvExtension_3158_, 2);
v___x_3160_ = lean_box(0);
v___x_3161_ = 0;
v___x_3162_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3156_, v_ext_3140_, v_env_3142_, v_asyncMode_3159_, v___x_3160_, v___x_3161_);
v_snd_3163_ = lean_ctor_get(v___x_3162_, 1);
lean_inc(v_snd_3163_);
lean_dec(v___x_3162_);
v___x_3164_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3163_, v_decl_3143_);
lean_dec(v_decl_3143_);
lean_dec(v_snd_3163_);
return v___x_3164_;
}
else
{
if (v_preserveOrder_3141_ == 0)
{
lean_object* v_val_3165_; uint8_t v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; uint8_t v___x_3170_; 
v_val_3165_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_val_3165_);
lean_dec_ref_known(v___x_3157_, 1);
v___x_3166_ = 0;
v___x_3167_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3156_, v_ext_3140_, v_env_3142_, v_val_3165_, v___x_3166_);
lean_dec(v_val_3165_);
lean_dec_ref(v_env_3142_);
v___x_3168_ = lean_unsigned_to_nat(0u);
v___x_3169_ = lean_array_get_size(v___x_3167_);
v___x_3170_ = lean_nat_dec_lt(v___x_3168_, v___x_3169_);
if (v___x_3170_ == 0)
{
lean_object* v___x_3171_; 
lean_dec_ref(v___x_3167_);
lean_dec(v_decl_3143_);
lean_dec(v_inst_3139_);
v___x_3171_ = lean_box(0);
return v___x_3171_;
}
else
{
lean_object* v___x_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; 
v___x_3172_ = lean_unsigned_to_nat(1u);
v___x_3173_ = lean_nat_sub(v___x_3169_, v___x_3172_);
v___x_3174_ = lean_nat_dec_le(v___x_3168_, v___x_3173_);
if (v___x_3174_ == 0)
{
lean_object* v___x_3175_; 
lean_dec(v___x_3173_);
lean_dec_ref(v___x_3167_);
lean_dec(v_decl_3143_);
lean_dec(v_inst_3139_);
v___x_3175_ = lean_box(0);
return v___x_3175_;
}
else
{
lean_object* v___f_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___f_3176_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v_decl_3143_);
lean_ctor_set(v___x_3177_, 1, v_inst_3139_);
v___x_3178_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3179_ = l_Array_binSearchAux___redArg(v___f_3176_, v___x_3178_, v___x_3167_, v___x_3177_, v___x_3168_, v___x_3173_);
lean_dec_ref(v___x_3167_);
v___y_3145_ = v___x_3179_;
goto v___jp_3144_;
}
}
}
else
{
lean_object* v_val_3180_; uint8_t v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___f_3187_; size_t v_sz_3188_; size_t v___x_3189_; lean_object* v___x_3190_; lean_object* v_fst_3191_; 
lean_dec(v_inst_3139_);
v_val_3180_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_val_3180_);
lean_dec_ref_known(v___x_3157_, 1);
v___x_3181_ = 0;
v___x_3182_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3156_, v_ext_3140_, v_env_3142_, v_val_3180_, v___x_3181_);
lean_dec(v_val_3180_);
lean_dec_ref(v_env_3142_);
v___x_3183_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12));
v___x_3184_ = lean_box(0);
v___x_3185_ = lean_box(0);
v___x_3186_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13));
v___f_3187_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3187_, 0, v_decl_3143_);
lean_closure_set(v___f_3187_, 1, v___x_3186_);
lean_closure_set(v___f_3187_, 2, v___x_3185_);
v_sz_3188_ = lean_array_size(v___x_3182_);
v___x_3189_ = ((size_t)0ULL);
v___x_3190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3183_, v___x_3182_, v___f_3187_, v_sz_3188_, v___x_3189_, v___x_3186_);
v_fst_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc(v_fst_3191_);
lean_dec(v___x_3190_);
if (lean_obj_tag(v_fst_3191_) == 0)
{
return v___x_3184_;
}
else
{
lean_object* v_val_3192_; 
v_val_3192_ = lean_ctor_get(v_fst_3191_, 0);
lean_inc(v_val_3192_);
lean_dec_ref_known(v_fst_3191_, 1);
v___y_3145_ = v_val_3192_;
goto v___jp_3144_;
}
}
}
v___jp_3144_:
{
if (lean_obj_tag(v___y_3145_) == 0)
{
lean_object* v___x_3146_; 
v___x_3146_ = lean_box(0);
return v___x_3146_;
}
else
{
lean_object* v_val_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3155_; 
v_val_3147_ = lean_ctor_get(v___y_3145_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___y_3145_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3149_ = v___y_3145_;
v_isShared_3150_ = v_isSharedCheck_3155_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_val_3147_);
lean_dec(v___y_3145_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3155_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v_snd_3151_; lean_object* v___x_3153_; 
v_snd_3151_ = lean_ctor_get(v_val_3147_, 1);
lean_inc(v_snd_3151_);
lean_dec(v_val_3147_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 0, v_snd_3151_);
v___x_3153_ = v___x_3149_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_snd_3151_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object* v_inst_3193_, lean_object* v_ext_3194_, lean_object* v_preserveOrder_3195_, lean_object* v_env_3196_, lean_object* v_decl_3197_){
_start:
{
uint8_t v_preserveOrder_boxed_3198_; lean_object* v_res_3199_; 
v_preserveOrder_boxed_3198_ = lean_unbox(v_preserveOrder_3195_);
v_res_3199_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3193_, v_ext_3194_, v_preserveOrder_boxed_3198_, v_env_3196_, v_decl_3197_);
lean_dec_ref(v_ext_3194_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object* v_00_u03b1_3200_, lean_object* v_inst_3201_, lean_object* v_ext_3202_, uint8_t v_preserveOrder_3203_, lean_object* v_env_3204_, lean_object* v_decl_3205_){
_start:
{
lean_object* v___x_3206_; 
v___x_3206_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3201_, v_ext_3202_, v_preserveOrder_3203_, v_env_3204_, v_decl_3205_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object* v_00_u03b1_3207_, lean_object* v_inst_3208_, lean_object* v_ext_3209_, lean_object* v_preserveOrder_3210_, lean_object* v_env_3211_, lean_object* v_decl_3212_){
_start:
{
uint8_t v_preserveOrder_boxed_3213_; lean_object* v_res_3214_; 
v_preserveOrder_boxed_3213_ = lean_unbox(v_preserveOrder_3210_);
v_res_3214_ = l_Lean_ParametricAttribute_getParamFromExt_x3f(v_00_u03b1_3207_, v_inst_3208_, v_ext_3209_, v_preserveOrder_boxed_3213_, v_env_3211_, v_decl_3212_);
lean_dec_ref(v_ext_3209_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3215_, lean_object* v_attr_3216_, lean_object* v_env_3217_, lean_object* v_decl_3218_){
_start:
{
lean_object* v_ext_3219_; uint8_t v_preserveOrder_3220_; lean_object* v___x_3221_; 
v_ext_3219_ = lean_ctor_get(v_attr_3216_, 1);
v_preserveOrder_3220_ = lean_ctor_get_uint8(v_attr_3216_, sizeof(void*)*2);
v___x_3221_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3215_, v_ext_3219_, v_preserveOrder_3220_, v_env_3217_, v_decl_3218_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3222_, lean_object* v_attr_3223_, lean_object* v_env_3224_, lean_object* v_decl_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3222_, v_attr_3223_, v_env_3224_, v_decl_3225_);
lean_dec_ref(v_attr_3223_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3227_, lean_object* v_inst_3228_, lean_object* v_attr_3229_, lean_object* v_env_3230_, lean_object* v_decl_3231_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3228_, v_attr_3229_, v_env_3230_, v_decl_3231_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3233_, lean_object* v_inst_3234_, lean_object* v_attr_3235_, lean_object* v_env_3236_, lean_object* v_decl_3237_){
_start:
{
lean_object* v_res_3238_; 
v_res_3238_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3233_, v_inst_3234_, v_attr_3235_, v_env_3236_, v_decl_3237_);
lean_dec_ref(v_attr_3235_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object* v_ext_3243_, lean_object* v_attr_3244_, lean_object* v_env_3245_, lean_object* v_decl_3246_, lean_object* v_param_3247_){
_start:
{
lean_object* v___x_3248_; 
v___x_3248_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3245_, v_decl_3246_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_toEnvExtension_3249_; lean_object* v_addEntryFn_3250_; lean_object* v_asyncMode_3251_; uint8_t v_logWrites_3252_; uint8_t v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v_snd_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3292_; 
v_toEnvExtension_3249_ = lean_ctor_get(v_ext_3243_, 0);
lean_inc_ref(v_toEnvExtension_3249_);
v_addEntryFn_3250_ = lean_ctor_get(v_ext_3243_, 3);
lean_inc(v_addEntryFn_3250_);
v_asyncMode_3251_ = lean_ctor_get(v_toEnvExtension_3249_, 2);
lean_inc(v_asyncMode_3251_);
v_logWrites_3252_ = lean_ctor_get_uint8(v_toEnvExtension_3249_, sizeof(void*)*6);
v___x_3253_ = 0;
v___x_3254_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3255_ = lean_box(0);
lean_inc_ref(v_env_3245_);
v___x_3256_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3254_, v_ext_3243_, v_env_3245_, v_asyncMode_3251_, v___x_3255_, v___x_3253_);
lean_dec_ref(v_ext_3243_);
v_snd_3257_ = lean_ctor_get(v___x_3256_, 1);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3292_ == 0)
{
lean_object* v_unused_3293_; 
v_unused_3293_ = lean_ctor_get(v___x_3256_, 0);
lean_dec(v_unused_3293_);
v___x_3259_ = v___x_3256_;
v_isShared_3260_ = v_isSharedCheck_3292_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_snd_3257_);
lean_dec(v___x_3256_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3292_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3261_; 
v___x_3261_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3257_, v_decl_3246_);
lean_dec(v_snd_3257_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v___x_3263_; 
lean_dec_ref(v_attr_3244_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set(v___x_3259_, 1, v_param_3247_);
lean_ctor_set(v___x_3259_, 0, v_decl_3246_);
v___x_3263_ = v___x_3259_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_decl_3246_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_param_3247_);
v___x_3263_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
lean_object* v___f_3264_; uint8_t v___x_3265_; 
v___f_3264_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3264_, 0, v_addEntryFn_3250_);
lean_closure_set(v___f_3264_, 1, v___x_3263_);
v___x_3265_ = 1;
if (v_logWrites_3252_ == 0)
{
lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3266_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3249_, v_env_3245_, v___f_3264_, v_asyncMode_3251_, v___x_3255_, v___x_3265_);
lean_dec(v_asyncMode_3251_);
v___x_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
return v___x_3267_;
}
else
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
lean_inc_ref(v_toEnvExtension_3249_);
v___x_3268_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3249_, v_env_3245_);
lean_dec_ref(v_env_3245_);
v___x_3269_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3249_, v___x_3268_, v___f_3264_, v_asyncMode_3251_, v___x_3255_, v___x_3265_);
lean_dec(v_asyncMode_3251_);
v___x_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3269_);
return v___x_3270_;
}
}
}
else
{
lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3290_; 
lean_del_object(v___x_3259_);
lean_dec(v_asyncMode_3251_);
lean_dec(v_addEntryFn_3250_);
lean_dec_ref(v_toEnvExtension_3249_);
lean_dec(v_param_3247_);
lean_dec_ref(v_env_3245_);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3290_ == 0)
{
lean_object* v_unused_3291_; 
v_unused_3291_ = lean_ctor_get(v___x_3261_, 0);
lean_dec(v_unused_3291_);
v___x_3273_ = v___x_3261_;
v_isShared_3274_ = v_isSharedCheck_3290_;
goto v_resetjp_3272_;
}
else
{
lean_dec(v___x_3261_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3290_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v_toAttributeImplCore_3275_; lean_object* v_name_3276_; uint8_t v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3288_; 
v_toAttributeImplCore_3275_ = lean_ctor_get(v_attr_3244_, 0);
lean_inc_ref(v_toAttributeImplCore_3275_);
lean_dec_ref(v_attr_3244_);
v_name_3276_ = lean_ctor_get(v_toAttributeImplCore_3275_, 1);
lean_inc(v_name_3276_);
lean_dec_ref(v_toAttributeImplCore_3275_);
v___x_3277_ = 1;
v___x_3278_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3279_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3276_, v___x_3277_);
v___x_3280_ = lean_string_append(v___x_3278_, v___x_3279_);
lean_dec_ref(v___x_3279_);
v___x_3281_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3282_ = lean_string_append(v___x_3280_, v___x_3281_);
v___x_3283_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3246_, v___x_3277_);
v___x_3284_ = lean_string_append(v___x_3282_, v___x_3283_);
lean_dec_ref(v___x_3283_);
v___x_3285_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2));
v___x_3286_ = lean_string_append(v___x_3284_, v___x_3285_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set_tag(v___x_3273_, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3286_);
v___x_3288_ = v___x_3273_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3286_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
}
else
{
lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3312_; 
lean_dec(v_param_3247_);
lean_dec_ref(v_env_3245_);
lean_dec_ref(v_ext_3243_);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3312_ == 0)
{
lean_object* v_unused_3313_; 
v_unused_3313_ = lean_ctor_get(v___x_3248_, 0);
lean_dec(v_unused_3313_);
v___x_3295_ = v___x_3248_;
v_isShared_3296_ = v_isSharedCheck_3312_;
goto v_resetjp_3294_;
}
else
{
lean_dec(v___x_3248_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3312_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v_toAttributeImplCore_3297_; lean_object* v_name_3298_; uint8_t v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3310_; 
v_toAttributeImplCore_3297_ = lean_ctor_get(v_attr_3244_, 0);
lean_inc_ref(v_toAttributeImplCore_3297_);
lean_dec_ref(v_attr_3244_);
v_name_3298_ = lean_ctor_get(v_toAttributeImplCore_3297_, 1);
lean_inc(v_name_3298_);
lean_dec_ref(v_toAttributeImplCore_3297_);
v___x_3299_ = 1;
v___x_3300_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3301_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3298_, v___x_3299_);
v___x_3302_ = lean_string_append(v___x_3300_, v___x_3301_);
lean_dec_ref(v___x_3301_);
v___x_3303_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3304_ = lean_string_append(v___x_3302_, v___x_3303_);
v___x_3305_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3246_, v___x_3299_);
v___x_3306_ = lean_string_append(v___x_3304_, v___x_3305_);
lean_dec_ref(v___x_3305_);
v___x_3307_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3));
v___x_3308_ = lean_string_append(v___x_3306_, v___x_3307_);
if (v_isShared_3296_ == 0)
{
lean_ctor_set_tag(v___x_3295_, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3308_);
v___x_3310_ = v___x_3295_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3308_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object* v_00_u03b1_3314_, lean_object* v_ext_3315_, lean_object* v_attr_3316_, lean_object* v_env_3317_, lean_object* v_decl_3318_, lean_object* v_param_3319_){
_start:
{
lean_object* v___x_3320_; 
v___x_3320_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3315_, v_attr_3316_, v_env_3317_, v_decl_3318_, v_param_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3321_, lean_object* v_env_3322_, lean_object* v_decl_3323_, lean_object* v_param_3324_){
_start:
{
lean_object* v_attr_3325_; lean_object* v_ext_3326_; lean_object* v___x_3327_; 
v_attr_3325_ = lean_ctor_get(v_attr_3321_, 0);
lean_inc_ref(v_attr_3325_);
v_ext_3326_ = lean_ctor_get(v_attr_3321_, 1);
lean_inc_ref(v_ext_3326_);
lean_dec_ref(v_attr_3321_);
v___x_3327_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3326_, v_attr_3325_, v_env_3322_, v_decl_3323_, v_param_3324_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3328_, lean_object* v_attr_3329_, lean_object* v_env_3330_, lean_object* v_decl_3331_, lean_object* v_param_3332_){
_start:
{
lean_object* v___x_3333_; 
v___x_3333_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3329_, v_env_3330_, v_decl_3331_, v_param_3332_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(lean_object* v_x_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0___boxed(lean_object* v_x_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(v_x_3339_, v___y_3340_);
lean_dec_ref(v___y_3340_);
lean_dec_ref(v_x_3339_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(lean_object* v_s_3343_, lean_object* v_x_3344_){
_start:
{
lean_inc(v_s_3343_);
return v_s_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1___boxed(lean_object* v_s_3345_, lean_object* v_x_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(v_s_3345_, v_x_3346_);
lean_dec_ref(v_x_3346_);
lean_dec(v_s_3345_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(lean_object* v_x_3348_, lean_object* v_x_3349_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2___boxed(lean_object* v_x_3351_, lean_object* v_x_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(v_x_3351_, v_x_3352_);
lean_dec(v_x_3352_);
lean_dec_ref(v_x_3351_);
return v_res_3353_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3(void){
_start:
{
lean_object* v___f_3357_; lean_object* v___f_3358_; lean_object* v___f_3359_; lean_object* v___f_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___f_3357_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3358_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2));
v___f_3359_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1));
v___f_3360_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0));
v___x_3361_ = lean_box(0);
v___x_3362_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_3363_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
lean_ctor_set(v___x_3363_, 1, v___x_3361_);
lean_ctor_set(v___x_3363_, 2, v___f_3360_);
lean_ctor_set(v___x_3363_, 3, v___f_3359_);
lean_ctor_set(v___x_3363_, 4, v___f_3358_);
lean_ctor_set(v___x_3363_, 5, v___f_3357_);
return v___x_3363_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3364_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3);
v___x_3365_ = lean_box(0);
v___x_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
lean_ctor_set(v___x_3366_, 1, v___x_3364_);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg(){
_start:
{
lean_object* v___x_3368_; 
v___x_3368_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___boxed(lean_object* v___dummy_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v_res_3370_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__0(void){
_start:
{
lean_object* v___x_3371_; 
v___x_3371_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3372_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg(){
_start:
{
lean_object* v___x_3375_; 
v___x_3375_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg___boxed(lean_object* v___dummy_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Lean_instInhabitedEnumAttributes___redArg();
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3378_){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3379_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3380_; 
v___x_3380_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3381_){
_start:
{
lean_object* v___x_3382_; 
v___x_3382_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3383_);
lean_dec(v_x_3383_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3385_, lean_object* v_x_3386_, lean_object* v_x_3387_){
_start:
{
if (lean_obj_tag(v_x_3387_) == 0)
{
return v_x_3386_;
}
else
{
lean_object* v_head_3388_; lean_object* v_tail_3389_; lean_object* v___x_3390_; 
v_head_3388_ = lean_ctor_get(v_x_3387_, 0);
lean_inc(v_head_3388_);
v_tail_3389_ = lean_ctor_get(v_x_3387_, 1);
lean_inc(v_tail_3389_);
lean_dec_ref_known(v_x_3387_, 2);
v___x_3390_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3385_, v_head_3388_);
if (lean_obj_tag(v___x_3390_) == 1)
{
lean_object* v_val_3391_; lean_object* v___x_3392_; 
v_val_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_val_3391_);
lean_dec_ref_known(v___x_3390_, 1);
v___x_3392_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3388_, v_val_3391_, v_x_3386_);
v_x_3386_ = v___x_3392_;
v_x_3387_ = v_tail_3389_;
goto _start;
}
else
{
lean_dec(v___x_3390_);
lean_dec(v_head_3388_);
v_x_3387_ = v_tail_3389_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3395_, lean_object* v_x_3396_, lean_object* v_x_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3395_, v_x_3396_, v_x_3397_);
lean_dec(v_newState_3395_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3399_, lean_object* v_newState_3400_, lean_object* v_consts_3401_, lean_object* v_st_3402_){
_start:
{
lean_object* v___x_3403_; 
v___x_3403_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3400_, v_st_3402_, v_consts_3401_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3404_, lean_object* v_newState_3405_, lean_object* v_consts_3406_, lean_object* v_st_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3404_, v_newState_3405_, v_consts_3406_, v_st_3407_);
lean_dec(v_newState_3405_);
lean_dec(v_x_3404_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3418_){
_start:
{
lean_object* v___x_3419_; lean_object* v___y_3421_; 
v___x_3419_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3418_) == 0)
{
lean_object* v_size_3425_; 
v_size_3425_ = lean_ctor_get(v_s_3418_, 0);
lean_inc(v_size_3425_);
lean_dec_ref_known(v_s_3418_, 5);
v___y_3421_ = v_size_3425_;
goto v___jp_3420_;
}
else
{
lean_object* v___x_3426_; 
v___x_3426_ = lean_unsigned_to_nat(0u);
v___y_3421_ = v___x_3426_;
goto v___jp_3420_;
}
v___jp_3420_:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3422_ = l_Nat_reprFast(v___y_3421_);
v___x_3423_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
v___x_3424_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3419_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
return v___x_3424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3427_, lean_object* v_as_3428_, size_t v_i_3429_, size_t v_stop_3430_, lean_object* v_b_3431_){
_start:
{
lean_object* v___y_3433_; uint8_t v___x_3437_; 
v___x_3437_ = lean_usize_dec_eq(v_i_3429_, v_stop_3430_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3438_; lean_object* v_fst_3439_; uint8_t v___x_3440_; lean_object* v___x_3441_; uint8_t v___x_3442_; 
v___x_3438_ = lean_array_uget_borrowed(v_as_3428_, v_i_3429_);
v_fst_3439_ = lean_ctor_get(v___x_3438_, 0);
v___x_3440_ = 1;
lean_inc_ref(v_env_3427_);
v___x_3441_ = l_Lean_Environment_setExporting(v_env_3427_, v___x_3440_);
lean_inc(v_fst_3439_);
v___x_3442_ = l_Lean_Environment_contains(v___x_3441_, v_fst_3439_, v___x_3437_);
if (v___x_3442_ == 0)
{
v___y_3433_ = v_b_3431_;
goto v___jp_3432_;
}
else
{
lean_object* v___x_3443_; 
lean_inc(v___x_3438_);
v___x_3443_ = lean_array_push(v_b_3431_, v___x_3438_);
v___y_3433_ = v___x_3443_;
goto v___jp_3432_;
}
}
else
{
lean_dec_ref(v_env_3427_);
return v_b_3431_;
}
v___jp_3432_:
{
size_t v___x_3434_; size_t v___x_3435_; 
v___x_3434_ = ((size_t)1ULL);
v___x_3435_ = lean_usize_add(v_i_3429_, v___x_3434_);
v_i_3429_ = v___x_3435_;
v_b_3431_ = v___y_3433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3444_, lean_object* v_as_3445_, lean_object* v_i_3446_, lean_object* v_stop_3447_, lean_object* v_b_3448_){
_start:
{
size_t v_i_boxed_3449_; size_t v_stop_boxed_3450_; lean_object* v_res_3451_; 
v_i_boxed_3449_ = lean_unbox_usize(v_i_3446_);
lean_dec(v_i_3446_);
v_stop_boxed_3450_ = lean_unbox_usize(v_stop_3447_);
lean_dec(v_stop_3447_);
v_res_3451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3444_, v_as_3445_, v_i_boxed_3449_, v_stop_boxed_3450_, v_b_3448_);
lean_dec_ref(v_as_3445_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3452_, lean_object* v_m_3453_){
_start:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___y_3457_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___y_3468_; lean_object* v___y_3469_; uint8_t v___x_3471_; 
v___x_3454_ = lean_unsigned_to_nat(0u);
v___x_3455_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_3465_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_3455_, v_m_3453_);
v___x_3466_ = lean_array_get_size(v___x_3465_);
v___x_3471_ = lean_nat_dec_eq(v___x_3466_, v___x_3454_);
if (v___x_3471_ == 0)
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___y_3475_; uint8_t v___x_3477_; 
v___x_3472_ = lean_unsigned_to_nat(1u);
v___x_3473_ = lean_nat_sub(v___x_3466_, v___x_3472_);
v___x_3477_ = lean_nat_dec_le(v___x_3454_, v___x_3473_);
if (v___x_3477_ == 0)
{
lean_inc(v___x_3473_);
v___y_3475_ = v___x_3473_;
goto v___jp_3474_;
}
else
{
v___y_3475_ = v___x_3454_;
goto v___jp_3474_;
}
v___jp_3474_:
{
uint8_t v___x_3476_; 
v___x_3476_ = lean_nat_dec_le(v___y_3475_, v___x_3473_);
if (v___x_3476_ == 0)
{
lean_dec(v___x_3473_);
lean_inc(v___y_3475_);
v___y_3468_ = v___y_3475_;
v___y_3469_ = v___y_3475_;
goto v___jp_3467_;
}
else
{
v___y_3468_ = v___y_3475_;
v___y_3469_ = v___x_3473_;
goto v___jp_3467_;
}
}
}
else
{
v___y_3457_ = v___x_3465_;
goto v___jp_3456_;
}
v___jp_3456_:
{
lean_object* v___x_3458_; uint8_t v___x_3459_; 
v___x_3458_ = lean_array_get_size(v___y_3457_);
v___x_3459_ = lean_nat_dec_lt(v___x_3454_, v___x_3458_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; 
lean_dec_ref(v_env_3452_);
v___x_3460_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3455_);
lean_ctor_set(v___x_3460_, 1, v___x_3455_);
lean_ctor_set(v___x_3460_, 2, v___y_3457_);
return v___x_3460_;
}
else
{
size_t v___x_3461_; size_t v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3461_ = ((size_t)0ULL);
v___x_3462_ = lean_usize_of_nat(v___x_3458_);
v___x_3463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3452_, v___y_3457_, v___x_3461_, v___x_3462_, v___x_3455_);
lean_inc_ref(v___x_3463_);
v___x_3464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
lean_ctor_set(v___x_3464_, 2, v___y_3457_);
return v___x_3464_;
}
}
v___jp_3467_:
{
lean_object* v___x_3470_; 
v___x_3470_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_3466_, v___x_3465_, v___y_3468_, v___y_3469_);
lean_dec(v___y_3469_);
v___y_3457_ = v___x_3470_;
goto v___jp_3456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3478_, lean_object* v_m_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3478_, v_m_3479_);
lean_dec(v_m_3479_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3481_, lean_object* v_p_3482_){
_start:
{
lean_object* v_fst_3483_; lean_object* v_snd_3484_; lean_object* v___x_3485_; 
v_fst_3483_ = lean_ctor_get(v_p_3482_, 0);
lean_inc(v_fst_3483_);
v_snd_3484_ = lean_ctor_get(v_p_3482_, 1);
lean_inc(v_snd_3484_);
lean_dec_ref(v_p_3482_);
v___x_3485_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3483_, v_snd_3484_, v_s_3481_);
return v___x_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3486_, lean_object* v_x_3487_, lean_object* v_x_3488_){
_start:
{
lean_object* v___x_3490_; 
v___x_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3486_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3491_, lean_object* v_x_3492_, lean_object* v_x_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3491_, v_x_3492_, v_x_3493_);
lean_dec_ref(v_x_3493_);
lean_dec_ref(v_x_3492_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3496_){
_start:
{
if (lean_obj_tag(v_as_3496_) == 0)
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3498_ = lean_box(0);
v___x_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
return v___x_3499_;
}
else
{
lean_object* v_head_3500_; lean_object* v_tail_3501_; lean_object* v___x_3502_; 
v_head_3500_ = lean_ctor_get(v_as_3496_, 0);
lean_inc(v_head_3500_);
v_tail_3501_ = lean_ctor_get(v_as_3496_, 1);
lean_inc(v_tail_3501_);
lean_dec_ref_known(v_as_3496_, 2);
v___x_3502_ = l_Lean_registerBuiltinAttribute(v_head_3500_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_dec_ref_known(v___x_3502_, 1);
v_as_3496_ = v_tail_3501_;
goto _start;
}
else
{
lean_dec(v_tail_3501_);
return v___x_3502_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3504_, lean_object* v___y_3505_){
_start:
{
lean_object* v_res_3506_; 
v_res_3506_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3504_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_addEntryFn_3507_, lean_object* v___x_3508_, lean_object* v_s_3509_){
_start:
{
lean_object* v_importedEntries_3510_; lean_object* v_state_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3519_; 
v_importedEntries_3510_ = lean_ctor_get(v_s_3509_, 0);
v_state_3511_ = lean_ctor_get(v_s_3509_, 1);
v_isSharedCheck_3519_ = !lean_is_exclusive(v_s_3509_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3513_ = v_s_3509_;
v_isShared_3514_ = v_isSharedCheck_3519_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_state_3511_);
lean_inc(v_importedEntries_3510_);
lean_dec(v_s_3509_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3519_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v_state_3515_; lean_object* v___x_3517_; 
v_state_3515_ = lean_apply_2(v_addEntryFn_3507_, v_state_3511_, v___x_3508_);
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 1, v_state_3515_);
v___x_3517_ = v___x_3513_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_importedEntries_3510_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v_state_3515_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2(lean_object* v_validate_3520_, lean_object* v_snd_3521_, lean_object* v_a_3522_, lean_object* v_fst_3523_, lean_object* v_decl_3524_, lean_object* v_stx_3525_, uint8_t v_kind_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v_nextMacroScope_3531_; lean_object* v_ngen_3532_; lean_object* v_auxDeclNGen_3533_; lean_object* v_traceState_3534_; lean_object* v_recordedDeps_3535_; lean_object* v_messages_3536_; lean_object* v_infoState_3537_; lean_object* v_snapshotTasks_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___x_3576_; 
v___x_3576_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3525_, v___y_3527_, v___y_3528_);
if (lean_obj_tag(v___x_3576_) == 0)
{
uint8_t v___x_3577_; uint8_t v___x_3578_; 
lean_dec_ref_known(v___x_3576_, 1);
v___x_3577_ = 0;
v___x_3578_ = l_Lean_instBEqAttributeKind_beq(v_kind_3526_, v___x_3577_);
if (v___x_3578_ == 0)
{
lean_object* v___x_3579_; 
lean_dec(v_decl_3524_);
lean_dec_ref(v_a_3522_);
lean_dec(v_snd_3521_);
lean_dec_ref(v_validate_3520_);
v___x_3579_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3523_, v_kind_3526_, v___y_3527_, v___y_3528_);
return v___x_3579_;
}
else
{
goto v___jp_3571_;
}
}
else
{
lean_dec(v_decl_3524_);
lean_dec(v_fst_3523_);
lean_dec_ref(v_a_3522_);
lean_dec(v_snd_3521_);
lean_dec_ref(v_validate_3520_);
return v___x_3576_;
}
v___jp_3530_:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3542_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_3543_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3543_, 0, v___y_3541_);
lean_ctor_set(v___x_3543_, 1, v_nextMacroScope_3531_);
lean_ctor_set(v___x_3543_, 2, v_ngen_3532_);
lean_ctor_set(v___x_3543_, 3, v_auxDeclNGen_3533_);
lean_ctor_set(v___x_3543_, 4, v_traceState_3534_);
lean_ctor_set(v___x_3543_, 5, v___x_3542_);
lean_ctor_set(v___x_3543_, 6, v_recordedDeps_3535_);
lean_ctor_set(v___x_3543_, 7, v_messages_3536_);
lean_ctor_set(v___x_3543_, 8, v_infoState_3537_);
lean_ctor_set(v___x_3543_, 9, v_snapshotTasks_3538_);
v___x_3544_ = lean_st_ref_put(v___y_3540_, v___x_3543_);
v___x_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3545_, 0, v___y_3539_);
return v___x_3545_;
}
v___jp_3546_:
{
lean_object* v___x_3549_; 
lean_inc(v___y_3548_);
lean_inc_ref(v___y_3547_);
lean_inc(v_snd_3521_);
lean_inc(v_decl_3524_);
v___x_3549_ = lean_apply_5(v_validate_3520_, v_decl_3524_, v_snd_3521_, v___y_3547_, v___y_3548_, lean_box(0));
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v___x_3550_; lean_object* v_toEnvExtension_3551_; lean_object* v_env_3552_; lean_object* v_nextMacroScope_3553_; lean_object* v_ngen_3554_; lean_object* v_auxDeclNGen_3555_; lean_object* v_traceState_3556_; lean_object* v_recordedDeps_3557_; lean_object* v_messages_3558_; lean_object* v_infoState_3559_; lean_object* v_snapshotTasks_3560_; lean_object* v_addEntryFn_3561_; lean_object* v_asyncMode_3562_; uint8_t v_logWrites_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___f_3566_; uint8_t v___x_3567_; 
lean_dec_ref_known(v___x_3549_, 1);
v___x_3550_ = lean_st_ref_take(v___y_3548_);
v_toEnvExtension_3551_ = lean_ctor_get(v_a_3522_, 0);
lean_inc_ref(v_toEnvExtension_3551_);
v_env_3552_ = lean_ctor_get(v___x_3550_, 0);
lean_inc_ref(v_env_3552_);
v_nextMacroScope_3553_ = lean_ctor_get(v___x_3550_, 1);
lean_inc(v_nextMacroScope_3553_);
v_ngen_3554_ = lean_ctor_get(v___x_3550_, 2);
lean_inc_ref(v_ngen_3554_);
v_auxDeclNGen_3555_ = lean_ctor_get(v___x_3550_, 3);
lean_inc_ref(v_auxDeclNGen_3555_);
v_traceState_3556_ = lean_ctor_get(v___x_3550_, 4);
lean_inc_ref(v_traceState_3556_);
v_recordedDeps_3557_ = lean_ctor_get(v___x_3550_, 6);
lean_inc_ref(v_recordedDeps_3557_);
v_messages_3558_ = lean_ctor_get(v___x_3550_, 7);
lean_inc_ref(v_messages_3558_);
v_infoState_3559_ = lean_ctor_get(v___x_3550_, 8);
lean_inc_ref(v_infoState_3559_);
v_snapshotTasks_3560_ = lean_ctor_get(v___x_3550_, 9);
lean_inc_ref(v_snapshotTasks_3560_);
lean_dec(v___x_3550_);
v_addEntryFn_3561_ = lean_ctor_get(v_a_3522_, 3);
lean_inc(v_addEntryFn_3561_);
lean_dec_ref(v_a_3522_);
v_asyncMode_3562_ = lean_ctor_get(v_toEnvExtension_3551_, 2);
lean_inc(v_asyncMode_3562_);
v_logWrites_3563_ = lean_ctor_get_uint8(v_toEnvExtension_3551_, sizeof(void*)*6);
v___x_3564_ = lean_box(0);
lean_inc(v_decl_3524_);
v___x_3565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3565_, 0, v_decl_3524_);
lean_ctor_set(v___x_3565_, 1, v_snd_3521_);
v___f_3566_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3566_, 0, v_addEntryFn_3561_);
lean_closure_set(v___f_3566_, 1, v___x_3565_);
v___x_3567_ = 1;
if (v_logWrites_3563_ == 0)
{
lean_object* v___x_3568_; 
v___x_3568_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3551_, v_env_3552_, v___f_3566_, v_asyncMode_3562_, v_decl_3524_, v___x_3567_);
lean_dec(v_asyncMode_3562_);
v_nextMacroScope_3531_ = v_nextMacroScope_3553_;
v_ngen_3532_ = v_ngen_3554_;
v_auxDeclNGen_3533_ = v_auxDeclNGen_3555_;
v_traceState_3534_ = v_traceState_3556_;
v_recordedDeps_3535_ = v_recordedDeps_3557_;
v_messages_3536_ = v_messages_3558_;
v_infoState_3537_ = v_infoState_3559_;
v_snapshotTasks_3538_ = v_snapshotTasks_3560_;
v___y_3539_ = v___x_3564_;
v___y_3540_ = v___y_3548_;
v___y_3541_ = v___x_3568_;
goto v___jp_3530_;
}
else
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
lean_inc_ref(v_toEnvExtension_3551_);
v___x_3569_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3551_, v_env_3552_);
lean_dec_ref(v_env_3552_);
v___x_3570_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3551_, v___x_3569_, v___f_3566_, v_asyncMode_3562_, v_decl_3524_, v___x_3567_);
lean_dec(v_asyncMode_3562_);
v_nextMacroScope_3531_ = v_nextMacroScope_3553_;
v_ngen_3532_ = v_ngen_3554_;
v_auxDeclNGen_3533_ = v_auxDeclNGen_3555_;
v_traceState_3534_ = v_traceState_3556_;
v_recordedDeps_3535_ = v_recordedDeps_3557_;
v_messages_3536_ = v_messages_3558_;
v_infoState_3537_ = v_infoState_3559_;
v_snapshotTasks_3538_ = v_snapshotTasks_3560_;
v___y_3539_ = v___x_3564_;
v___y_3540_ = v___y_3548_;
v___y_3541_ = v___x_3570_;
goto v___jp_3530_;
}
}
else
{
lean_dec(v_decl_3524_);
lean_dec_ref(v_a_3522_);
lean_dec(v_snd_3521_);
return v___x_3549_;
}
}
v___jp_3571_:
{
lean_object* v___x_3572_; lean_object* v_env_3573_; lean_object* v___x_3574_; 
v___x_3572_ = lean_st_ref_get(v___y_3528_);
v_env_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc_ref(v_env_3573_);
lean_dec(v___x_3572_);
v___x_3574_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3573_, v_decl_3524_);
lean_dec_ref(v_env_3573_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_dec(v_fst_3523_);
v___y_3547_ = v___y_3527_;
v___y_3548_ = v___y_3528_;
goto v___jp_3546_;
}
else
{
lean_object* v___x_3575_; 
lean_dec_ref_known(v___x_3574_, 1);
lean_dec_ref(v_a_3522_);
lean_dec(v_snd_3521_);
lean_dec_ref(v_validate_3520_);
v___x_3575_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3523_, v_decl_3524_, v___y_3527_, v___y_3528_);
return v___x_3575_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2___boxed(lean_object* v_validate_3580_, lean_object* v_snd_3581_, lean_object* v_a_3582_, lean_object* v_fst_3583_, lean_object* v_decl_3584_, lean_object* v_stx_3585_, lean_object* v_kind_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
uint8_t v_kind_boxed_3590_; lean_object* v_res_3591_; 
v_kind_boxed_3590_ = lean_unbox(v_kind_3586_);
v_res_3591_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2(v_validate_3580_, v_snd_3581_, v_a_3582_, v_fst_3583_, v_decl_3584_, v_stx_3585_, v_kind_boxed_3590_, v___y_3587_, v___y_3588_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3592_, lean_object* v_decl_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3597_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3598_ = l_Lean_MessageData_ofName(v_fst_3592_);
v___x_3599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3597_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
v___x_3600_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3599_);
lean_ctor_set(v___x_3601_, 1, v___x_3600_);
v___x_3602_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3601_, v___y_3594_, v___y_3595_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3603_, lean_object* v_decl_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3603_, v_decl_3604_, v___y_3605_, v___y_3606_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec(v_decl_3604_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3609_, lean_object* v_a_3610_, lean_object* v_ref_3611_, uint8_t v_applicationTime_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_){
_start:
{
if (lean_obj_tag(v_a_3613_) == 0)
{
lean_object* v___x_3615_; 
lean_dec(v_ref_3611_);
lean_dec_ref(v_a_3610_);
lean_dec_ref(v_validate_3609_);
v___x_3615_ = l_List_reverse___redArg(v_a_3614_);
return v___x_3615_;
}
else
{
lean_object* v_head_3616_; lean_object* v_snd_3617_; lean_object* v_tail_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3633_; 
v_head_3616_ = lean_ctor_get(v_a_3613_, 0);
lean_inc(v_head_3616_);
v_snd_3617_ = lean_ctor_get(v_head_3616_, 1);
lean_inc(v_snd_3617_);
v_tail_3618_ = lean_ctor_get(v_a_3613_, 1);
v_isSharedCheck_3633_ = !lean_is_exclusive(v_a_3613_);
if (v_isSharedCheck_3633_ == 0)
{
lean_object* v_unused_3634_; 
v_unused_3634_ = lean_ctor_get(v_a_3613_, 0);
lean_dec(v_unused_3634_);
v___x_3620_ = v_a_3613_;
v_isShared_3621_ = v_isSharedCheck_3633_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_tail_3618_);
lean_dec(v_a_3613_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3633_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v_fst_3622_; lean_object* v_fst_3623_; lean_object* v_snd_3624_; lean_object* v___f_3625_; lean_object* v___f_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3630_; 
v_fst_3622_ = lean_ctor_get(v_head_3616_, 0);
lean_inc_n(v_fst_3622_, 3);
lean_dec(v_head_3616_);
v_fst_3623_ = lean_ctor_get(v_snd_3617_, 0);
lean_inc(v_fst_3623_);
v_snd_3624_ = lean_ctor_get(v_snd_3617_, 1);
lean_inc(v_snd_3624_);
lean_dec(v_snd_3617_);
v___f_3625_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3625_, 0, v_fst_3622_);
lean_inc_ref(v_a_3610_);
lean_inc_ref(v_validate_3609_);
v___f_3626_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2___boxed), 10, 4);
lean_closure_set(v___f_3626_, 0, v_validate_3609_);
lean_closure_set(v___f_3626_, 1, v_snd_3624_);
lean_closure_set(v___f_3626_, 2, v_a_3610_);
lean_closure_set(v___f_3626_, 3, v_fst_3622_);
lean_inc(v_ref_3611_);
v___x_3627_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3627_, 0, v_ref_3611_);
lean_ctor_set(v___x_3627_, 1, v_fst_3622_);
lean_ctor_set(v___x_3627_, 2, v_fst_3623_);
lean_ctor_set_uint8(v___x_3627_, sizeof(void*)*3, v_applicationTime_3612_);
v___x_3628_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3627_);
lean_ctor_set(v___x_3628_, 1, v___f_3626_);
lean_ctor_set(v___x_3628_, 2, v___f_3625_);
if (v_isShared_3621_ == 0)
{
lean_ctor_set(v___x_3620_, 1, v_a_3614_);
lean_ctor_set(v___x_3620_, 0, v___x_3628_);
v___x_3630_ = v___x_3620_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3628_);
lean_ctor_set(v_reuseFailAlloc_3632_, 1, v_a_3614_);
v___x_3630_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
v_a_3613_ = v_tail_3618_;
v_a_3614_ = v___x_3630_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3635_, lean_object* v_a_3636_, lean_object* v_ref_3637_, lean_object* v_applicationTime_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_){
_start:
{
uint8_t v_applicationTime_boxed_3641_; lean_object* v_res_3642_; 
v_applicationTime_boxed_3641_ = lean_unbox(v_applicationTime_3638_);
v_res_3642_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3635_, v_a_3636_, v_ref_3637_, v_applicationTime_boxed_3641_, v_a_3639_, v_a_3640_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3656_, lean_object* v_validate_3657_, uint8_t v_applicationTime_3658_, lean_object* v_ref_3659_){
_start:
{
lean_object* v___f_3661_; lean_object* v___f_3662_; lean_object* v___f_3663_; lean_object* v___f_3664_; lean_object* v___f_3665_; lean_object* v___f_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; uint8_t v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___f_3661_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3662_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3663_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3664_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3665_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3666_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3667_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3668_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
v___x_3669_ = 0;
lean_inc(v_ref_3659_);
v___x_3670_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_3670_, 0, v_ref_3659_);
lean_ctor_set(v___x_3670_, 1, v___f_3665_);
lean_ctor_set(v___x_3670_, 2, v___f_3666_);
lean_ctor_set(v___x_3670_, 3, v___f_3664_);
lean_ctor_set(v___x_3670_, 4, v___f_3663_);
lean_ctor_set(v___x_3670_, 5, v___f_3662_);
lean_ctor_set(v___x_3670_, 6, v___x_3667_);
lean_ctor_set(v___x_3670_, 7, v___x_3668_);
lean_ctor_set_uint8(v___x_3670_, sizeof(void*)*8, v___x_3669_);
lean_ctor_set_uint8(v___x_3670_, sizeof(void*)*8 + 1, v___x_3669_);
v___x_3671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3670_);
lean_ctor_set(v___x_3671_, 1, v___f_3661_);
v___x_3672_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3671_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc_n(v_a_3673_, 2);
lean_dec_ref_known(v___x_3672_, 1);
v___x_3674_ = lean_box(0);
v___x_3675_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3657_, v_a_3673_, v_ref_3659_, v_applicationTime_3658_, v_attrDescrs_3656_, v___x_3674_);
lean_inc(v___x_3675_);
v___x_3676_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3675_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3684_; 
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3684_ == 0)
{
lean_object* v_unused_3685_; 
v_unused_3685_ = lean_ctor_get(v___x_3676_, 0);
lean_dec(v_unused_3685_);
v___x_3678_ = v___x_3676_;
v_isShared_3679_ = v_isSharedCheck_3684_;
goto v_resetjp_3677_;
}
else
{
lean_dec(v___x_3676_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3684_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3680_; lean_object* v___x_3682_; 
v___x_3680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3675_);
lean_ctor_set(v___x_3680_, 1, v_a_3673_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 0, v___x_3680_);
v___x_3682_ = v___x_3678_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
lean_dec(v___x_3675_);
lean_dec(v_a_3673_);
v_a_3686_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3676_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3676_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
lean_dec(v_ref_3659_);
lean_dec_ref(v_validate_3657_);
lean_dec(v_attrDescrs_3656_);
v_a_3694_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___x_3672_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3672_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3702_, lean_object* v_validate_3703_, lean_object* v_applicationTime_3704_, lean_object* v_ref_3705_, lean_object* v_a_3706_){
_start:
{
uint8_t v_applicationTime_boxed_3707_; lean_object* v_res_3708_; 
v_applicationTime_boxed_3707_ = lean_unbox(v_applicationTime_3704_);
v_res_3708_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3702_, v_validate_3703_, v_applicationTime_boxed_3707_, v_ref_3705_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3709_, lean_object* v_attrDescrs_3710_, lean_object* v_validate_3711_, uint8_t v_applicationTime_3712_, lean_object* v_ref_3713_){
_start:
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3710_, v_validate_3711_, v_applicationTime_3712_, v_ref_3713_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3716_, lean_object* v_attrDescrs_3717_, lean_object* v_validate_3718_, lean_object* v_applicationTime_3719_, lean_object* v_ref_3720_, lean_object* v_a_3721_){
_start:
{
uint8_t v_applicationTime_boxed_3722_; lean_object* v_res_3723_; 
v_applicationTime_boxed_3722_ = lean_unbox(v_applicationTime_3719_);
v_res_3723_ = l_Lean_registerEnumAttributes(v_00_u03b1_3716_, v_attrDescrs_3717_, v_validate_3718_, v_applicationTime_boxed_3722_, v_ref_3720_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3724_, lean_object* v_env_3725_, lean_object* v_as_3726_, size_t v_i_3727_, size_t v_stop_3728_, lean_object* v_b_3729_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3725_, v_as_3726_, v_i_3727_, v_stop_3728_, v_b_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3731_, lean_object* v_env_3732_, lean_object* v_as_3733_, lean_object* v_i_3734_, lean_object* v_stop_3735_, lean_object* v_b_3736_){
_start:
{
size_t v_i_boxed_3737_; size_t v_stop_boxed_3738_; lean_object* v_res_3739_; 
v_i_boxed_3737_ = lean_unbox_usize(v_i_3734_);
lean_dec(v_i_3734_);
v_stop_boxed_3738_ = lean_unbox_usize(v_stop_3735_);
lean_dec(v_stop_3735_);
v_res_3739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3731_, v_env_3732_, v_as_3733_, v_i_boxed_3737_, v_stop_boxed_3738_, v_b_3736_);
lean_dec_ref(v_as_3733_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3740_, lean_object* v_newState_3741_, lean_object* v_x_3742_, lean_object* v_x_3743_){
_start:
{
lean_object* v___x_3744_; 
v___x_3744_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3741_, v_x_3742_, v_x_3743_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3745_, lean_object* v_newState_3746_, lean_object* v_x_3747_, lean_object* v_x_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3745_, v_newState_3746_, v_x_3747_, v_x_3748_);
lean_dec(v_newState_3746_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3750_, lean_object* v_validate_3751_, lean_object* v_a_3752_, lean_object* v_ref_3753_, uint8_t v_applicationTime_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_){
_start:
{
lean_object* v___x_3757_; 
v___x_3757_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3751_, v_a_3752_, v_ref_3753_, v_applicationTime_3754_, v_a_3755_, v_a_3756_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3758_, lean_object* v_validate_3759_, lean_object* v_a_3760_, lean_object* v_ref_3761_, lean_object* v_applicationTime_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_){
_start:
{
uint8_t v_applicationTime_boxed_3765_; lean_object* v_res_3766_; 
v_applicationTime_boxed_3765_ = lean_unbox(v_applicationTime_3762_);
v_res_3766_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3758_, v_validate_3759_, v_a_3760_, v_ref_3761_, v_applicationTime_boxed_3765_, v_a_3763_, v_a_3764_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3767_, lean_object* v_attr_3768_, lean_object* v_env_3769_, lean_object* v_decl_3770_){
_start:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3771_ = lean_box(1);
v___x_3772_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3769_, v_decl_3770_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v_ext_3773_; lean_object* v_toEnvExtension_3774_; lean_object* v_asyncMode_3775_; uint8_t v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
lean_dec(v_inst_3767_);
v_ext_3773_ = lean_ctor_get(v_attr_3768_, 1);
lean_inc_ref(v_ext_3773_);
lean_dec_ref(v_attr_3768_);
v_toEnvExtension_3774_ = lean_ctor_get(v_ext_3773_, 0);
v_asyncMode_3775_ = lean_ctor_get(v_toEnvExtension_3774_, 2);
lean_inc(v_asyncMode_3775_);
v___x_3776_ = 0;
lean_inc(v_decl_3770_);
v___x_3777_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3771_, v_ext_3773_, v_env_3769_, v_asyncMode_3775_, v_decl_3770_, v___x_3776_);
lean_dec(v_asyncMode_3775_);
lean_dec_ref(v_ext_3773_);
v___x_3778_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3777_, v_decl_3770_);
lean_dec(v_decl_3770_);
lean_dec(v___x_3777_);
return v___x_3778_;
}
else
{
lean_object* v_val_3779_; lean_object* v_ext_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3810_; 
v_val_3779_ = lean_ctor_get(v___x_3772_, 0);
lean_inc(v_val_3779_);
lean_dec_ref_known(v___x_3772_, 1);
v_ext_3780_ = lean_ctor_get(v_attr_3768_, 1);
v_isSharedCheck_3810_ = !lean_is_exclusive(v_attr_3768_);
if (v_isSharedCheck_3810_ == 0)
{
lean_object* v_unused_3811_; 
v_unused_3811_ = lean_ctor_get(v_attr_3768_, 0);
lean_dec(v_unused_3811_);
v___x_3782_ = v_attr_3768_;
v_isShared_3783_ = v_isSharedCheck_3810_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_ext_3780_);
lean_dec(v_attr_3768_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3810_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
uint8_t v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; uint8_t v___x_3788_; 
v___x_3784_ = 0;
v___x_3785_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3771_, v_ext_3780_, v_env_3769_, v_val_3779_, v___x_3784_);
lean_dec(v_val_3779_);
lean_dec_ref(v_env_3769_);
lean_dec_ref(v_ext_3780_);
v___x_3786_ = lean_unsigned_to_nat(0u);
v___x_3787_ = lean_array_get_size(v___x_3785_);
v___x_3788_ = lean_nat_dec_lt(v___x_3786_, v___x_3787_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3789_; 
lean_dec_ref(v___x_3785_);
lean_del_object(v___x_3782_);
lean_dec(v_decl_3770_);
lean_dec(v_inst_3767_);
v___x_3789_ = lean_box(0);
return v___x_3789_;
}
else
{
lean_object* v___x_3790_; lean_object* v___x_3791_; uint8_t v___x_3792_; 
v___x_3790_ = lean_unsigned_to_nat(1u);
v___x_3791_ = lean_nat_sub(v___x_3787_, v___x_3790_);
v___x_3792_ = lean_nat_dec_le(v___x_3786_, v___x_3791_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; 
lean_dec(v___x_3791_);
lean_dec_ref(v___x_3785_);
lean_del_object(v___x_3782_);
lean_dec(v_decl_3770_);
lean_dec(v_inst_3767_);
v___x_3793_ = lean_box(0);
return v___x_3793_;
}
else
{
lean_object* v___f_3794_; lean_object* v___x_3796_; 
v___f_3794_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 1, v_inst_3767_);
lean_ctor_set(v___x_3782_, 0, v_decl_3770_);
v___x_3796_ = v___x_3782_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_decl_3770_);
lean_ctor_set(v_reuseFailAlloc_3809_, 1, v_inst_3767_);
v___x_3796_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3798_ = l_Array_binSearchAux___redArg(v___f_3794_, v___x_3797_, v___x_3785_, v___x_3796_, v___x_3786_, v___x_3791_);
lean_dec_ref(v___x_3785_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v___x_3799_; 
v___x_3799_ = lean_box(0);
return v___x_3799_;
}
else
{
lean_object* v_val_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3808_; 
v_val_3800_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3802_ = v___x_3798_;
v_isShared_3803_ = v_isSharedCheck_3808_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_val_3800_);
lean_dec(v___x_3798_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3808_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v_snd_3804_; lean_object* v___x_3806_; 
v_snd_3804_ = lean_ctor_get(v_val_3800_, 1);
lean_inc(v_snd_3804_);
lean_dec(v_val_3800_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 0, v_snd_3804_);
v___x_3806_ = v___x_3802_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_snd_3804_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3812_, lean_object* v_inst_3813_, lean_object* v_attr_3814_, lean_object* v_env_3815_, lean_object* v_decl_3816_){
_start:
{
lean_object* v___x_3817_; 
v___x_3817_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3813_, v_attr_3814_, v_env_3815_, v_decl_3816_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3826_, lean_object* v_env_3827_, lean_object* v_decl_3828_, lean_object* v_val_3829_){
_start:
{
lean_object* v_ext_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3900_; 
v_ext_3830_ = lean_ctor_get(v_attrs_3826_, 1);
v_isSharedCheck_3900_ = !lean_is_exclusive(v_attrs_3826_);
if (v_isSharedCheck_3900_ == 0)
{
lean_object* v_unused_3901_; 
v_unused_3901_ = lean_ctor_get(v_attrs_3826_, 0);
lean_dec(v_unused_3901_);
v___x_3832_ = v_attrs_3826_;
v_isShared_3833_ = v_isSharedCheck_3900_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_ext_3830_);
lean_dec(v_attrs_3826_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3900_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v_toEnvExtension_3834_; lean_object* v_name_3835_; lean_object* v_addEntryFn_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v_pfx_3846_; lean_object* v___x_3847_; 
v_toEnvExtension_3834_ = lean_ctor_get(v_ext_3830_, 0);
lean_inc_ref(v_toEnvExtension_3834_);
v_name_3835_ = lean_ctor_get(v_ext_3830_, 1);
v_addEntryFn_3836_ = lean_ctor_get(v_ext_3830_, 3);
lean_inc(v_addEntryFn_3836_);
v___x_3837_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3838_ = 1;
lean_inc(v_name_3835_);
v___x_3839_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3835_, v___x_3838_);
v___x_3840_ = lean_string_append(v___x_3837_, v___x_3839_);
lean_dec_ref(v___x_3839_);
v___x_3841_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3842_ = lean_string_append(v___x_3840_, v___x_3841_);
lean_inc(v_decl_3828_);
v___x_3843_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3828_, v___x_3838_);
v___x_3844_ = lean_string_append(v___x_3842_, v___x_3843_);
lean_dec_ref(v___x_3843_);
v___x_3845_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3846_ = lean_string_append(v___x_3844_, v___x_3845_);
v___x_3847_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3827_, v_decl_3828_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v_asyncMode_3848_; uint8_t v_logWrites_3849_; uint8_t v___x_3850_; 
v_asyncMode_3848_ = lean_ctor_get(v_toEnvExtension_3834_, 2);
lean_inc(v_asyncMode_3848_);
v_logWrites_3849_ = lean_ctor_get_uint8(v_toEnvExtension_3834_, sizeof(void*)*6);
lean_inc(v_decl_3828_);
lean_inc_ref(v_env_3827_);
v___x_3850_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3827_, v_decl_3828_, v_asyncMode_3848_);
if (v___x_3850_ == 0)
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___y_3854_; lean_object* v___x_3858_; 
lean_dec(v_asyncMode_3848_);
lean_dec(v_addEntryFn_3836_);
lean_dec_ref(v_toEnvExtension_3834_);
lean_del_object(v___x_3832_);
lean_dec_ref(v_ext_3830_);
lean_dec(v_val_3829_);
lean_dec(v_decl_3828_);
v___x_3851_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3852_ = lean_string_append(v_pfx_3846_, v___x_3851_);
v___x_3858_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3827_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v___x_3859_; 
v___x_3859_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3854_ = v___x_3859_;
goto v___jp_3853_;
}
else
{
lean_object* v_val_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v_val_3860_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_val_3860_);
lean_dec_ref_known(v___x_3858_, 1);
v___x_3861_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3862_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3860_, v___x_3838_);
v___x_3863_ = l_addParenHeuristic(v___x_3862_);
v___x_3864_ = lean_string_append(v___x_3861_, v___x_3863_);
lean_dec_ref(v___x_3863_);
v___x_3865_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3866_ = lean_string_append(v___x_3864_, v___x_3865_);
v___y_3854_ = v___x_3866_;
goto v___jp_3853_;
}
v___jp_3853_:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3855_ = lean_string_append(v___x_3852_, v___y_3854_);
lean_dec_ref(v___y_3854_);
v___x_3856_ = lean_string_append(v___x_3855_, v___x_3845_);
v___x_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
return v___x_3857_;
}
}
else
{
lean_object* v___x_3867_; uint8_t v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3867_ = lean_box(1);
v___x_3868_ = 0;
lean_inc(v_decl_3828_);
lean_inc_ref(v_env_3827_);
v___x_3869_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3867_, v_ext_3830_, v_env_3827_, v_asyncMode_3848_, v_decl_3828_, v___x_3868_);
lean_dec_ref(v_ext_3830_);
v___x_3870_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3869_, v_decl_3828_);
lean_dec(v___x_3869_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v___x_3872_; 
lean_dec_ref(v_pfx_3846_);
lean_inc(v_decl_3828_);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 1, v_val_3829_);
lean_ctor_set(v___x_3832_, 0, v_decl_3828_);
v___x_3872_ = v___x_3832_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_decl_3828_);
lean_ctor_set(v_reuseFailAlloc_3879_, 1, v_val_3829_);
v___x_3872_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
lean_object* v___f_3873_; 
v___f_3873_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3873_, 0, v_addEntryFn_3836_);
lean_closure_set(v___f_3873_, 1, v___x_3872_);
if (v_logWrites_3849_ == 0)
{
lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3874_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3834_, v_env_3827_, v___f_3873_, v_asyncMode_3848_, v_decl_3828_, v___x_3850_);
lean_dec(v_asyncMode_3848_);
v___x_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3874_);
return v___x_3875_;
}
else
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
lean_inc_ref(v_toEnvExtension_3834_);
v___x_3876_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3834_, v_env_3827_);
lean_dec_ref(v_env_3827_);
v___x_3877_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3834_, v___x_3876_, v___f_3873_, v_asyncMode_3848_, v_decl_3828_, v___x_3850_);
lean_dec(v_asyncMode_3848_);
v___x_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3877_);
return v___x_3878_;
}
}
}
else
{
lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3888_; 
lean_dec(v_asyncMode_3848_);
lean_dec(v_addEntryFn_3836_);
lean_dec_ref(v_toEnvExtension_3834_);
lean_del_object(v___x_3832_);
lean_dec(v_val_3829_);
lean_dec(v_decl_3828_);
lean_dec_ref(v_env_3827_);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3888_ == 0)
{
lean_object* v_unused_3889_; 
v_unused_3889_ = lean_ctor_get(v___x_3870_, 0);
lean_dec(v_unused_3889_);
v___x_3881_ = v___x_3870_;
v_isShared_3882_ = v_isSharedCheck_3888_;
goto v_resetjp_3880_;
}
else
{
lean_dec(v___x_3870_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3888_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3886_; 
v___x_3883_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3884_ = lean_string_append(v_pfx_3846_, v___x_3883_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set_tag(v___x_3881_, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3884_);
v___x_3886_ = v___x_3881_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3884_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
}
else
{
lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3898_; 
lean_dec(v_addEntryFn_3836_);
lean_dec_ref(v_toEnvExtension_3834_);
lean_del_object(v___x_3832_);
lean_dec_ref(v_ext_3830_);
lean_dec(v_val_3829_);
lean_dec(v_decl_3828_);
lean_dec_ref(v_env_3827_);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3898_ == 0)
{
lean_object* v_unused_3899_; 
v_unused_3899_ = lean_ctor_get(v___x_3847_, 0);
lean_dec(v_unused_3899_);
v___x_3891_ = v___x_3847_;
v_isShared_3892_ = v_isSharedCheck_3898_;
goto v_resetjp_3890_;
}
else
{
lean_dec(v___x_3847_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3898_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3896_; 
v___x_3893_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3894_ = lean_string_append(v_pfx_3846_, v___x_3893_);
if (v_isShared_3892_ == 0)
{
lean_ctor_set_tag(v___x_3891_, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3894_);
v___x_3896_ = v___x_3891_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3894_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3902_, lean_object* v_attrs_3903_, lean_object* v_env_3904_, lean_object* v_decl_3905_, lean_object* v_val_3906_){
_start:
{
lean_object* v___x_3907_; 
v___x_3907_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3903_, v_env_3904_, v_decl_3905_, v_val_3906_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3909_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3910_ = lean_st_mk_ref(v___x_3909_);
v___x_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3910_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3916_, lean_object* v_builder_3917_){
_start:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; uint8_t v___x_3921_; 
v___x_3919_ = l_Lean_attributeImplBuilderTableRef;
v___x_3920_ = lean_st_ref_get(v___x_3919_);
v___x_3921_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3920_, v_builderId_3916_);
lean_dec(v___x_3920_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3922_ = lean_st_ref_take(v___x_3919_);
v___x_3923_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3922_, v_builderId_3916_, v_builder_3917_);
v___x_3924_ = lean_st_ref_put(v___x_3919_, v___x_3923_);
v___x_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
return v___x_3925_;
}
else
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
lean_dec_ref(v_builder_3917_);
v___x_3926_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3927_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3916_, v___x_3921_);
v___x_3928_ = lean_string_append(v___x_3926_, v___x_3927_);
lean_dec_ref(v___x_3927_);
v___x_3929_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3930_ = lean_string_append(v___x_3928_, v___x_3929_);
v___x_3931_ = lean_mk_io_user_error(v___x_3930_);
v___x_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3931_);
return v___x_3932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3933_, lean_object* v_builder_3934_, lean_object* v_a_3935_){
_start:
{
lean_object* v_res_3936_; 
v_res_3936_ = l_Lean_registerAttributeImplBuilder(v_builderId_3933_, v_builder_3934_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3937_){
_start:
{
if (lean_obj_tag(v_e_3937_) == 0)
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3947_; 
v_a_3939_ = lean_ctor_get(v_e_3937_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v_e_3937_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3941_ = v_e_3937_;
v_isShared_3942_ = v_isSharedCheck_3947_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v_e_3937_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3947_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3943_; lean_object* v___x_3945_; 
v___x_3943_ = lean_mk_io_user_error(v_a_3939_);
if (v_isShared_3942_ == 0)
{
lean_ctor_set_tag(v___x_3941_, 1);
lean_ctor_set(v___x_3941_, 0, v___x_3943_);
v___x_3945_ = v___x_3941_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3943_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
else
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3955_; 
v_a_3948_ = lean_ctor_get(v_e_3937_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v_e_3937_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3950_ = v_e_3937_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v_e_3937_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3953_; 
if (v_isShared_3951_ == 0)
{
lean_ctor_set_tag(v___x_3950_, 0);
v___x_3953_ = v___x_3950_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3948_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3956_, lean_object* v_a_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3956_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3959_, lean_object* v_e_3960_){
_start:
{
lean_object* v___x_3962_; 
v___x_3962_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3960_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3963_, lean_object* v_e_3964_, lean_object* v_a_3965_){
_start:
{
lean_object* v_res_3966_; 
v_res_3966_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3963_, v_e_3964_);
return v_res_3966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3967_, lean_object* v_x_3968_){
_start:
{
if (lean_obj_tag(v_x_3968_) == 0)
{
lean_object* v___x_3969_; 
v___x_3969_ = lean_box(0);
return v___x_3969_;
}
else
{
lean_object* v_key_3970_; lean_object* v_value_3971_; lean_object* v_tail_3972_; uint8_t v___x_3973_; 
v_key_3970_ = lean_ctor_get(v_x_3968_, 0);
v_value_3971_ = lean_ctor_get(v_x_3968_, 1);
v_tail_3972_ = lean_ctor_get(v_x_3968_, 2);
v___x_3973_ = lean_name_eq(v_key_3970_, v_a_3967_);
if (v___x_3973_ == 0)
{
v_x_3968_ = v_tail_3972_;
goto _start;
}
else
{
lean_object* v___x_3975_; 
lean_inc(v_value_3971_);
v___x_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3975_, 0, v_value_3971_);
return v___x_3975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3976_, lean_object* v_x_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3976_, v_x_3977_);
lean_dec(v_x_3977_);
lean_dec(v_a_3976_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3979_, lean_object* v_a_3980_){
_start:
{
lean_object* v_buckets_3981_; lean_object* v___x_3982_; uint64_t v___y_3984_; 
v_buckets_3981_ = lean_ctor_get(v_m_3979_, 1);
v___x_3982_ = lean_array_get_size(v_buckets_3981_);
if (lean_obj_tag(v_a_3980_) == 0)
{
uint64_t v___x_3998_; 
v___x_3998_ = 1723ULL;
v___y_3984_ = v___x_3998_;
goto v___jp_3983_;
}
else
{
uint64_t v_hash_3999_; 
v_hash_3999_ = lean_ctor_get_uint64(v_a_3980_, sizeof(void*)*2);
v___y_3984_ = v_hash_3999_;
goto v___jp_3983_;
}
v___jp_3983_:
{
uint64_t v___x_3985_; uint64_t v___x_3986_; uint64_t v_fold_3987_; uint64_t v___x_3988_; uint64_t v___x_3989_; uint64_t v___x_3990_; size_t v___x_3991_; size_t v___x_3992_; size_t v___x_3993_; size_t v___x_3994_; size_t v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3985_ = 32ULL;
v___x_3986_ = lean_uint64_shift_right(v___y_3984_, v___x_3985_);
v_fold_3987_ = lean_uint64_xor(v___y_3984_, v___x_3986_);
v___x_3988_ = 16ULL;
v___x_3989_ = lean_uint64_shift_right(v_fold_3987_, v___x_3988_);
v___x_3990_ = lean_uint64_xor(v_fold_3987_, v___x_3989_);
v___x_3991_ = lean_uint64_to_usize(v___x_3990_);
v___x_3992_ = lean_usize_of_nat(v___x_3982_);
v___x_3993_ = ((size_t)1ULL);
v___x_3994_ = lean_usize_sub(v___x_3992_, v___x_3993_);
v___x_3995_ = lean_usize_land(v___x_3991_, v___x_3994_);
v___x_3996_ = lean_array_uget_borrowed(v_buckets_3981_, v___x_3995_);
v___x_3997_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3980_, v___x_3996_);
return v___x_3997_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_4000_, lean_object* v_a_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_4000_, v_a_4001_);
lean_dec(v_a_4001_);
lean_dec_ref(v_m_4000_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_4004_){
_start:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v_builderId_4008_; lean_object* v_ref_4009_; lean_object* v_args_4010_; lean_object* v___x_4011_; 
v___x_4006_ = l_Lean_attributeImplBuilderTableRef;
v___x_4007_ = lean_st_ref_get(v___x_4006_);
v_builderId_4008_ = lean_ctor_get(v_e_4004_, 0);
lean_inc(v_builderId_4008_);
v_ref_4009_ = lean_ctor_get(v_e_4004_, 1);
lean_inc(v_ref_4009_);
v_args_4010_ = lean_ctor_get(v_e_4004_, 2);
lean_inc(v_args_4010_);
lean_dec_ref(v_e_4004_);
v___x_4011_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4007_, v_builderId_4008_);
lean_dec(v___x_4007_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v___x_4012_; uint8_t v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
lean_dec(v_args_4010_);
lean_dec(v_ref_4009_);
v___x_4012_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_4013_ = 1;
v___x_4014_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_4008_, v___x_4013_);
v___x_4015_ = lean_string_append(v___x_4012_, v___x_4014_);
lean_dec_ref(v___x_4014_);
v___x_4016_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4017_ = lean_string_append(v___x_4015_, v___x_4016_);
v___x_4018_ = lean_mk_io_user_error(v___x_4017_);
v___x_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4018_);
return v___x_4019_;
}
else
{
lean_object* v_val_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
lean_dec(v_builderId_4008_);
v_val_4020_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_val_4020_);
lean_dec_ref_known(v___x_4011_, 1);
v___x_4021_ = lean_apply_2(v_val_4020_, v_ref_4009_, v_args_4010_);
v___x_4022_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_4021_);
return v___x_4022_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_4023_, lean_object* v_a_4024_){
_start:
{
lean_object* v_res_4025_; 
v_res_4025_ = l_Lean_mkAttributeImplOfEntry(v_e_4023_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_4026_, lean_object* v_m_4027_, lean_object* v_a_4028_){
_start:
{
lean_object* v___x_4029_; 
v___x_4029_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_4027_, v_a_4028_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_4030_, lean_object* v_m_4031_, lean_object* v_a_4032_){
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_4030_, v_m_4031_, v_a_4032_);
lean_dec(v_a_4032_);
lean_dec_ref(v_m_4031_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_4034_, lean_object* v_a_4035_, lean_object* v_x_4036_){
_start:
{
lean_object* v___x_4037_; 
v___x_4037_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_4035_, v_x_4036_);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4038_, lean_object* v_a_4039_, lean_object* v_x_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_4038_, v_a_4039_, v_x_4040_);
lean_dec(v_x_4040_);
lean_dec(v_a_4039_);
return v_res_4041_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4042_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_4043_ = lean_box(0);
v___x_4044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4043_);
lean_ctor_set(v___x_4044_, 1, v___x_4042_);
return v___x_4044_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_4045_; 
v___x_4045_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_4045_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4048_ = l_Lean_attributeMapRef;
v___x_4049_ = lean_st_ref_get(v___x_4048_);
v___x_4050_ = lean_box(0);
v___x_4051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4050_);
lean_ctor_set(v___x_4051_, 1, v___x_4049_);
v___x_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4051_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_4060_, lean_object* v_opts_4061_, lean_object* v_declName_4062_){
_start:
{
uint8_t v___x_4065_; lean_object* v___x_4066_; 
v___x_4065_ = 0;
lean_inc(v_declName_4062_);
lean_inc_ref(v_env_4060_);
v___x_4066_ = l_Lean_Environment_find_x3f(v_env_4060_, v_declName_4062_, v___x_4065_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v___x_4067_; uint8_t v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
lean_dec_ref(v_env_4060_);
v___x_4067_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_4068_ = 1;
v___x_4069_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_4062_, v___x_4068_);
v___x_4070_ = lean_string_append(v___x_4067_, v___x_4069_);
lean_dec_ref(v___x_4069_);
v___x_4071_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4072_ = lean_string_append(v___x_4070_, v___x_4071_);
v___x_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4072_);
return v___x_4073_;
}
else
{
lean_object* v_val_4074_; lean_object* v___x_4075_; 
v_val_4074_ = lean_ctor_get(v___x_4066_, 0);
lean_inc(v_val_4074_);
lean_dec_ref_known(v___x_4066_, 1);
v___x_4075_ = l_Lean_ConstantInfo_type(v_val_4074_);
lean_dec(v_val_4074_);
if (lean_obj_tag(v___x_4075_) == 4)
{
lean_object* v_declName_4076_; 
v_declName_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc(v_declName_4076_);
lean_dec_ref_known(v___x_4075_, 2);
if (lean_obj_tag(v_declName_4076_) == 1)
{
lean_object* v_pre_4077_; 
v_pre_4077_ = lean_ctor_get(v_declName_4076_, 0);
lean_inc(v_pre_4077_);
if (lean_obj_tag(v_pre_4077_) == 1)
{
lean_object* v_pre_4078_; 
v_pre_4078_ = lean_ctor_get(v_pre_4077_, 0);
if (lean_obj_tag(v_pre_4078_) == 0)
{
lean_object* v_str_4079_; lean_object* v_str_4080_; lean_object* v___x_4081_; uint8_t v___x_4082_; 
v_str_4079_ = lean_ctor_get(v_declName_4076_, 1);
lean_inc_ref(v_str_4079_);
lean_dec_ref_known(v_declName_4076_, 2);
v_str_4080_ = lean_ctor_get(v_pre_4077_, 1);
lean_inc_ref(v_str_4080_);
lean_dec_ref_known(v_pre_4077_, 2);
v___x_4081_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_4082_ = lean_string_dec_eq(v_str_4080_, v___x_4081_);
lean_dec_ref(v_str_4080_);
if (v___x_4082_ == 0)
{
lean_dec_ref(v_str_4079_);
lean_dec(v_declName_4062_);
lean_dec_ref(v_env_4060_);
goto v___jp_4063_;
}
else
{
lean_object* v___x_4083_; uint8_t v___x_4084_; 
v___x_4083_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_4084_ = lean_string_dec_eq(v_str_4079_, v___x_4083_);
lean_dec_ref(v_str_4079_);
if (v___x_4084_ == 0)
{
lean_dec(v_declName_4062_);
lean_dec_ref(v_env_4060_);
goto v___jp_4063_;
}
else
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Lean_Environment_evalConst___redArg(v_env_4060_, v_opts_4061_, v_declName_4062_, v___x_4084_);
lean_dec(v_declName_4062_);
lean_dec_ref(v_env_4060_);
return v___x_4085_;
}
}
}
else
{
lean_dec_ref_known(v_pre_4077_, 2);
lean_dec_ref_known(v_declName_4076_, 2);
lean_dec(v_declName_4062_);
lean_dec_ref(v_env_4060_);
goto v___jp_4063_;
}
}
else
{
lean_dec_ref_known(v_declName_4076_, 2);
lean_dec(v_pre_4077_);
lean_dec(v_declName_4062_);
lean_dec_ref(v_env_4060_);
goto v___jp_4063_;
}
}
else
{
lean_dec(v_declName_4076_);
lean_dec(v_declName_4062_);
lean_dec_ref(v_env_4060_);
goto v___jp_4063_;
}
}
else
{
lean_dec_ref(v___x_4075_);
lean_dec(v_declName_4062_);
lean_dec_ref(v_env_4060_);
goto v___jp_4063_;
}
}
v___jp_4063_:
{
lean_object* v___x_4064_; 
v___x_4064_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_4064_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_4086_, lean_object* v_opts_4087_, lean_object* v_declName_4088_){
_start:
{
lean_object* v_res_4089_; 
v_res_4089_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_4086_, v_opts_4087_, v_declName_4088_);
lean_dec_ref(v_opts_4087_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_4090_, size_t v_i_4091_, size_t v_stop_4092_, lean_object* v_b_4093_){
_start:
{
uint8_t v___x_4095_; 
v___x_4095_ = lean_usize_dec_eq(v_i_4091_, v_stop_4092_);
if (v___x_4095_ == 0)
{
lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___x_4096_ = lean_array_uget_borrowed(v_as_4090_, v_i_4091_);
lean_inc(v___x_4096_);
v___x_4097_ = l_Lean_mkAttributeImplOfEntry(v___x_4096_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v_a_4098_; lean_object* v_toAttributeImplCore_4099_; lean_object* v_name_4100_; lean_object* v___x_4101_; size_t v___x_4102_; size_t v___x_4103_; 
v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
lean_inc(v_a_4098_);
lean_dec_ref_known(v___x_4097_, 1);
v_toAttributeImplCore_4099_ = lean_ctor_get(v_a_4098_, 0);
v_name_4100_ = lean_ctor_get(v_toAttributeImplCore_4099_, 1);
lean_inc(v_name_4100_);
v___x_4101_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_4093_, v_name_4100_, v_a_4098_);
v___x_4102_ = ((size_t)1ULL);
v___x_4103_ = lean_usize_add(v_i_4091_, v___x_4102_);
v_i_4091_ = v___x_4103_;
v_b_4093_ = v___x_4101_;
goto _start;
}
else
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4112_; 
lean_dec_ref(v_b_4093_);
v_a_4105_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4107_ = v___x_4097_;
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v___x_4097_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4110_; 
if (v_isShared_4108_ == 0)
{
v___x_4110_ = v___x_4107_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4105_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
else
{
lean_object* v___x_4113_; 
v___x_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4113_, 0, v_b_4093_);
return v___x_4113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_4114_, lean_object* v_i_4115_, lean_object* v_stop_4116_, lean_object* v_b_4117_, lean_object* v___y_4118_){
_start:
{
size_t v_i_boxed_4119_; size_t v_stop_boxed_4120_; lean_object* v_res_4121_; 
v_i_boxed_4119_ = lean_unbox_usize(v_i_4115_);
lean_dec(v_i_4115_);
v_stop_boxed_4120_ = lean_unbox_usize(v_stop_4116_);
lean_dec(v_stop_4116_);
v_res_4121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4114_, v_i_boxed_4119_, v_stop_boxed_4120_, v_b_4117_);
lean_dec_ref(v_as_4114_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_4122_, size_t v_i_4123_, size_t v_stop_4124_, lean_object* v_b_4125_, lean_object* v___y_4126_){
_start:
{
lean_object* v_a_4129_; uint8_t v___x_4133_; 
v___x_4133_ = lean_usize_dec_eq(v_i_4123_, v_stop_4124_);
if (v___x_4133_ == 0)
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; uint8_t v___x_4137_; 
v___x_4134_ = lean_array_uget_borrowed(v_as_4122_, v_i_4123_);
v___x_4135_ = lean_unsigned_to_nat(0u);
v___x_4136_ = lean_array_get_size(v___x_4134_);
v___x_4137_ = lean_nat_dec_lt(v___x_4135_, v___x_4136_);
if (v___x_4137_ == 0)
{
v_a_4129_ = v_b_4125_;
goto v___jp_4128_;
}
else
{
size_t v___x_4138_; size_t v___x_4139_; lean_object* v___x_4140_; 
v___x_4138_ = ((size_t)0ULL);
v___x_4139_ = lean_usize_of_nat(v___x_4136_);
v___x_4140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4134_, v___x_4138_, v___x_4139_, v_b_4125_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4141_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref_known(v___x_4140_, 1);
v_a_4129_ = v_a_4141_;
goto v___jp_4128_;
}
else
{
return v___x_4140_;
}
}
}
else
{
lean_object* v___x_4142_; 
v___x_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4142_, 0, v_b_4125_);
return v___x_4142_;
}
v___jp_4128_:
{
size_t v___x_4130_; size_t v___x_4131_; 
v___x_4130_ = ((size_t)1ULL);
v___x_4131_ = lean_usize_add(v_i_4123_, v___x_4130_);
v_i_4123_ = v___x_4131_;
v_b_4125_ = v_a_4129_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4143_, lean_object* v_i_4144_, lean_object* v_stop_4145_, lean_object* v_b_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_){
_start:
{
size_t v_i_boxed_4149_; size_t v_stop_boxed_4150_; lean_object* v_res_4151_; 
v_i_boxed_4149_ = lean_unbox_usize(v_i_4144_);
lean_dec(v_i_4144_);
v_stop_boxed_4150_ = lean_unbox_usize(v_stop_4145_);
lean_dec(v_stop_4145_);
v_res_4151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4143_, v_i_boxed_4149_, v_stop_boxed_4150_, v_b_4146_, v___y_4147_);
lean_dec_ref(v___y_4147_);
lean_dec_ref(v_as_4143_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4152_, lean_object* v_a_4153_){
_start:
{
lean_object* v_a_4156_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; uint8_t v___x_4164_; 
v___x_4160_ = l_Lean_attributeMapRef;
v___x_4161_ = lean_st_ref_get(v___x_4160_);
v___x_4162_ = lean_unsigned_to_nat(0u);
v___x_4163_ = lean_array_get_size(v_es_4152_);
v___x_4164_ = lean_nat_dec_lt(v___x_4162_, v___x_4163_);
if (v___x_4164_ == 0)
{
v_a_4156_ = v___x_4161_;
goto v___jp_4155_;
}
else
{
size_t v___x_4165_; size_t v___x_4166_; lean_object* v___x_4167_; 
v___x_4165_ = ((size_t)0ULL);
v___x_4166_ = lean_usize_of_nat(v___x_4163_);
v___x_4167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4152_, v___x_4165_, v___x_4166_, v___x_4161_, v_a_4153_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_object* v_a_4168_; 
v_a_4168_ = lean_ctor_get(v___x_4167_, 0);
lean_inc(v_a_4168_);
lean_dec_ref_known(v___x_4167_, 1);
v_a_4156_ = v_a_4168_;
goto v___jp_4155_;
}
else
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
v_a_4169_ = lean_ctor_get(v___x_4167_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4171_ = v___x_4167_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4167_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
v___jp_4155_:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4157_ = lean_box(0);
v___x_4158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4157_);
lean_ctor_set(v___x_4158_, 1, v_a_4156_);
v___x_4159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4158_);
return v___x_4159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4177_, v_a_4178_);
lean_dec_ref(v_a_4178_);
lean_dec_ref(v_es_4177_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4181_, size_t v_i_4182_, size_t v_stop_4183_, lean_object* v_b_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v___x_4187_; 
v___x_4187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4181_, v_i_4182_, v_stop_4183_, v_b_4184_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4188_, lean_object* v_i_4189_, lean_object* v_stop_4190_, lean_object* v_b_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
size_t v_i_boxed_4194_; size_t v_stop_boxed_4195_; lean_object* v_res_4196_; 
v_i_boxed_4194_ = lean_unbox_usize(v_i_4189_);
lean_dec(v_i_4189_);
v_stop_boxed_4195_ = lean_unbox_usize(v_stop_4190_);
lean_dec(v_stop_4190_);
v_res_4196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4188_, v_i_boxed_4194_, v_stop_boxed_4195_, v_b_4191_, v___y_4192_);
lean_dec_ref(v___y_4192_);
lean_dec_ref(v_as_4188_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4197_, lean_object* v_e_4198_){
_start:
{
lean_object* v_snd_4199_; lean_object* v_toAttributeImplCore_4200_; lean_object* v_fst_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4219_; 
v_snd_4199_ = lean_ctor_get(v_e_4198_, 1);
lean_inc(v_snd_4199_);
v_toAttributeImplCore_4200_ = lean_ctor_get(v_snd_4199_, 0);
v_fst_4201_ = lean_ctor_get(v_e_4198_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v_e_4198_);
if (v_isSharedCheck_4219_ == 0)
{
lean_object* v_unused_4220_; 
v_unused_4220_ = lean_ctor_get(v_e_4198_, 1);
lean_dec(v_unused_4220_);
v___x_4203_ = v_e_4198_;
v_isShared_4204_ = v_isSharedCheck_4219_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_fst_4201_);
lean_dec(v_e_4198_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4219_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v_newEntries_4205_; lean_object* v_map_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4218_; 
v_newEntries_4205_ = lean_ctor_get(v_s_4197_, 0);
v_map_4206_ = lean_ctor_get(v_s_4197_, 1);
v_isSharedCheck_4218_ = !lean_is_exclusive(v_s_4197_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4208_ = v_s_4197_;
v_isShared_4209_ = v_isSharedCheck_4218_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_map_4206_);
lean_inc(v_newEntries_4205_);
lean_dec(v_s_4197_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4218_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v_name_4210_; lean_object* v___x_4212_; 
v_name_4210_ = lean_ctor_get(v_toAttributeImplCore_4200_, 1);
lean_inc(v_name_4210_);
if (v_isShared_4204_ == 0)
{
lean_ctor_set_tag(v___x_4203_, 1);
lean_ctor_set(v___x_4203_, 1, v_newEntries_4205_);
v___x_4212_ = v___x_4203_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_fst_4201_);
lean_ctor_set(v_reuseFailAlloc_4217_, 1, v_newEntries_4205_);
v___x_4212_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
lean_object* v___x_4213_; lean_object* v___x_4215_; 
v___x_4213_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4206_, v_name_4210_, v_snd_4199_);
if (v_isShared_4209_ == 0)
{
lean_ctor_set(v___x_4208_, 1, v___x_4213_);
lean_ctor_set(v___x_4208_, 0, v___x_4212_);
v___x_4215_ = v___x_4208_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4212_);
lean_ctor_set(v_reuseFailAlloc_4216_, 1, v___x_4213_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4221_, lean_object* v_s_4222_){
_start:
{
lean_object* v_newEntries_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; 
v_newEntries_4223_ = lean_ctor_get(v_s_4222_, 0);
lean_inc(v_newEntries_4223_);
lean_dec_ref(v_s_4222_);
v___x_4224_ = l_List_reverse___redArg(v_newEntries_4223_);
v___x_4225_ = lean_array_mk(v___x_4224_);
lean_inc_ref_n(v___x_4225_, 2);
v___x_4226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4226_, 0, v___x_4225_);
lean_ctor_set(v___x_4226_, 1, v___x_4225_);
lean_ctor_set(v___x_4226_, 2, v___x_4225_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4227_, lean_object* v_s_4228_){
_start:
{
lean_object* v_res_4229_; 
v_res_4229_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4227_, v_s_4228_);
lean_dec_ref(v_x_4227_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4230_){
_start:
{
lean_object* v_newEntries_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4242_; 
v_newEntries_4231_ = lean_ctor_get(v_s_4230_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v_s_4230_);
if (v_isSharedCheck_4242_ == 0)
{
lean_object* v_unused_4243_; 
v_unused_4243_ = lean_ctor_get(v_s_4230_, 1);
lean_dec(v_unused_4243_);
v___x_4233_ = v_s_4230_;
v_isShared_4234_ = v_isSharedCheck_4242_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_newEntries_4231_);
lean_dec(v_s_4230_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4242_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4240_; 
v___x_4235_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4236_ = l_List_lengthTR___redArg(v_newEntries_4231_);
lean_dec(v_newEntries_4231_);
v___x_4237_ = l_Nat_reprFast(v___x_4236_);
v___x_4238_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4237_);
if (v_isShared_4234_ == 0)
{
lean_ctor_set_tag(v___x_4233_, 5);
lean_ctor_set(v___x_4233_, 1, v___x_4238_);
lean_ctor_set(v___x_4233_, 0, v___x_4235_);
v___x_4240_ = v___x_4233_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v___x_4235_);
lean_ctor_set(v_reuseFailAlloc_4241_, 1, v___x_4238_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4244_){
_start:
{
lean_object* v_newEntries_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; 
v_newEntries_4245_ = lean_ctor_get(v_s_4244_, 0);
lean_inc(v_newEntries_4245_);
lean_dec_ref(v_s_4244_);
v___x_4246_ = l_List_reverse___redArg(v_newEntries_4245_);
v___x_4247_ = lean_array_mk(v___x_4246_);
return v___x_4247_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___f_4260_; lean_object* v___f_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4257_ = 0;
v___x_4258_ = lean_box(0);
v___x_4259_ = lean_box(2);
v___f_4260_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4261_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4262_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4263_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4264_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4265_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4266_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_4266_, 0, v___x_4265_);
lean_ctor_set(v___x_4266_, 1, v___x_4264_);
lean_ctor_set(v___x_4266_, 2, v___x_4263_);
lean_ctor_set(v___x_4266_, 3, v___x_4262_);
lean_ctor_set(v___x_4266_, 4, v___f_4261_);
lean_ctor_set(v___x_4266_, 5, v___f_4260_);
lean_ctor_set(v___x_4266_, 6, v___x_4259_);
lean_ctor_set(v___x_4266_, 7, v___x_4258_);
lean_ctor_set_uint8(v___x_4266_, sizeof(void*)*8, v___x_4257_);
lean_ctor_set_uint8(v___x_4266_, sizeof(void*)*8 + 1, v___x_4257_);
return v___x_4266_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___f_4267_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4268_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4268_);
lean_ctor_set(v___x_4269_, 1, v___f_4267_);
return v___x_4269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4271_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4272_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4271_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4275_){
_start:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; uint8_t v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v___x_4277_ = l_Lean_attributeMapRef;
v___x_4278_ = lean_st_ref_get(v___x_4277_);
v___x_4279_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4278_, v_n_4275_);
lean_dec(v___x_4278_);
v___x_4280_ = lean_box(v___x_4279_);
v___x_4281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4280_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4282_, lean_object* v_a_4283_){
_start:
{
lean_object* v_res_4284_; 
v_res_4284_ = l_Lean_isBuiltinAttribute(v_n_4282_);
lean_dec(v_n_4282_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4285_, lean_object* v_x_4286_){
_start:
{
if (lean_obj_tag(v_x_4286_) == 0)
{
return v_x_4285_;
}
else
{
lean_object* v_key_4287_; lean_object* v_tail_4288_; lean_object* v___x_4289_; 
v_key_4287_ = lean_ctor_get(v_x_4286_, 0);
v_tail_4288_ = lean_ctor_get(v_x_4286_, 2);
lean_inc(v_key_4287_);
v___x_4289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4289_, 0, v_key_4287_);
lean_ctor_set(v___x_4289_, 1, v_x_4285_);
v_x_4285_ = v___x_4289_;
v_x_4286_ = v_tail_4288_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4291_, lean_object* v_x_4292_){
_start:
{
lean_object* v_res_4293_; 
v_res_4293_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4291_, v_x_4292_);
lean_dec(v_x_4292_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4294_, size_t v_i_4295_, size_t v_stop_4296_, lean_object* v_b_4297_){
_start:
{
uint8_t v___x_4298_; 
v___x_4298_ = lean_usize_dec_eq(v_i_4295_, v_stop_4296_);
if (v___x_4298_ == 0)
{
lean_object* v___x_4299_; lean_object* v___x_4300_; size_t v___x_4301_; size_t v___x_4302_; 
v___x_4299_ = lean_array_uget_borrowed(v_as_4294_, v_i_4295_);
v___x_4300_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4297_, v___x_4299_);
v___x_4301_ = ((size_t)1ULL);
v___x_4302_ = lean_usize_add(v_i_4295_, v___x_4301_);
v_i_4295_ = v___x_4302_;
v_b_4297_ = v___x_4300_;
goto _start;
}
else
{
return v_b_4297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4304_, lean_object* v_i_4305_, lean_object* v_stop_4306_, lean_object* v_b_4307_){
_start:
{
size_t v_i_boxed_4308_; size_t v_stop_boxed_4309_; lean_object* v_res_4310_; 
v_i_boxed_4308_ = lean_unbox_usize(v_i_4305_);
lean_dec(v_i_4305_);
v_stop_boxed_4309_ = lean_unbox_usize(v_stop_4306_);
lean_dec(v_stop_4306_);
v_res_4310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4304_, v_i_boxed_4308_, v_stop_boxed_4309_, v_b_4307_);
lean_dec_ref(v_as_4304_);
return v_res_4310_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v_buckets_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; uint8_t v___x_4318_; 
v___x_4312_ = l_Lean_attributeMapRef;
v___x_4313_ = lean_st_ref_get(v___x_4312_);
v_buckets_4314_ = lean_ctor_get(v___x_4313_, 1);
lean_inc_ref(v_buckets_4314_);
lean_dec(v___x_4313_);
v___x_4315_ = lean_box(0);
v___x_4316_ = lean_unsigned_to_nat(0u);
v___x_4317_ = lean_array_get_size(v_buckets_4314_);
v___x_4318_ = lean_nat_dec_lt(v___x_4316_, v___x_4317_);
if (v___x_4318_ == 0)
{
lean_object* v___x_4319_; 
lean_dec_ref(v_buckets_4314_);
v___x_4319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4315_);
return v___x_4319_;
}
else
{
size_t v___x_4320_; size_t v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4320_ = ((size_t)0ULL);
v___x_4321_ = lean_usize_of_nat(v___x_4317_);
v___x_4322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4314_, v___x_4320_, v___x_4321_, v___x_4315_);
lean_dec_ref(v_buckets_4314_);
v___x_4323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4322_);
return v___x_4323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4324_){
_start:
{
lean_object* v_res_4325_; 
v_res_4325_ = l_Lean_getBuiltinAttributeNames();
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4327_){
_start:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4329_ = l_Lean_attributeMapRef;
v___x_4330_ = lean_st_ref_get(v___x_4329_);
v___x_4331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4330_, v_attrName_4327_);
lean_dec(v___x_4330_);
if (lean_obj_tag(v___x_4331_) == 0)
{
lean_object* v___x_4332_; uint8_t v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4332_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4333_ = 1;
v___x_4334_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4327_, v___x_4333_);
v___x_4335_ = lean_string_append(v___x_4332_, v___x_4334_);
lean_dec_ref(v___x_4334_);
v___x_4336_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4337_ = lean_string_append(v___x_4335_, v___x_4336_);
v___x_4338_ = lean_mk_io_user_error(v___x_4337_);
v___x_4339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4339_, 0, v___x_4338_);
return v___x_4339_;
}
else
{
lean_object* v_val_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4347_; 
lean_dec(v_attrName_4327_);
v_val_4340_ = lean_ctor_get(v___x_4331_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4331_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4342_ = v___x_4331_;
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_val_4340_);
lean_dec(v___x_4331_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4345_; 
if (v_isShared_4343_ == 0)
{
lean_ctor_set_tag(v___x_4342_, 0);
v___x_4345_ = v___x_4342_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_val_4340_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4348_, lean_object* v_a_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4348_);
return v_res_4350_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4351_, lean_object* v_attrName_4352_){
_start:
{
lean_object* v___x_4353_; lean_object* v_toEnvExtension_4354_; lean_object* v_asyncMode_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; uint8_t v___x_4358_; lean_object* v___x_4359_; lean_object* v_map_4360_; uint8_t v___x_4361_; 
v___x_4353_ = l_Lean_attributeExtension;
v_toEnvExtension_4354_ = lean_ctor_get(v___x_4353_, 0);
v_asyncMode_4355_ = lean_ctor_get(v_toEnvExtension_4354_, 2);
v___x_4356_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4357_ = lean_box(0);
v___x_4358_ = 0;
v___x_4359_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4356_, v___x_4353_, v_env_4351_, v_asyncMode_4355_, v___x_4357_, v___x_4358_);
v_map_4360_ = lean_ctor_get(v___x_4359_, 1);
lean_inc_ref(v_map_4360_);
lean_dec(v___x_4359_);
v___x_4361_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4360_, v_attrName_4352_);
lean_dec_ref(v_map_4360_);
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4362_, lean_object* v_attrName_4363_){
_start:
{
uint8_t v_res_4364_; lean_object* v_r_4365_; 
v_res_4364_ = l_Lean_isAttribute(v_env_4362_, v_attrName_4363_);
lean_dec(v_attrName_4363_);
v_r_4365_ = lean_box(v_res_4364_);
return v_r_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4366_){
_start:
{
lean_object* v___x_4367_; lean_object* v_toEnvExtension_4368_; lean_object* v_asyncMode_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; uint8_t v___x_4372_; lean_object* v___x_4373_; lean_object* v_map_4374_; lean_object* v_buckets_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; uint8_t v___x_4379_; 
v___x_4367_ = l_Lean_attributeExtension;
v_toEnvExtension_4368_ = lean_ctor_get(v___x_4367_, 0);
v_asyncMode_4369_ = lean_ctor_get(v_toEnvExtension_4368_, 2);
v___x_4370_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4371_ = lean_box(0);
v___x_4372_ = 0;
v___x_4373_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4370_, v___x_4367_, v_env_4366_, v_asyncMode_4369_, v___x_4371_, v___x_4372_);
v_map_4374_ = lean_ctor_get(v___x_4373_, 1);
lean_inc_ref(v_map_4374_);
lean_dec(v___x_4373_);
v_buckets_4375_ = lean_ctor_get(v_map_4374_, 1);
lean_inc_ref(v_buckets_4375_);
lean_dec_ref(v_map_4374_);
v___x_4376_ = lean_box(0);
v___x_4377_ = lean_unsigned_to_nat(0u);
v___x_4378_ = lean_array_get_size(v_buckets_4375_);
v___x_4379_ = lean_nat_dec_lt(v___x_4377_, v___x_4378_);
if (v___x_4379_ == 0)
{
lean_dec_ref(v_buckets_4375_);
return v___x_4376_;
}
else
{
size_t v___x_4380_; size_t v___x_4381_; lean_object* v___x_4382_; 
v___x_4380_ = ((size_t)0ULL);
v___x_4381_ = lean_usize_of_nat(v___x_4378_);
v___x_4382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4375_, v___x_4380_, v___x_4381_, v___x_4376_);
lean_dec_ref(v_buckets_4375_);
return v___x_4382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4383_, lean_object* v_attrName_4384_){
_start:
{
lean_object* v___x_4385_; lean_object* v_toEnvExtension_4386_; lean_object* v_asyncMode_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; uint8_t v___x_4390_; lean_object* v___x_4391_; lean_object* v_map_4392_; lean_object* v___x_4393_; 
v___x_4385_ = l_Lean_attributeExtension;
v_toEnvExtension_4386_ = lean_ctor_get(v___x_4385_, 0);
v_asyncMode_4387_ = lean_ctor_get(v_toEnvExtension_4386_, 2);
v___x_4388_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4389_ = lean_box(0);
v___x_4390_ = 0;
v___x_4391_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4388_, v___x_4385_, v_env_4383_, v_asyncMode_4387_, v___x_4389_, v___x_4390_);
v_map_4392_ = lean_ctor_get(v___x_4391_, 1);
lean_inc_ref(v_map_4392_);
lean_dec(v___x_4391_);
v___x_4393_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4392_, v_attrName_4384_);
lean_dec_ref(v_map_4392_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_object* v___x_4394_; uint8_t v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4394_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4395_ = 1;
v___x_4396_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4384_, v___x_4395_);
v___x_4397_ = lean_string_append(v___x_4394_, v___x_4396_);
lean_dec_ref(v___x_4396_);
v___x_4398_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4399_ = lean_string_append(v___x_4397_, v___x_4398_);
v___x_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4399_);
return v___x_4400_;
}
else
{
lean_object* v_val_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4408_; 
lean_dec(v_attrName_4384_);
v_val_4401_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v___x_4393_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_val_4401_);
lean_dec(v___x_4393_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4406_; 
if (v_isShared_4404_ == 0)
{
v___x_4406_ = v___x_4403_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_val_4401_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___lam__0(lean_object* v_addEntryFn_4409_, lean_object* v___x_4410_, lean_object* v_s_4411_){
_start:
{
lean_object* v_importedEntries_4412_; lean_object* v_state_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4421_; 
v_importedEntries_4412_ = lean_ctor_get(v_s_4411_, 0);
v_state_4413_ = lean_ctor_get(v_s_4411_, 1);
v_isSharedCheck_4421_ = !lean_is_exclusive(v_s_4411_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4415_ = v_s_4411_;
v_isShared_4416_ = v_isSharedCheck_4421_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_state_4413_);
lean_inc(v_importedEntries_4412_);
lean_dec(v_s_4411_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4421_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v_state_4417_; lean_object* v___x_4419_; 
v_state_4417_ = lean_apply_2(v_addEntryFn_4409_, v_state_4413_, v___x_4410_);
if (v_isShared_4416_ == 0)
{
lean_ctor_set(v___x_4415_, 1, v_state_4417_);
v___x_4419_ = v___x_4415_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_importedEntries_4412_);
lean_ctor_set(v_reuseFailAlloc_4420_, 1, v_state_4417_);
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
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4422_, lean_object* v_builderId_4423_, lean_object* v_ref_4424_, lean_object* v_args_4425_){
_start:
{
lean_object* v_entry_4427_; lean_object* v___x_4428_; 
v_entry_4427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4427_, 0, v_builderId_4423_);
lean_ctor_set(v_entry_4427_, 1, v_ref_4424_);
lean_ctor_set(v_entry_4427_, 2, v_args_4425_);
lean_inc_ref(v_entry_4427_);
v___x_4428_ = l_Lean_mkAttributeImplOfEntry(v_entry_4427_);
if (lean_obj_tag(v___x_4428_) == 0)
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4463_; 
v_a_4429_ = lean_ctor_get(v___x_4428_, 0);
v_isSharedCheck_4463_ = !lean_is_exclusive(v___x_4428_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4431_ = v___x_4428_;
v_isShared_4432_ = v_isSharedCheck_4463_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4428_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4463_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v_toAttributeImplCore_4433_; lean_object* v_name_4434_; uint8_t v___x_4435_; 
v_toAttributeImplCore_4433_ = lean_ctor_get(v_a_4429_, 0);
v_name_4434_ = lean_ctor_get(v_toAttributeImplCore_4433_, 1);
lean_inc_ref(v_env_4422_);
v___x_4435_ = l_Lean_isAttribute(v_env_4422_, v_name_4434_);
if (v___x_4435_ == 0)
{
lean_object* v___x_4436_; lean_object* v_toEnvExtension_4437_; lean_object* v_addEntryFn_4438_; lean_object* v_asyncMode_4439_; uint8_t v_logWrites_4440_; lean_object* v___x_4441_; lean_object* v___f_4442_; lean_object* v___x_4443_; uint8_t v___x_4444_; 
v___x_4436_ = l_Lean_attributeExtension;
v_toEnvExtension_4437_ = lean_ctor_get(v___x_4436_, 0);
v_addEntryFn_4438_ = lean_ctor_get(v___x_4436_, 3);
v_asyncMode_4439_ = lean_ctor_get(v_toEnvExtension_4437_, 2);
v_logWrites_4440_ = lean_ctor_get_uint8(v_toEnvExtension_4437_, sizeof(void*)*6);
v___x_4441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4441_, 0, v_entry_4427_);
lean_ctor_set(v___x_4441_, 1, v_a_4429_);
lean_inc(v_addEntryFn_4438_);
v___f_4442_ = lean_alloc_closure((void*)(l_Lean_registerAttributeOfBuilder___lam__0), 3, 2);
lean_closure_set(v___f_4442_, 0, v_addEntryFn_4438_);
lean_closure_set(v___f_4442_, 1, v___x_4441_);
v___x_4443_ = lean_box(0);
v___x_4444_ = 1;
if (v_logWrites_4440_ == 0)
{
lean_object* v___x_4445_; lean_object* v___x_4447_; 
lean_inc_ref(v_toEnvExtension_4437_);
v___x_4445_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4437_, v_env_4422_, v___f_4442_, v_asyncMode_4439_, v___x_4443_, v___x_4444_);
if (v_isShared_4432_ == 0)
{
lean_ctor_set(v___x_4431_, 0, v___x_4445_);
v___x_4447_ = v___x_4431_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v___x_4445_);
v___x_4447_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
return v___x_4447_;
}
}
else
{
lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4452_; 
lean_inc_ref_n(v_toEnvExtension_4437_, 2);
v___x_4449_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4437_, v_env_4422_);
lean_dec_ref(v_env_4422_);
v___x_4450_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4437_, v___x_4449_, v___f_4442_, v_asyncMode_4439_, v___x_4443_, v___x_4444_);
if (v_isShared_4432_ == 0)
{
lean_ctor_set(v___x_4431_, 0, v___x_4450_);
v___x_4452_ = v___x_4431_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v___x_4450_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
else
{
lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4461_; 
lean_inc(v_name_4434_);
lean_dec(v_a_4429_);
lean_dec_ref_known(v_entry_4427_, 3);
lean_dec_ref(v_env_4422_);
v___x_4454_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4455_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4434_, v___x_4435_);
v___x_4456_ = lean_string_append(v___x_4454_, v___x_4455_);
lean_dec_ref(v___x_4455_);
v___x_4457_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4458_ = lean_string_append(v___x_4456_, v___x_4457_);
v___x_4459_ = lean_mk_io_user_error(v___x_4458_);
if (v_isShared_4432_ == 0)
{
lean_ctor_set_tag(v___x_4431_, 1);
lean_ctor_set(v___x_4431_, 0, v___x_4459_);
v___x_4461_ = v___x_4431_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v___x_4459_);
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
else
{
lean_object* v_a_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4471_; 
lean_dec_ref_known(v_entry_4427_, 3);
lean_dec_ref(v_env_4422_);
v_a_4464_ = lean_ctor_get(v___x_4428_, 0);
v_isSharedCheck_4471_ = !lean_is_exclusive(v___x_4428_);
if (v_isSharedCheck_4471_ == 0)
{
v___x_4466_ = v___x_4428_;
v_isShared_4467_ = v_isSharedCheck_4471_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_a_4464_);
lean_dec(v___x_4428_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4471_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v___x_4469_; 
if (v_isShared_4467_ == 0)
{
v___x_4469_ = v___x_4466_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v_a_4464_);
v___x_4469_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
return v___x_4469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4472_, lean_object* v_builderId_4473_, lean_object* v_ref_4474_, lean_object* v_args_4475_, lean_object* v_a_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l_Lean_registerAttributeOfBuilder(v_env_4472_, v_builderId_4473_, v_ref_4474_, v_args_4475_);
return v_res_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_){
_start:
{
if (lean_obj_tag(v_x_4478_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v_a_4482_ = lean_ctor_get(v_x_4478_, 0);
lean_inc(v_a_4482_);
lean_dec_ref_known(v_x_4478_, 1);
v___x_4483_ = l_Lean_stringToMessageData(v_a_4482_);
v___x_4484_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4483_, v___y_4479_, v___y_4480_);
return v___x_4484_;
}
else
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4492_; 
v_a_4485_ = lean_ctor_get(v_x_4478_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v_x_4478_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4487_ = v_x_4478_;
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v_x_4478_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4490_; 
if (v_isShared_4488_ == 0)
{
lean_ctor_set_tag(v___x_4487_, 0);
v___x_4490_ = v___x_4487_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4485_);
v___x_4490_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
return v___x_4490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v_res_4497_; 
v_res_4497_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4493_, v___y_4494_, v___y_4495_);
lean_dec(v___y_4495_);
lean_dec_ref(v___y_4494_);
return v_res_4497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4498_, lean_object* v_attrName_4499_, lean_object* v_stx_4500_, uint8_t v_kind_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_){
_start:
{
lean_object* v___x_4505_; lean_object* v_env_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; 
v___x_4505_ = lean_st_ref_get(v_a_4503_);
v_env_4506_ = lean_ctor_get(v___x_4505_, 0);
lean_inc_ref(v_env_4506_);
lean_dec(v___x_4505_);
v___x_4507_ = l_Lean_getAttributeImpl(v_env_4506_, v_attrName_4499_);
v___x_4508_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4507_, v_a_4502_, v_a_4503_);
if (lean_obj_tag(v___x_4508_) == 0)
{
lean_object* v_a_4509_; lean_object* v_add_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; 
v_a_4509_ = lean_ctor_get(v___x_4508_, 0);
lean_inc(v_a_4509_);
lean_dec_ref_known(v___x_4508_, 1);
v_add_4510_ = lean_ctor_get(v_a_4509_, 1);
lean_inc_ref(v_add_4510_);
lean_dec(v_a_4509_);
v___x_4511_ = lean_box(v_kind_4501_);
lean_inc(v_a_4503_);
lean_inc_ref(v_a_4502_);
v___x_4512_ = lean_apply_6(v_add_4510_, v_declName_4498_, v_stx_4500_, v___x_4511_, v_a_4502_, v_a_4503_, lean_box(0));
return v___x_4512_;
}
else
{
lean_object* v_a_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4520_; 
lean_dec(v_stx_4500_);
lean_dec(v_declName_4498_);
v_a_4513_ = lean_ctor_get(v___x_4508_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4508_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4515_ = v___x_4508_;
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_a_4513_);
lean_dec(v___x_4508_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4518_; 
if (v_isShared_4516_ == 0)
{
v___x_4518_ = v___x_4515_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4513_);
v___x_4518_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
return v___x_4518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4521_, lean_object* v_attrName_4522_, lean_object* v_stx_4523_, lean_object* v_kind_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_){
_start:
{
uint8_t v_kind_boxed_4528_; lean_object* v_res_4529_; 
v_kind_boxed_4528_ = lean_unbox(v_kind_4524_);
v_res_4529_ = l_Lean_Attribute_add(v_declName_4521_, v_attrName_4522_, v_stx_4523_, v_kind_boxed_4528_, v_a_4525_, v_a_4526_);
lean_dec(v_a_4526_);
lean_dec_ref(v_a_4525_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4530_, lean_object* v_x_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
lean_object* v___x_4535_; 
v___x_4535_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4531_, v___y_4532_, v___y_4533_);
return v___x_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4536_, lean_object* v_x_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_){
_start:
{
lean_object* v_res_4541_; 
v_res_4541_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4536_, v_x_4537_, v___y_4538_, v___y_4539_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
return v_res_4541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4542_, lean_object* v_attrName_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_){
_start:
{
lean_object* v___x_4547_; lean_object* v_env_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; 
v___x_4547_ = lean_st_ref_get(v_a_4545_);
v_env_4548_ = lean_ctor_get(v___x_4547_, 0);
lean_inc_ref(v_env_4548_);
lean_dec(v___x_4547_);
v___x_4549_ = l_Lean_getAttributeImpl(v_env_4548_, v_attrName_4543_);
v___x_4550_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4549_, v_a_4544_, v_a_4545_);
if (lean_obj_tag(v___x_4550_) == 0)
{
lean_object* v_a_4551_; lean_object* v_erase_4552_; lean_object* v___x_4553_; 
v_a_4551_ = lean_ctor_get(v___x_4550_, 0);
lean_inc(v_a_4551_);
lean_dec_ref_known(v___x_4550_, 1);
v_erase_4552_ = lean_ctor_get(v_a_4551_, 2);
lean_inc_ref(v_erase_4552_);
lean_dec(v_a_4551_);
lean_inc(v_a_4545_);
lean_inc_ref(v_a_4544_);
v___x_4553_ = lean_apply_4(v_erase_4552_, v_declName_4542_, v_a_4544_, v_a_4545_, lean_box(0));
return v___x_4553_;
}
else
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4561_; 
lean_dec(v_declName_4542_);
v_a_4554_ = lean_ctor_get(v___x_4550_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4550_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4556_ = v___x_4550_;
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v___x_4550_);
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
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4562_, lean_object* v_attrName_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_){
_start:
{
lean_object* v_res_4567_; 
v_res_4567_ = l_Lean_Attribute_erase(v_declName_4562_, v_attrName_4563_, v_a_4564_, v_a_4565_);
lean_dec(v_a_4565_);
lean_dec_ref(v_a_4564_);
return v_res_4567_;
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___lam__0(lean_object* v___y_4568_, lean_object* v_ps_4569_){
_start:
{
lean_object* v_importedEntries_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4577_; 
v_importedEntries_4570_ = lean_ctor_get(v_ps_4569_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v_ps_4569_);
if (v_isSharedCheck_4577_ == 0)
{
lean_object* v_unused_4578_; 
v_unused_4578_ = lean_ctor_get(v_ps_4569_, 1);
lean_dec(v_unused_4578_);
v___x_4572_ = v_ps_4569_;
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_importedEntries_4570_);
lean_dec(v_ps_4569_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4575_; 
if (v_isShared_4573_ == 0)
{
lean_ctor_set(v___x_4572_, 1, v___y_4568_);
v___x_4575_ = v___x_4572_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_importedEntries_4570_);
lean_ctor_set(v_reuseFailAlloc_4576_, 1, v___y_4568_);
v___x_4575_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
return v___x_4575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4579_, lean_object* v_x_4580_){
_start:
{
if (lean_obj_tag(v_x_4580_) == 0)
{
return v_x_4579_;
}
else
{
lean_object* v_key_4581_; lean_object* v_value_4582_; lean_object* v_tail_4583_; lean_object* v_newEntries_4584_; lean_object* v_map_4585_; uint8_t v___x_4586_; 
v_key_4581_ = lean_ctor_get(v_x_4580_, 0);
lean_inc(v_key_4581_);
v_value_4582_ = lean_ctor_get(v_x_4580_, 1);
lean_inc(v_value_4582_);
v_tail_4583_ = lean_ctor_get(v_x_4580_, 2);
lean_inc(v_tail_4583_);
lean_dec_ref_known(v_x_4580_, 3);
v_newEntries_4584_ = lean_ctor_get(v_x_4579_, 0);
v_map_4585_ = lean_ctor_get(v_x_4579_, 1);
v___x_4586_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4585_, v_key_4581_);
if (v___x_4586_ == 0)
{
lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4595_; 
lean_inc_ref(v_map_4585_);
lean_inc(v_newEntries_4584_);
v_isSharedCheck_4595_ = !lean_is_exclusive(v_x_4579_);
if (v_isSharedCheck_4595_ == 0)
{
lean_object* v_unused_4596_; lean_object* v_unused_4597_; 
v_unused_4596_ = lean_ctor_get(v_x_4579_, 1);
lean_dec(v_unused_4596_);
v_unused_4597_ = lean_ctor_get(v_x_4579_, 0);
lean_dec(v_unused_4597_);
v___x_4588_ = v_x_4579_;
v_isShared_4589_ = v_isSharedCheck_4595_;
goto v_resetjp_4587_;
}
else
{
lean_dec(v_x_4579_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4595_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4590_; lean_object* v___x_4592_; 
v___x_4590_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4585_, v_key_4581_, v_value_4582_);
if (v_isShared_4589_ == 0)
{
lean_ctor_set(v___x_4588_, 1, v___x_4590_);
v___x_4592_ = v___x_4588_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_newEntries_4584_);
lean_ctor_set(v_reuseFailAlloc_4594_, 1, v___x_4590_);
v___x_4592_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
v_x_4579_ = v___x_4592_;
v_x_4580_ = v_tail_4583_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4582_);
lean_dec(v_key_4581_);
v_x_4580_ = v_tail_4583_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4599_, size_t v_i_4600_, size_t v_stop_4601_, lean_object* v_b_4602_){
_start:
{
uint8_t v___x_4603_; 
v___x_4603_ = lean_usize_dec_eq(v_i_4600_, v_stop_4601_);
if (v___x_4603_ == 0)
{
lean_object* v___x_4604_; lean_object* v___x_4605_; size_t v___x_4606_; size_t v___x_4607_; 
v___x_4604_ = lean_array_uget_borrowed(v_as_4599_, v_i_4600_);
lean_inc(v___x_4604_);
v___x_4605_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4602_, v___x_4604_);
v___x_4606_ = ((size_t)1ULL);
v___x_4607_ = lean_usize_add(v_i_4600_, v___x_4606_);
v_i_4600_ = v___x_4607_;
v_b_4602_ = v___x_4605_;
goto _start;
}
else
{
return v_b_4602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4609_, lean_object* v_i_4610_, lean_object* v_stop_4611_, lean_object* v_b_4612_){
_start:
{
size_t v_i_boxed_4613_; size_t v_stop_boxed_4614_; lean_object* v_res_4615_; 
v_i_boxed_4613_ = lean_unbox_usize(v_i_4610_);
lean_dec(v_i_4610_);
v_stop_boxed_4614_ = lean_unbox_usize(v_stop_4611_);
lean_dec(v_stop_4611_);
v_res_4615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4609_, v_i_boxed_4613_, v_stop_boxed_4614_, v_b_4612_);
lean_dec_ref(v_as_4609_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4616_){
_start:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v_toEnvExtension_4622_; lean_object* v_asyncMode_4623_; uint8_t v_logWrites_4624_; lean_object* v___y_4626_; lean_object* v_buckets_4635_; lean_object* v___x_4636_; uint8_t v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; uint8_t v___x_4641_; 
v___x_4618_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4619_ = l_Lean_attributeMapRef;
v___x_4620_ = lean_st_ref_get(v___x_4619_);
v___x_4621_ = l_Lean_attributeExtension;
v_toEnvExtension_4622_ = lean_ctor_get(v___x_4621_, 0);
v_asyncMode_4623_ = lean_ctor_get(v_toEnvExtension_4622_, 2);
v_logWrites_4624_ = lean_ctor_get_uint8(v_toEnvExtension_4622_, sizeof(void*)*6);
v_buckets_4635_ = lean_ctor_get(v___x_4620_, 1);
lean_inc_ref(v_buckets_4635_);
lean_dec(v___x_4620_);
v___x_4636_ = lean_box(0);
v___x_4637_ = 0;
lean_inc_ref(v_env_4616_);
v___x_4638_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4618_, v___x_4621_, v_env_4616_, v_asyncMode_4623_, v___x_4636_, v___x_4637_);
v___x_4639_ = lean_unsigned_to_nat(0u);
v___x_4640_ = lean_array_get_size(v_buckets_4635_);
v___x_4641_ = lean_nat_dec_lt(v___x_4639_, v___x_4640_);
if (v___x_4641_ == 0)
{
lean_dec_ref(v_buckets_4635_);
v___y_4626_ = v___x_4638_;
goto v___jp_4625_;
}
else
{
size_t v___x_4642_; size_t v___x_4643_; lean_object* v___x_4644_; 
v___x_4642_ = ((size_t)0ULL);
v___x_4643_ = lean_usize_of_nat(v___x_4640_);
v___x_4644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4635_, v___x_4642_, v___x_4643_, v___x_4638_);
lean_dec_ref(v_buckets_4635_);
v___y_4626_ = v___x_4644_;
goto v___jp_4625_;
}
v___jp_4625_:
{
lean_object* v___f_4627_; lean_object* v___x_4628_; uint8_t v___x_4629_; 
v___f_4627_ = lean_alloc_closure((void*)(l_Lean_updateEnvAttributesImpl___lam__0), 2, 1);
lean_closure_set(v___f_4627_, 0, v___y_4626_);
v___x_4628_ = lean_box(0);
v___x_4629_ = 1;
if (v_logWrites_4624_ == 0)
{
lean_object* v___x_4630_; lean_object* v___x_4631_; 
lean_inc_ref(v_toEnvExtension_4622_);
v___x_4630_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4622_, v_env_4616_, v___f_4627_, v_asyncMode_4623_, v___x_4628_, v___x_4629_);
v___x_4631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4631_, 0, v___x_4630_);
return v___x_4631_;
}
else
{
lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; 
lean_inc_ref_n(v_toEnvExtension_4622_, 2);
v___x_4632_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4622_, v_env_4616_);
lean_dec_ref(v_env_4616_);
v___x_4633_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4622_, v___x_4632_, v___f_4627_, v_asyncMode_4623_, v___x_4628_, v___x_4629_);
v___x_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4633_);
return v___x_4634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4645_, lean_object* v_a_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = lean_update_env_attributes(v_env_4645_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v_size_4651_; lean_object* v___x_4652_; 
v___x_4649_ = l_Lean_attributeMapRef;
v___x_4650_ = lean_st_ref_get(v___x_4649_);
v_size_4651_ = lean_ctor_get(v___x_4650_, 0);
lean_inc(v_size_4651_);
lean_dec(v___x_4650_);
v___x_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4652_, 0, v_size_4651_);
return v___x_4652_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = lean_get_num_attributes();
return v_res_4654_;
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
