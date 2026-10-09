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
lean_object* l_Lean_AttributeApplicationTime_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_AttributeApplicationTime_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_AttributeApplicationTime_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_AttributeApplicationTime_ctorIdx___impl(v_x_4__boxed_6_);
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
lean_object* l_Lean_AttributeApplicationTime_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_AttributeApplicationTime_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_AttributeApplicationTime_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_AttributeApplicationTime_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(lean_object* v_afterTypeChecking_24_){
_start:
{
lean_inc(v_afterTypeChecking_24_);
return v_afterTypeChecking_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg___boxed(lean_object* v_afterTypeChecking_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(v_afterTypeChecking_25_);
lean_dec(v_afterTypeChecking_25_);
return v_res_26_;
}
}
lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_afterTypeChecking_30_){
_start:
{
lean_inc(v_afterTypeChecking_30_);
return v_afterTypeChecking_30_;
}
}
LEAN_EXPORT void l_Lean_AttributeApplicationTime_afterTypeChecking_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_afterTypeChecking_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_AttributeApplicationTime_afterTypeChecking_elim(lean_box(0), v_t_28_, lean_box(0), v_afterTypeChecking_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_afterTypeChecking_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_AttributeApplicationTime_afterTypeChecking_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_afterTypeChecking_35_);
lean_dec(v_afterTypeChecking_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(lean_object* v_afterCompilation_38_){
_start:
{
lean_inc(v_afterCompilation_38_);
return v_afterCompilation_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg___boxed(lean_object* v_afterCompilation_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(v_afterCompilation_39_);
lean_dec(v_afterCompilation_39_);
return v_res_40_;
}
}
lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_afterCompilation_44_){
_start:
{
lean_inc(v_afterCompilation_44_);
return v_afterCompilation_44_;
}
}
LEAN_EXPORT void l_Lean_AttributeApplicationTime_afterCompilation_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_afterCompilation_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_AttributeApplicationTime_afterCompilation_elim(lean_box(0), v_t_42_, lean_box(0), v_afterCompilation_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_afterCompilation_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_AttributeApplicationTime_afterCompilation_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_afterCompilation_49_);
lean_dec(v_afterCompilation_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(lean_object* v_beforeElaboration_52_){
_start:
{
lean_inc(v_beforeElaboration_52_);
return v_beforeElaboration_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg___boxed(lean_object* v_beforeElaboration_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(v_beforeElaboration_53_);
lean_dec(v_beforeElaboration_53_);
return v_res_54_;
}
}
lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_beforeElaboration_58_){
_start:
{
lean_inc(v_beforeElaboration_58_);
return v_beforeElaboration_58_;
}
}
LEAN_EXPORT void l_Lean_AttributeApplicationTime_beforeElaboration_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_beforeElaboration_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_AttributeApplicationTime_beforeElaboration_elim(lean_box(0), v_t_56_, lean_box(0), v_beforeElaboration_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_beforeElaboration_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_AttributeApplicationTime_beforeElaboration_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_beforeElaboration_63_);
lean_dec(v_beforeElaboration_63_);
return v_res_65_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeApplicationTime_default(void){
_start:
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeApplicationTime(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
uint8_t l_Lean_instBEqAttributeApplicationTime_beq(uint8_t v_x_68_, uint8_t v_y_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_70_ = lean_box(v_x_68_);
v___x_71_ = lean_obj_tag_nat(v___x_70_);
lean_dec(v___x_70_);
v___x_72_ = lean_box(v_y_69_);
v___x_73_ = lean_obj_tag_nat(v___x_72_);
lean_dec(v___x_72_);
v___x_74_ = lean_nat_dec_eq(v___x_71_, v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT void l_Lean_instBEqAttributeApplicationTime_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_68_ = stack[0].m_num;
uint8_t v_y_69_ = stack[1].m_num;
uint8_t v_res_75_;
v_res_75_ = l_Lean_instBEqAttributeApplicationTime_beq(v_x_68_, v_y_69_);
stack->m_num = v_res_75_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeApplicationTime_beq___boxed(lean_object* v_x_76_, lean_object* v_y_77_){
_start:
{
uint8_t v_x_24__boxed_78_; uint8_t v_y_25__boxed_79_; uint8_t v_res_80_; lean_object* v_r_81_; 
v_x_24__boxed_78_ = lean_unbox(v_x_76_);
v_y_25__boxed_79_ = lean_unbox(v_y_77_);
v_res_80_ = l_Lean_instBEqAttributeApplicationTime_beq(v_x_24__boxed_78_, v_y_25__boxed_79_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0(lean_object* v_00_u03b1_84_, lean_object* v_x_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v___x_89_; lean_object* v_env_90_; lean_object* v_ref_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_89_ = lean_st_ref_get(v___y_87_);
v_env_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc_ref(v_env_90_);
lean_dec(v___x_89_);
v_ref_91_ = lean_ctor_get(v___y_86_, 2);
v___x_92_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_86_);
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v_env_90_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = lean_apply_2(v_x_85_, v___x_93_, lean_box(0));
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v___x_94_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_94_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
else
{
lean_object* v_a_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_114_; 
v_a_103_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_114_ == 0)
{
v___x_105_ = v___x_94_;
v_isShared_106_ = v_isSharedCheck_114_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_a_103_);
lean_dec(v___x_94_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_114_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_107_ = lean_io_error_to_string(v_a_103_);
v___x_108_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
v___x_109_ = l_Lean_MessageData_ofFormat(v___x_108_);
lean_inc(v_ref_91_);
v___x_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_110_, 0, v_ref_91_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_110_);
v___x_112_ = v___x_105_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instMonadLiftImportMAttrM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_85_ = stack[1].m_obj;
lean_object* v___y_86_ = stack[2].m_obj;
lean_object* v___y_87_ = stack[3].m_obj;
lean_object* v_res_115_;
v_res_115_ = l_Lean_instMonadLiftImportMAttrM___lam__0(lean_box(0), v_x_85_, v___y_86_, v___y_87_);
stack->m_obj
 = v_res_115_;
}
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0___boxed(lean_object* v_00_u03b1_116_, lean_object* v_x_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_instMonadLiftImportMAttrM___lam__0(v_00_u03b1_116_, v_x_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
return v_res_121_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__10));
v___x_151_ = l_Lean_mkAtom(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__12, &l_Lean_AttributeImplCore_ref___autoParam___closed__12_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12);
v___x_153_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_154_ = lean_array_push(v___x_153_, v___x_152_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__17));
v___x_164_ = l_Lean_mkAtom(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__18, &l_Lean_AttributeImplCore_ref___autoParam___closed__18_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18);
v___x_166_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_167_ = lean_array_push(v___x_166_, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__19, &l_Lean_AttributeImplCore_ref___autoParam___closed__19_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19);
v___x_169_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__16));
v___x_170_ = lean_box(2);
v___x_171_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
lean_ctor_set(v___x_171_, 2, v___x_168_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__20, &l_Lean_AttributeImplCore_ref___autoParam___closed__20_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20);
v___x_173_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__13, &l_Lean_AttributeImplCore_ref___autoParam___closed__13_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13);
v___x_174_ = lean_array_push(v___x_173_, v___x_172_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__21, &l_Lean_AttributeImplCore_ref___autoParam___closed__21_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21);
v___x_176_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__11));
v___x_177_ = lean_box(2);
v___x_178_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___x_176_);
lean_ctor_set(v___x_178_, 2, v___x_175_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__22, &l_Lean_AttributeImplCore_ref___autoParam___closed__22_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22);
v___x_180_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_181_ = lean_array_push(v___x_180_, v___x_179_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_182_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__23, &l_Lean_AttributeImplCore_ref___autoParam___closed__23_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23);
v___x_183_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__9));
v___x_184_ = lean_box(2);
v___x_185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_183_);
lean_ctor_set(v___x_185_, 2, v___x_182_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__24, &l_Lean_AttributeImplCore_ref___autoParam___closed__24_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24);
v___x_187_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_188_ = lean_array_push(v___x_187_, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_189_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__25, &l_Lean_AttributeImplCore_ref___autoParam___closed__25_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25);
v___x_190_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__7));
v___x_191_ = lean_box(2);
v___x_192_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_190_);
lean_ctor_set(v___x_192_, 2, v___x_189_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__26, &l_Lean_AttributeImplCore_ref___autoParam___closed__26_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26);
v___x_194_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_195_ = lean_array_push(v___x_194_, v___x_193_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_196_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__27, &l_Lean_AttributeImplCore_ref___autoParam___closed__27_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27);
v___x_197_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__4));
v___x_198_ = lean_box(2);
v___x_199_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_197_);
lean_ctor_set(v___x_199_, 2, v___x_196_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam(void){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_200_;
}
}
lean_object* l_Lean_AttributeKind_ctorIdx___impl(uint8_t v_x_215_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_box(v_x_215_);
v___x_217_ = lean_obj_tag_nat(v___x_216_);
lean_dec(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT void l_Lean_AttributeKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_215_ = stack[0].m_num;
lean_object* v_res_218_;
v_res_218_ = l_Lean_AttributeKind_ctorIdx___impl(v_x_215_);
stack->m_obj
 = v_res_218_;
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx___impl___boxed(lean_object* v_x_219_){
_start:
{
uint8_t v_x_4__boxed_220_; lean_object* v_res_221_; 
v_x_4__boxed_220_ = lean_unbox(v_x_219_);
v_res_221_ = l_Lean_AttributeKind_ctorIdx___impl(v_x_4__boxed_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg(lean_object* v_k_222_){
_start:
{
lean_inc(v_k_222_);
return v_k_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg___boxed(lean_object* v_k_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_AttributeKind_ctorElim___redArg(v_k_223_);
lean_dec(v_k_223_);
return v_res_224_;
}
}
lean_object* l_Lean_AttributeKind_ctorElim(lean_object* v_motive_225_, lean_object* v_ctorIdx_226_, uint8_t v_t_227_, lean_object* v_h_228_, lean_object* v_k_229_){
_start:
{
lean_inc(v_k_229_);
return v_k_229_;
}
}
LEAN_EXPORT void l_Lean_AttributeKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_226_ = stack[1].m_obj;
uint8_t v_t_227_ = stack[2].m_num;
lean_object* v_k_229_ = stack[4].m_obj;
lean_object* v_res_230_;
v_res_230_ = l_Lean_AttributeKind_ctorElim(lean_box(0), v_ctorIdx_226_, v_t_227_, lean_box(0), v_k_229_);
stack->m_obj
 = v_res_230_;
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___boxed(lean_object* v_motive_231_, lean_object* v_ctorIdx_232_, lean_object* v_t_233_, lean_object* v_h_234_, lean_object* v_k_235_){
_start:
{
uint8_t v_t_boxed_236_; lean_object* v_res_237_; 
v_t_boxed_236_ = lean_unbox(v_t_233_);
v_res_237_ = l_Lean_AttributeKind_ctorElim(v_motive_231_, v_ctorIdx_232_, v_t_boxed_236_, v_h_234_, v_k_235_);
lean_dec(v_k_235_);
lean_dec(v_ctorIdx_232_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg(lean_object* v_global_238_){
_start:
{
lean_inc(v_global_238_);
return v_global_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg___boxed(lean_object* v_global_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_AttributeKind_global_elim___redArg(v_global_239_);
lean_dec(v_global_239_);
return v_res_240_;
}
}
lean_object* l_Lean_AttributeKind_global_elim(lean_object* v_motive_241_, uint8_t v_t_242_, lean_object* v_h_243_, lean_object* v_global_244_){
_start:
{
lean_inc(v_global_244_);
return v_global_244_;
}
}
LEAN_EXPORT void l_Lean_AttributeKind_global_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_242_ = stack[1].m_num;
lean_object* v_global_244_ = stack[3].m_obj;
lean_object* v_res_245_;
v_res_245_ = l_Lean_AttributeKind_global_elim(lean_box(0), v_t_242_, lean_box(0), v_global_244_);
stack->m_obj
 = v_res_245_;
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___boxed(lean_object* v_motive_246_, lean_object* v_t_247_, lean_object* v_h_248_, lean_object* v_global_249_){
_start:
{
uint8_t v_t_boxed_250_; lean_object* v_res_251_; 
v_t_boxed_250_ = lean_unbox(v_t_247_);
v_res_251_ = l_Lean_AttributeKind_global_elim(v_motive_246_, v_t_boxed_250_, v_h_248_, v_global_249_);
lean_dec(v_global_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg(lean_object* v_local_252_){
_start:
{
lean_inc(v_local_252_);
return v_local_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg___boxed(lean_object* v_local_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_AttributeKind_local_elim___redArg(v_local_253_);
lean_dec(v_local_253_);
return v_res_254_;
}
}
lean_object* l_Lean_AttributeKind_local_elim(lean_object* v_motive_255_, uint8_t v_t_256_, lean_object* v_h_257_, lean_object* v_local_258_){
_start:
{
lean_inc(v_local_258_);
return v_local_258_;
}
}
LEAN_EXPORT void l_Lean_AttributeKind_local_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_256_ = stack[1].m_num;
lean_object* v_local_258_ = stack[3].m_obj;
lean_object* v_res_259_;
v_res_259_ = l_Lean_AttributeKind_local_elim(lean_box(0), v_t_256_, lean_box(0), v_local_258_);
stack->m_obj
 = v_res_259_;
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___boxed(lean_object* v_motive_260_, lean_object* v_t_261_, lean_object* v_h_262_, lean_object* v_local_263_){
_start:
{
uint8_t v_t_boxed_264_; lean_object* v_res_265_; 
v_t_boxed_264_ = lean_unbox(v_t_261_);
v_res_265_ = l_Lean_AttributeKind_local_elim(v_motive_260_, v_t_boxed_264_, v_h_262_, v_local_263_);
lean_dec(v_local_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg(lean_object* v_scoped_266_){
_start:
{
lean_inc(v_scoped_266_);
return v_scoped_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg___boxed(lean_object* v_scoped_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_AttributeKind_scoped_elim___redArg(v_scoped_267_);
lean_dec(v_scoped_267_);
return v_res_268_;
}
}
lean_object* l_Lean_AttributeKind_scoped_elim(lean_object* v_motive_269_, uint8_t v_t_270_, lean_object* v_h_271_, lean_object* v_scoped_272_){
_start:
{
lean_inc(v_scoped_272_);
return v_scoped_272_;
}
}
LEAN_EXPORT void l_Lean_AttributeKind_scoped_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_270_ = stack[1].m_num;
lean_object* v_scoped_272_ = stack[3].m_obj;
lean_object* v_res_273_;
v_res_273_ = l_Lean_AttributeKind_scoped_elim(lean_box(0), v_t_270_, lean_box(0), v_scoped_272_);
stack->m_obj
 = v_res_273_;
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___boxed(lean_object* v_motive_274_, lean_object* v_t_275_, lean_object* v_h_276_, lean_object* v_scoped_277_){
_start:
{
uint8_t v_t_boxed_278_; lean_object* v_res_279_; 
v_t_boxed_278_ = lean_unbox(v_t_275_);
v_res_279_ = l_Lean_AttributeKind_scoped_elim(v_motive_274_, v_t_boxed_278_, v_h_276_, v_scoped_277_);
lean_dec(v_scoped_277_);
return v_res_279_;
}
}
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t v_x_280_, uint8_t v_y_281_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_282_ = lean_box(v_x_280_);
v___x_283_ = lean_obj_tag_nat(v___x_282_);
lean_dec(v___x_282_);
v___x_284_ = lean_box(v_y_281_);
v___x_285_ = lean_obj_tag_nat(v___x_284_);
lean_dec(v___x_284_);
v___x_286_ = lean_nat_dec_eq(v___x_283_, v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT void l_Lean_instBEqAttributeKind_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_280_ = stack[0].m_num;
uint8_t v_y_281_ = stack[1].m_num;
uint8_t v_res_287_;
v_res_287_ = l_Lean_instBEqAttributeKind_beq(v_x_280_, v_y_281_);
stack->m_num = v_res_287_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeKind_beq___boxed(lean_object* v_x_288_, lean_object* v_y_289_){
_start:
{
uint8_t v_x_24__boxed_290_; uint8_t v_y_25__boxed_291_; uint8_t v_res_292_; lean_object* v_r_293_; 
v_x_24__boxed_290_ = lean_unbox(v_x_288_);
v_y_25__boxed_291_ = lean_unbox(v_y_289_);
v_res_292_ = l_Lean_instBEqAttributeKind_beq(v_x_24__boxed_290_, v_y_25__boxed_291_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind_default(void){
_start:
{
uint8_t v___x_296_; 
v___x_296_ = 0;
return v___x_296_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind(void){
_start:
{
uint8_t v___x_297_; 
v___x_297_ = 0;
return v___x_297_;
}
}
lean_object* l_Lean_instToStringAttributeKind___lam__0(uint8_t v_x_301_){
_start:
{
switch(v_x_301_)
{
case 0:
{
lean_object* v___x_302_; 
v___x_302_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
return v___x_302_;
}
case 1:
{
lean_object* v___x_303_; 
v___x_303_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
return v___x_303_;
}
default: 
{
lean_object* v___x_304_; 
v___x_304_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
return v___x_304_;
}
}
}
}
LEAN_EXPORT void l_Lean_instToStringAttributeKind___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_301_ = stack[0].m_num;
lean_object* v_res_305_;
v_res_305_ = l_Lean_instToStringAttributeKind___lam__0(v_x_301_);
stack->m_obj
 = v_res_305_;
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0___boxed(lean_object* v_x_306_){
_start:
{
uint8_t v_x_36__boxed_307_; lean_object* v_res_308_; 
v_x_36__boxed_307_ = lean_unbox(v_x_306_);
v_res_308_ = l_Lean_instToStringAttributeKind___lam__0(v_x_36__boxed_307_);
return v_res_308_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = l_Lean_instInhabitedMessageData_default;
v___x_312_ = lean_box(0);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
return v___x_313_;
}
}
lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0(lean_object* v_x_314_, lean_object* v___y_315_, uint8_t v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0, &l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0);
v___x_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedAttributeImpl_default___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_314_ = stack[0].m_obj;
lean_object* v___y_315_ = stack[1].m_obj;
uint8_t v___y_316_ = stack[2].m_num;
lean_object* v___y_317_ = stack[3].m_obj;
lean_object* v___y_318_ = stack[4].m_obj;
lean_object* v_res_322_;
v_res_322_ = l_Lean_instInhabitedAttributeImpl_default___lam__0(v_x_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
stack->m_obj
 = v_res_322_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed(lean_object* v_x_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
uint8_t v___y_1034__boxed_329_; lean_object* v_res_330_; 
v___y_1034__boxed_329_ = lean_unbox(v___y_325_);
v_res_330_ = l_Lean_instInhabitedAttributeImpl_default___lam__0(v_x_323_, v___y_324_, v___y_1034__boxed_329_, v___y_326_, v___y_327_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_324_);
lean_dec(v_x_323_);
return v_res_330_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_331_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_334_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_335_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
lean_ctor_set(v___x_337_, 2, v___x_336_);
lean_ctor_set(v___x_337_, 3, v___x_336_);
lean_ctor_set(v___x_337_, 4, v___x_335_);
lean_ctor_set(v___x_337_, 5, v___x_335_);
lean_ctor_set(v___x_337_, 6, v___x_335_);
lean_ctor_set(v___x_337_, 7, v___x_335_);
lean_ctor_set(v___x_337_, 8, v___x_335_);
lean_ctor_set(v___x_337_, 9, v___x_335_);
lean_ctor_set(v___x_337_, 10, v___x_335_);
lean_ctor_set(v___x_337_, 11, v___x_334_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = lean_unsigned_to_nat(32u);
v___x_339_ = lean_mk_empty_array_with_capacity(v___x_338_);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_341_ = ((size_t)5ULL);
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = lean_unsigned_to_nat(32u);
v___x_344_ = lean_mk_empty_array_with_capacity(v___x_343_);
v___x_345_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3);
v___x_346_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
lean_ctor_set(v___x_346_, 2, v___x_342_);
lean_ctor_set(v___x_346_, 3, v___x_342_);
lean_ctor_set_usize(v___x_346_, 4, v___x_341_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_347_ = lean_box(1);
v___x_348_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4);
v___x_349_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_348_);
lean_ctor_set(v___x_350_, 2, v___x_347_);
return v___x_350_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(lean_object* v_msgData_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; lean_object* v_toCold_356_; lean_object* v_env_357_; lean_object* v_options_358_; uint8_t v___x_359_; lean_object* v_env_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_355_ = lean_st_ref_get(v___y_353_);
v_toCold_356_ = lean_ctor_get(v___y_352_, 0);
v_env_357_ = lean_ctor_get(v___x_355_, 0);
lean_inc_ref(v_env_357_);
lean_dec(v___x_355_);
v_options_358_ = lean_ctor_get(v_toCold_356_, 2);
v___x_359_ = 0;
v_env_360_ = l_Lean_Environment_setRecordingDeps(v_env_357_, v___x_359_);
v___x_361_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2);
v___x_362_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_358_);
v___x_363_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_363_, 0, v_env_360_);
lean_ctor_set(v___x_363_, 1, v___x_361_);
lean_ctor_set(v___x_363_, 2, v___x_362_);
lean_ctor_set(v___x_363_, 3, v_options_358_);
v___x_364_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v_msgData_351_);
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_351_ = stack[0].m_obj;
lean_object* v___y_352_ = stack[1].m_obj;
lean_object* v___y_353_ = stack[2].m_obj;
lean_object* v_res_366_;
v_res_366_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msgData_351_, v___y_352_, v___y_353_);
stack->m_obj
 = v_res_366_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___boxed(lean_object* v_msgData_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msgData_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_371_;
}
}
lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(lean_object* v_msg_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_ref_376_; lean_object* v___x_377_; lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_386_; 
v_ref_376_ = lean_ctor_get(v___y_373_, 2);
v___x_377_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msg_372_, v___y_373_, v___y_374_);
v_a_378_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_386_ == 0)
{
v___x_380_ = v___x_377_;
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; lean_object* v___x_384_; 
lean_inc(v_ref_376_);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v_ref_376_);
lean_ctor_set(v___x_382_, 1, v_a_378_);
if (v_isShared_381_ == 0)
{
lean_ctor_set_tag(v___x_380_, 1);
lean_ctor_set(v___x_380_, 0, v___x_382_);
v___x_384_ = v___x_380_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_372_ = stack[0].m_obj;
lean_object* v___y_373_ = stack[1].m_obj;
lean_object* v___y_374_ = stack[2].m_obj;
lean_object* v_res_387_;
v_res_387_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_372_, v___y_373_, v___y_374_);
stack->m_obj
 = v_res_387_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg___boxed(lean_object* v_msg_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
return v_res_392_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0));
v___x_395_ = l_Lean_stringToMessageData(v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2));
v___x_398_ = l_Lean_stringToMessageData(v___x_397_);
return v___x_398_;
}
}
lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1(lean_object* v___x_399_, lean_object* v_decl_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_name_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v_name_404_ = lean_ctor_get(v___x_399_, 1);
lean_inc(v_name_404_);
lean_dec_ref(v___x_399_);
v___x_405_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_406_ = l_Lean_MessageData_ofName(v_name_404_);
v___x_407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_409_, v___y_401_, v___y_402_);
return v___x_410_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedAttributeImpl_default___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_399_ = stack[0].m_obj;
lean_object* v_decl_400_ = stack[1].m_obj;
lean_object* v___y_401_ = stack[2].m_obj;
lean_object* v___y_402_ = stack[3].m_obj;
lean_object* v_res_411_;
v_res_411_ = l_Lean_instInhabitedAttributeImpl_default___lam__1(v___x_399_, v_decl_400_, v___y_401_, v___y_402_);
stack->m_obj
 = v_res_411_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed(lean_object* v___x_412_, lean_object* v_decl_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_instInhabitedAttributeImpl_default___lam__1(v___x_412_, v_decl_413_, v___y_414_, v___y_415_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v_decl_413_);
return v_res_417_;
}
}
lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(lean_object* v_00_u03b1_426_, lean_object* v_msg_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_427_, v___y_428_, v___y_429_);
return v___x_431_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_427_ = stack[1].m_obj;
lean_object* v___y_428_ = stack[2].m_obj;
lean_object* v___y_429_ = stack[3].m_obj;
lean_object* v_res_432_;
v_res_432_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(lean_box(0), v_msg_427_, v___y_428_, v___y_429_);
stack->m_obj
 = v_res_432_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___boxed(lean_object* v_00_u03b1_433_, lean_object* v_msg_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(v_00_u03b1_433_, v_msg_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
return v_res_438_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_box(0);
v___x_441_ = lean_unsigned_to_nat(16u);
v___x_442_ = lean_mk_array(v___x_441_, v___x_440_);
return v___x_442_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v___x_443_);
return v___x_445_;
}
}
lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_448_ = lean_st_mk_ref(v___x_447_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT void l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_450_;
v_res_450_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
stack->m_obj
 = v_res_450_;
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
return v_res_452_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object* v_a_453_, lean_object* v_x_454_){
_start:
{
if (lean_obj_tag(v_x_454_) == 0)
{
uint8_t v___x_455_; 
v___x_455_ = 0;
return v___x_455_;
}
else
{
lean_object* v_key_456_; lean_object* v_tail_457_; uint8_t v___x_458_; 
v_key_456_ = lean_ctor_get(v_x_454_, 0);
v_tail_457_ = lean_ctor_get(v_x_454_, 2);
v___x_458_ = lean_name_eq(v_key_456_, v_a_453_);
if (v___x_458_ == 0)
{
v_x_454_ = v_tail_457_;
goto _start;
}
else
{
return v___x_458_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_453_ = stack[0].m_obj;
lean_object* v_x_454_ = stack[1].m_obj;
uint8_t v_res_460_;
v_res_460_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_453_, v_x_454_);
stack->m_num = v_res_460_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg___boxed(lean_object* v_a_461_, lean_object* v_x_462_){
_start:
{
uint8_t v_res_463_; lean_object* v_r_464_; 
v_res_463_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_461_, v_x_462_);
lean_dec(v_x_462_);
lean_dec(v_a_461_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(lean_object* v_m_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_buckets_467_; lean_object* v___x_468_; uint64_t v___y_470_; 
v_buckets_467_ = lean_ctor_get(v_m_465_, 1);
v___x_468_ = lean_array_get_size(v_buckets_467_);
if (lean_obj_tag(v_a_466_) == 0)
{
uint64_t v___x_484_; 
v___x_484_ = 1723ULL;
v___y_470_ = v___x_484_;
goto v___jp_469_;
}
else
{
uint64_t v_hash_485_; 
v_hash_485_ = lean_ctor_get_uint64(v_a_466_, sizeof(void*)*2);
v___y_470_ = v_hash_485_;
goto v___jp_469_;
}
v___jp_469_:
{
uint64_t v___x_471_; uint64_t v___x_472_; uint64_t v_fold_473_; uint64_t v___x_474_; uint64_t v___x_475_; uint64_t v___x_476_; size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_471_ = 32ULL;
v___x_472_ = lean_uint64_shift_right(v___y_470_, v___x_471_);
v_fold_473_ = lean_uint64_xor(v___y_470_, v___x_472_);
v___x_474_ = 16ULL;
v___x_475_ = lean_uint64_shift_right(v_fold_473_, v___x_474_);
v___x_476_ = lean_uint64_xor(v_fold_473_, v___x_475_);
v___x_477_ = lean_uint64_to_usize(v___x_476_);
v___x_478_ = lean_usize_of_nat(v___x_468_);
v___x_479_ = ((size_t)1ULL);
v___x_480_ = lean_usize_sub(v___x_478_, v___x_479_);
v___x_481_ = lean_usize_land(v___x_477_, v___x_480_);
v___x_482_ = lean_array_uget_borrowed(v_buckets_467_, v___x_481_);
v___x_483_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_466_, v___x_482_);
return v___x_483_;
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_465_ = stack[0].m_obj;
lean_object* v_a_466_ = stack[1].m_obj;
uint8_t v_res_486_;
v_res_486_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_465_, v_a_466_);
stack->m_num = v_res_486_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___boxed(lean_object* v_m_487_, lean_object* v_a_488_){
_start:
{
uint8_t v_res_489_; lean_object* v_r_490_; 
v_res_489_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec_ref(v_m_487_);
v_r_490_ = lean_box(v_res_489_);
return v_r_490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(lean_object* v_a_491_, lean_object* v_b_492_, lean_object* v_x_493_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
lean_dec(v_b_492_);
lean_dec(v_a_491_);
return v_x_493_;
}
else
{
lean_object* v_key_494_; lean_object* v_value_495_; lean_object* v_tail_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_508_; 
v_key_494_ = lean_ctor_get(v_x_493_, 0);
v_value_495_ = lean_ctor_get(v_x_493_, 1);
v_tail_496_ = lean_ctor_get(v_x_493_, 2);
v_isSharedCheck_508_ = !lean_is_exclusive(v_x_493_);
if (v_isSharedCheck_508_ == 0)
{
v___x_498_ = v_x_493_;
v_isShared_499_ = v_isSharedCheck_508_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_tail_496_);
lean_inc(v_value_495_);
lean_inc(v_key_494_);
lean_dec(v_x_493_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_508_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
uint8_t v___x_500_; 
v___x_500_ = lean_name_eq(v_key_494_, v_a_491_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_501_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_491_, v_b_492_, v_tail_496_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 2, v___x_501_);
v___x_503_ = v___x_498_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_key_494_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_value_495_);
lean_ctor_set(v_reuseFailAlloc_504_, 2, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
else
{
lean_object* v___x_506_; 
lean_dec(v_value_495_);
lean_dec(v_key_494_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 1, v_b_492_);
lean_ctor_set(v___x_498_, 0, v_a_491_);
v___x_506_ = v___x_498_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_491_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_b_492_);
lean_ctor_set(v_reuseFailAlloc_507_, 2, v_tail_496_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
if (lean_obj_tag(v_x_510_) == 0)
{
return v_x_509_;
}
else
{
lean_object* v_key_511_; lean_object* v_value_512_; lean_object* v_tail_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_539_; 
v_key_511_ = lean_ctor_get(v_x_510_, 0);
v_value_512_ = lean_ctor_get(v_x_510_, 1);
v_tail_513_ = lean_ctor_get(v_x_510_, 2);
v_isSharedCheck_539_ = !lean_is_exclusive(v_x_510_);
if (v_isSharedCheck_539_ == 0)
{
v___x_515_ = v_x_510_;
v_isShared_516_ = v_isSharedCheck_539_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_tail_513_);
lean_inc(v_value_512_);
lean_inc(v_key_511_);
lean_dec(v_x_510_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_539_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; uint64_t v___y_519_; 
v___x_517_ = lean_array_get_size(v_x_509_);
if (lean_obj_tag(v_key_511_) == 0)
{
uint64_t v___x_537_; 
v___x_537_ = 1723ULL;
v___y_519_ = v___x_537_;
goto v___jp_518_;
}
else
{
uint64_t v_hash_538_; 
v_hash_538_ = lean_ctor_get_uint64(v_key_511_, sizeof(void*)*2);
v___y_519_ = v_hash_538_;
goto v___jp_518_;
}
v___jp_518_:
{
uint64_t v___x_520_; uint64_t v___x_521_; uint64_t v_fold_522_; uint64_t v___x_523_; uint64_t v___x_524_; uint64_t v___x_525_; size_t v___x_526_; size_t v___x_527_; size_t v___x_528_; size_t v___x_529_; size_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_520_ = 32ULL;
v___x_521_ = lean_uint64_shift_right(v___y_519_, v___x_520_);
v_fold_522_ = lean_uint64_xor(v___y_519_, v___x_521_);
v___x_523_ = 16ULL;
v___x_524_ = lean_uint64_shift_right(v_fold_522_, v___x_523_);
v___x_525_ = lean_uint64_xor(v_fold_522_, v___x_524_);
v___x_526_ = lean_uint64_to_usize(v___x_525_);
v___x_527_ = lean_usize_of_nat(v___x_517_);
v___x_528_ = ((size_t)1ULL);
v___x_529_ = lean_usize_sub(v___x_527_, v___x_528_);
v___x_530_ = lean_usize_land(v___x_526_, v___x_529_);
v___x_531_ = lean_array_uget_borrowed(v_x_509_, v___x_530_);
lean_inc(v___x_531_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 2, v___x_531_);
v___x_533_ = v___x_515_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_key_511_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_value_512_);
lean_ctor_set(v_reuseFailAlloc_536_, 2, v___x_531_);
v___x_533_ = v_reuseFailAlloc_536_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; 
v___x_534_ = lean_array_uset(v_x_509_, v___x_530_, v___x_533_);
v_x_509_ = v___x_534_;
v_x_510_ = v_tail_513_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(lean_object* v_i_540_, lean_object* v_source_541_, lean_object* v_target_542_){
_start:
{
lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_543_ = lean_array_get_size(v_source_541_);
v___x_544_ = lean_nat_dec_lt(v_i_540_, v___x_543_);
if (v___x_544_ == 0)
{
lean_dec_ref(v_source_541_);
lean_dec(v_i_540_);
return v_target_542_;
}
else
{
lean_object* v_es_545_; lean_object* v___x_546_; lean_object* v_source_547_; lean_object* v_target_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v_es_545_ = lean_array_fget(v_source_541_, v_i_540_);
v___x_546_ = lean_box(0);
v_source_547_ = lean_array_fset(v_source_541_, v_i_540_, v___x_546_);
v_target_548_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_target_542_, v_es_545_);
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = lean_nat_add(v_i_540_, v___x_549_);
lean_dec(v_i_540_);
v_i_540_ = v___x_550_;
v_source_541_ = v_source_547_;
v_target_542_ = v_target_548_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(lean_object* v_data_552_){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v_nbuckets_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_553_ = lean_array_get_size(v_data_552_);
v___x_554_ = lean_unsigned_to_nat(2u);
v_nbuckets_555_ = lean_nat_mul(v___x_553_, v___x_554_);
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = lean_box(0);
v___x_558_ = lean_mk_array(v_nbuckets_555_, v___x_557_);
v___x_559_ = lean_array_propagate_mark(v_data_552_, v___x_558_);
v___x_560_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v___x_556_, v_data_552_, v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(lean_object* v_m_561_, lean_object* v_a_562_, lean_object* v_b_563_){
_start:
{
lean_object* v_size_564_; lean_object* v_buckets_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_611_; 
v_size_564_ = lean_ctor_get(v_m_561_, 0);
v_buckets_565_ = lean_ctor_get(v_m_561_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_m_561_);
if (v_isSharedCheck_611_ == 0)
{
v___x_567_ = v_m_561_;
v_isShared_568_ = v_isSharedCheck_611_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_buckets_565_);
lean_inc(v_size_564_);
lean_dec(v_m_561_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_611_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; uint64_t v___y_571_; 
v___x_569_ = lean_array_get_size(v_buckets_565_);
if (lean_obj_tag(v_a_562_) == 0)
{
uint64_t v___x_609_; 
v___x_609_ = 1723ULL;
v___y_571_ = v___x_609_;
goto v___jp_570_;
}
else
{
uint64_t v_hash_610_; 
v_hash_610_ = lean_ctor_get_uint64(v_a_562_, sizeof(void*)*2);
v___y_571_ = v_hash_610_;
goto v___jp_570_;
}
v___jp_570_:
{
uint64_t v___x_572_; uint64_t v___x_573_; uint64_t v_fold_574_; uint64_t v___x_575_; uint64_t v___x_576_; uint64_t v___x_577_; size_t v___x_578_; size_t v___x_579_; size_t v___x_580_; size_t v___x_581_; size_t v___x_582_; lean_object* v_bkt_583_; uint8_t v___x_584_; 
v___x_572_ = 32ULL;
v___x_573_ = lean_uint64_shift_right(v___y_571_, v___x_572_);
v_fold_574_ = lean_uint64_xor(v___y_571_, v___x_573_);
v___x_575_ = 16ULL;
v___x_576_ = lean_uint64_shift_right(v_fold_574_, v___x_575_);
v___x_577_ = lean_uint64_xor(v_fold_574_, v___x_576_);
v___x_578_ = lean_uint64_to_usize(v___x_577_);
v___x_579_ = lean_usize_of_nat(v___x_569_);
v___x_580_ = ((size_t)1ULL);
v___x_581_ = lean_usize_sub(v___x_579_, v___x_580_);
v___x_582_ = lean_usize_land(v___x_578_, v___x_581_);
v_bkt_583_ = lean_array_uget_borrowed(v_buckets_565_, v___x_582_);
v___x_584_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_562_, v_bkt_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v_size_x27_586_; lean_object* v___x_587_; lean_object* v_buckets_x27_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_585_ = lean_unsigned_to_nat(1u);
v_size_x27_586_ = lean_nat_add(v_size_564_, v___x_585_);
lean_dec(v_size_564_);
lean_inc(v_bkt_583_);
v___x_587_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_587_, 0, v_a_562_);
lean_ctor_set(v___x_587_, 1, v_b_563_);
lean_ctor_set(v___x_587_, 2, v_bkt_583_);
v_buckets_x27_588_ = lean_array_uset(v_buckets_565_, v___x_582_, v___x_587_);
v___x_589_ = lean_unsigned_to_nat(4u);
v___x_590_ = lean_nat_mul(v_size_x27_586_, v___x_589_);
v___x_591_ = lean_unsigned_to_nat(3u);
v___x_592_ = lean_nat_div(v___x_590_, v___x_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_array_get_size(v_buckets_x27_588_);
v___x_594_ = lean_nat_dec_le(v___x_592_, v___x_593_);
lean_dec(v___x_592_);
if (v___x_594_ == 0)
{
lean_object* v_val_595_; lean_object* v___x_597_; 
v_val_595_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_buckets_x27_588_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v_val_595_);
lean_ctor_set(v___x_567_, 0, v_size_x27_586_);
v___x_597_ = v___x_567_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_size_x27_586_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_val_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
else
{
lean_object* v___x_600_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v_buckets_x27_588_);
lean_ctor_set(v___x_567_, 0, v_size_x27_586_);
v___x_600_ = v___x_567_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_size_x27_586_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_buckets_x27_588_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
else
{
lean_object* v___x_602_; lean_object* v_buckets_x27_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
lean_inc(v_bkt_583_);
v___x_602_ = lean_box(0);
v_buckets_x27_603_ = lean_array_uset(v_buckets_565_, v___x_582_, v___x_602_);
v___x_604_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_562_, v_b_563_, v_bkt_583_);
v___x_605_ = lean_array_uset(v_buckets_x27_603_, v___x_582_, v___x_604_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v___x_605_);
v___x_607_ = v___x_567_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_size_564_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_registerBuiltinAttribute___closed__1(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__0));
v___x_614_ = lean_mk_io_user_error(v___x_613_);
return v___x_614_;
}
}
lean_object* l_Lean_registerBuiltinAttribute(lean_object* v_attr_617_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v_toAttributeImplCore_621_; lean_object* v_name_622_; uint8_t v___x_623_; 
v___x_619_ = l_Lean_attributeMapRef;
v___x_620_ = lean_st_ref_get(v___x_619_);
v_toAttributeImplCore_621_ = lean_ctor_get(v_attr_617_, 0);
v_name_622_ = lean_ctor_get(v_toAttributeImplCore_621_, 1);
lean_inc(v_name_622_);
v___x_623_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_620_, v_name_622_);
lean_dec(v___x_620_);
if (v___x_623_ == 0)
{
uint8_t v___x_624_; 
v___x_624_ = l_Lean_initializing();
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v_name_622_);
lean_dec_ref(v_attr_617_);
v___x_625_ = lean_obj_once(&l_Lean_registerBuiltinAttribute___closed__1, &l_Lean_registerBuiltinAttribute___closed__1_once, _init_l_Lean_registerBuiltinAttribute___closed__1);
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_627_ = lean_st_ref_take(v___x_619_);
v___x_628_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_627_, v_name_622_, v_attr_617_);
v___x_629_ = lean_st_ref_put(v___x_619_, v___x_628_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
lean_dec_ref(v_attr_617_);
v___x_631_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_632_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_622_, v___x_623_);
v___x_633_ = lean_string_append(v___x_631_, v___x_632_);
lean_dec_ref(v___x_632_);
v___x_634_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_635_ = lean_string_append(v___x_633_, v___x_634_);
v___x_636_ = lean_mk_io_user_error(v___x_635_);
v___x_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
return v___x_637_;
}
}
}
LEAN_EXPORT void l_Lean_registerBuiltinAttribute_0interp(lean_interpreter_value* stack)
{
lean_object* v_attr_617_ = stack[0].m_obj;
lean_object* v_res_638_;
v_res_638_ = l_Lean_registerBuiltinAttribute(v_attr_617_);
stack->m_obj
 = v_res_638_;
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute___boxed(lean_object* v_attr_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_registerBuiltinAttribute(v_attr_639_);
return v_res_641_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(lean_object* v_00_u03b2_642_, lean_object* v_m_643_, lean_object* v_a_644_){
_start:
{
uint8_t v___x_645_; 
v___x_645_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_643_, v_a_644_);
return v___x_645_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_643_ = stack[1].m_obj;
lean_object* v_a_644_ = stack[2].m_obj;
uint8_t v_res_646_;
v_res_646_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(lean_box(0), v_m_643_, v_a_644_);
stack->m_num = v_res_646_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___boxed(lean_object* v_00_u03b2_647_, lean_object* v_m_648_, lean_object* v_a_649_){
_start:
{
uint8_t v_res_650_; lean_object* v_r_651_; 
v_res_650_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(v_00_u03b2_647_, v_m_648_, v_a_649_);
lean_dec(v_a_649_);
lean_dec_ref(v_m_648_);
v_r_651_ = lean_box(v_res_650_);
return v_r_651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1(lean_object* v_00_u03b2_652_, lean_object* v_m_653_, lean_object* v_a_654_, lean_object* v_b_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_m_653_, v_a_654_, v_b_655_);
return v___x_656_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_object* v_00_u03b2_657_, lean_object* v_a_658_, lean_object* v_x_659_){
_start:
{
uint8_t v___x_660_; 
v___x_660_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_658_, v_x_659_);
return v___x_660_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_658_ = stack[1].m_obj;
lean_object* v_x_659_ = stack[2].m_obj;
uint8_t v_res_661_;
v_res_661_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_box(0), v_a_658_, v_x_659_);
stack->m_num = v_res_661_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___boxed(lean_object* v_00_u03b2_662_, lean_object* v_a_663_, lean_object* v_x_664_){
_start:
{
uint8_t v_res_665_; lean_object* v_r_666_; 
v_res_665_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(v_00_u03b2_662_, v_a_663_, v_x_664_);
lean_dec(v_x_664_);
lean_dec(v_a_663_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(lean_object* v_00_u03b2_667_, lean_object* v_data_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_data_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3(lean_object* v_00_u03b2_670_, lean_object* v_a_671_, lean_object* v_b_672_, lean_object* v_x_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_671_, v_b_672_, v_x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_675_, lean_object* v_i_676_, lean_object* v_source_677_, lean_object* v_target_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v_i_676_, v_source_677_, v_target_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_680_, lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_x_681_, v_x_682_);
return v___x_683_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object* v_ref_684_, lean_object* v_msg_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_toCold_689_; lean_object* v_currRecDepth_690_; lean_object* v_ref_691_; uint16_t v_optionFlags_692_; uint8_t v_suppressElabErrors_693_; uint8_t v_isRecordingDeps_694_; lean_object* v_ref_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_toCold_689_ = lean_ctor_get(v___y_686_, 0);
v_currRecDepth_690_ = lean_ctor_get(v___y_686_, 1);
v_ref_691_ = lean_ctor_get(v___y_686_, 2);
v_optionFlags_692_ = lean_ctor_get_uint16(v___y_686_, sizeof(void*)*3);
v_suppressElabErrors_693_ = lean_ctor_get_uint8(v___y_686_, sizeof(void*)*3 + 2);
v_isRecordingDeps_694_ = lean_ctor_get_uint8(v___y_686_, sizeof(void*)*3 + 3);
v_ref_695_ = l_Lean_replaceRef(v_ref_684_, v_ref_691_);
lean_inc(v_currRecDepth_690_);
lean_inc_ref(v_toCold_689_);
v___x_696_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_696_, 0, v_toCold_689_);
lean_ctor_set(v___x_696_, 1, v_currRecDepth_690_);
lean_ctor_set(v___x_696_, 2, v_ref_695_);
lean_ctor_set_uint16(v___x_696_, sizeof(void*)*3, v_optionFlags_692_);
lean_ctor_set_uint8(v___x_696_, sizeof(void*)*3 + 2, v_suppressElabErrors_693_);
lean_ctor_set_uint8(v___x_696_, sizeof(void*)*3 + 3, v_isRecordingDeps_694_);
v___x_697_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_685_, v___x_696_, v___y_687_);
lean_dec_ref_known(v___x_696_, 3);
return v___x_697_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_684_ = stack[0].m_obj;
lean_object* v_msg_685_ = stack[1].m_obj;
lean_object* v___y_686_ = stack[2].m_obj;
lean_object* v___y_687_ = stack[3].m_obj;
lean_object* v_res_698_;
v_res_698_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_684_, v_msg_685_, v___y_686_, v___y_687_);
stack->m_obj
 = v_res_698_;
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
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object* v_stx_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v___x_725_; uint8_t v___y_736_; lean_object* v___x_742_; uint8_t v___x_743_; 
lean_inc(v_stx_721_);
v___x_725_ = l_Lean_Syntax_getKind(v_stx_721_);
v___x_742_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_743_ = lean_name_eq(v___x_725_, v___x_742_);
if (v___x_743_ == 0)
{
v___y_736_ = v___x_743_;
goto v___jp_735_;
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_744_ = lean_unsigned_to_nat(1u);
v___x_745_ = l_Lean_Syntax_getArg(v_stx_721_, v___x_744_);
v___x_746_ = l_Lean_Syntax_isNone(v___x_745_);
lean_dec(v___x_745_);
v___y_736_ = v___x_746_;
goto v___jp_735_;
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
v___jp_735_:
{
if (v___y_736_ == 0)
{
goto v___jp_726_;
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_737_ = lean_unsigned_to_nat(2u);
v___x_738_ = l_Lean_Syntax_getArg(v_stx_721_, v___x_737_);
v___x_739_ = l_Lean_Syntax_isNone(v___x_738_);
lean_dec(v___x_738_);
if (v___x_739_ == 0)
{
goto v___jp_726_;
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec(v___x_725_);
lean_dec(v_stx_721_);
v___x_740_ = lean_box(0);
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
return v___x_741_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Attribute_Builtin_ensureNoArgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_721_ = stack[0].m_obj;
lean_object* v_a_722_ = stack[1].m_obj;
lean_object* v_a_723_ = stack[2].m_obj;
lean_object* v_res_747_;
v_res_747_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_721_, v_a_722_, v_a_723_);
stack->m_obj
 = v_res_747_;
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object* v_stx_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_748_, v_a_749_, v_a_750_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
return v_res_752_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object* v_00_u03b1_753_, lean_object* v_ref_754_, lean_object* v_msg_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_754_, v_msg_755_, v___y_756_, v___y_757_);
return v___x_759_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_754_ = stack[1].m_obj;
lean_object* v_msg_755_ = stack[2].m_obj;
lean_object* v___y_756_ = stack[3].m_obj;
lean_object* v___y_757_ = stack[4].m_obj;
lean_object* v_res_760_;
v_res_760_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_box(0), v_ref_754_, v_msg_755_, v___y_756_, v___y_757_);
stack->m_obj
 = v_res_760_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object* v_00_u03b1_761_, lean_object* v_ref_762_, lean_object* v_msg_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(v_00_u03b1_761_, v_ref_762_, v_msg_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v_ref_762_);
return v_res_767_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__4));
v___x_782_ = l_Lean_stringToMessageData(v___x_781_);
return v___x_782_;
}
}
lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object* v_stx_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
lean_inc(v_stx_783_);
v___x_795_ = l_Lean_Syntax_getKind(v_stx_783_);
v___x_796_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_797_ = lean_name_eq(v___x_795_, v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_798_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_799_ = lean_name_eq(v___x_795_, v___x_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_801_ = lean_name_eq(v___x_795_, v___x_800_);
lean_dec(v___x_795_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_803_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_783_, v___x_802_, v_a_784_, v_a_785_);
lean_dec(v_stx_783_);
return v___x_803_;
}
else
{
goto v___jp_787_;
}
}
else
{
lean_dec(v___x_795_);
goto v___jp_787_;
}
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
lean_dec(v___x_795_);
v___x_804_ = lean_unsigned_to_nat(1u);
v___x_805_ = l_Lean_Syntax_getArg(v_stx_783_, v___x_804_);
lean_dec(v_stx_783_);
v___x_806_ = l_Lean_Syntax_isNone(v___x_805_);
if (v___x_806_ == 0)
{
if (v___x_797_ == 0)
{
lean_dec(v___x_805_);
goto v___jp_792_;
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = l_Lean_Syntax_getArg(v___x_805_, v___x_807_);
lean_dec(v___x_805_);
v___x_809_ = l_Lean_Syntax_isIdent(v___x_808_);
if (v___x_809_ == 0)
{
lean_dec(v___x_808_);
goto v___jp_792_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_808_);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
return v___x_811_;
}
}
}
else
{
lean_dec(v___x_805_);
goto v___jp_792_;
}
}
v___jp_787_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_788_ = lean_unsigned_to_nat(1u);
v___x_789_ = l_Lean_Syntax_getArg(v_stx_783_, v___x_788_);
lean_dec(v_stx_783_);
v___x_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
v___jp_792_:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_box(0);
v___x_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
return v___x_794_;
}
}
}
LEAN_EXPORT void l_Lean_Attribute_Builtin_getIdent_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_783_ = stack[0].m_obj;
lean_object* v_a_784_ = stack[1].m_obj;
lean_object* v_a_785_ = stack[2].m_obj;
lean_object* v_res_812_;
v_res_812_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_783_, v_a_784_, v_a_785_);
stack->m_obj
 = v_res_812_;
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object* v_stx_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_813_, v_a_814_, v_a_815_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
return v_res_817_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent___closed__1(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent___closed__0));
v___x_820_ = l_Lean_stringToMessageData(v___x_819_);
return v___x_820_;
}
}
lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v___x_825_; 
lean_inc(v_stx_821_);
v___x_825_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_821_, v_a_822_, v_a_823_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_839_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_839_ == 0)
{
v___x_828_ = v___x_825_;
v_isShared_829_ = v_isSharedCheck_839_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_839_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
if (lean_obj_tag(v_a_826_) == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
lean_del_object(v___x_828_);
v___x_830_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent___closed__1, &l_Lean_Attribute_Builtin_getIdent___closed__1_once, _init_l_Lean_Attribute_Builtin_getIdent___closed__1);
lean_inc(v_stx_821_);
v___x_831_ = l_Lean_MessageData_ofSyntax(v_stx_821_);
v___x_832_ = l_Lean_indentD(v___x_831_);
v___x_833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_830_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_821_, v___x_833_, v_a_822_, v_a_823_);
lean_dec(v_stx_821_);
return v___x_834_;
}
else
{
lean_object* v_val_835_; lean_object* v___x_837_; 
lean_dec(v_stx_821_);
v_val_835_ = lean_ctor_get(v_a_826_, 0);
lean_inc(v_val_835_);
lean_dec_ref_known(v_a_826_, 1);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v_val_835_);
v___x_837_ = v___x_828_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_val_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec(v_stx_821_);
v_a_840_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_825_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_825_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Attribute_Builtin_getIdent_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_821_ = stack[0].m_obj;
lean_object* v_a_822_ = stack[1].m_obj;
lean_object* v_a_823_ = stack[2].m_obj;
lean_object* v_res_848_;
v_res_848_ = l_Lean_Attribute_Builtin_getIdent(v_stx_821_, v_a_822_, v_a_823_);
stack->m_obj
 = v_res_848_;
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_Attribute_Builtin_getIdent(v_stx_849_, v_a_850_, v_a_851_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
return v_res_853_;
}
}
lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_854_, v_a_855_, v_a_856_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_879_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_879_ == 0)
{
v___x_861_ = v___x_858_;
v_isShared_862_ = v_isSharedCheck_879_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_879_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
if (lean_obj_tag(v_a_859_) == 0)
{
lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_863_ = lean_box(0);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_863_);
v___x_865_ = v___x_861_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
else
{
lean_object* v_val_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_878_; 
v_val_867_ = lean_ctor_get(v_a_859_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v_a_859_);
if (v_isSharedCheck_878_ == 0)
{
v___x_869_ = v_a_859_;
v_isShared_870_ = v_isSharedCheck_878_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_val_867_);
lean_dec(v_a_859_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_878_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_871_ = l_Lean_Syntax_getId(v_val_867_);
lean_dec(v_val_867_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_871_);
v___x_873_ = v___x_869_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_877_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_875_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_873_);
v___x_875_ = v___x_861_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
v_a_880_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_858_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_858_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Attribute_Builtin_getId_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_854_ = stack[0].m_obj;
lean_object* v_a_855_ = stack[1].m_obj;
lean_object* v_a_856_ = stack[2].m_obj;
lean_object* v_res_888_;
v_res_888_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_854_, v_a_855_, v_a_856_);
stack->m_obj
 = v_res_888_;
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_889_, v_a_890_, v_a_891_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
return v_res_893_;
}
}
lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_Attribute_Builtin_getIdent(v_stx_894_, v_a_895_, v_a_896_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_907_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_907_ == 0)
{
v___x_901_ = v___x_898_;
v_isShared_902_ = v_isSharedCheck_907_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_907_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_903_ = l_Lean_Syntax_getId(v_a_899_);
lean_dec(v_a_899_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_903_);
v___x_905_ = v___x_901_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
v_a_908_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_898_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_898_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Attribute_Builtin_getId_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_894_ = stack[0].m_obj;
lean_object* v_a_895_ = stack[1].m_obj;
lean_object* v_a_896_ = stack[2].m_obj;
lean_object* v_res_916_;
v_res_916_ = l_Lean_Attribute_Builtin_getId(v_stx_894_, v_a_895_, v_a_896_);
stack->m_obj
 = v_res_916_;
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_Attribute_Builtin_getId(v_stx_917_, v_a_918_, v_a_919_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
return v_res_921_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_924_ = l_Lean_stringToMessageData(v___x_923_);
return v___x_924_;
}
}
lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
uint8_t v___x_929_; 
v___x_929_ = l_Lean_Syntax_isNone(v_optPrioStx_925_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = lean_unsigned_to_nat(0u);
v___x_931_ = l_Lean_Syntax_getArg(v_optPrioStx_925_, v___x_930_);
v___x_932_ = l_Lean_Syntax_isNatLit_x3f(v___x_931_);
lean_dec(v___x_931_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_933_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_925_);
v___x_934_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_925_);
v___x_935_ = l_Lean_indentD(v___x_934_);
v___x_936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_933_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_925_, v___x_936_, v_a_926_, v_a_927_);
lean_dec(v_optPrioStx_925_);
return v___x_937_;
}
else
{
lean_object* v_val_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec(v_optPrioStx_925_);
v_val_938_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_932_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_val_938_);
lean_dec(v___x_932_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set_tag(v___x_940_, 0);
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_val_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
else
{
lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec(v_optPrioStx_925_);
v___x_946_ = lean_unsigned_to_nat(1000u);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
}
}
LEAN_EXPORT void l_Lean_getAttrParamOptPrio_0interp(lean_interpreter_value* stack)
{
lean_object* v_optPrioStx_925_ = stack[0].m_obj;
lean_object* v_a_926_ = stack[1].m_obj;
lean_object* v_a_927_ = stack[2].m_obj;
lean_object* v_res_948_;
v_res_948_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_925_, v_a_926_, v_a_927_);
stack->m_obj
 = v_res_948_;
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object* v_optPrioStx_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_949_, v_a_950_, v_a_951_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
return v_res_953_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getPrio___closed__1(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l_Lean_Attribute_Builtin_getPrio___closed__0));
v___x_956_ = l_Lean_stringToMessageData(v___x_955_);
return v___x_956_;
}
}
lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
lean_inc(v_stx_957_);
v___x_961_ = l_Lean_Syntax_getKind(v_stx_957_);
v___x_962_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_963_ = lean_name_eq(v___x_961_, v___x_962_);
lean_dec(v___x_961_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_964_ = lean_obj_once(&l_Lean_Attribute_Builtin_getPrio___closed__1, &l_Lean_Attribute_Builtin_getPrio___closed__1_once, _init_l_Lean_Attribute_Builtin_getPrio___closed__1);
lean_inc(v_stx_957_);
v___x_965_ = l_Lean_MessageData_ofSyntax(v_stx_957_);
v___x_966_ = l_Lean_indentD(v___x_965_);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_964_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_957_, v___x_967_, v_a_958_, v_a_959_);
lean_dec(v_stx_957_);
return v___x_968_;
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_969_ = lean_unsigned_to_nat(1u);
v___x_970_ = l_Lean_Syntax_getArg(v_stx_957_, v___x_969_);
lean_dec(v_stx_957_);
v___x_971_ = l_Lean_getAttrParamOptPrio(v___x_970_, v_a_958_, v_a_959_);
return v___x_971_;
}
}
}
LEAN_EXPORT void l_Lean_Attribute_Builtin_getPrio_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_957_ = stack[0].m_obj;
lean_object* v_a_958_ = stack[1].m_obj;
lean_object* v_a_959_ = stack[2].m_obj;
lean_object* v_res_972_;
v_res_972_ = l_Lean_Attribute_Builtin_getPrio(v_stx_957_, v_a_958_, v_a_959_);
stack->m_obj
 = v_res_972_;
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_Attribute_Builtin_getPrio(v_stx_973_, v_a_974_, v_a_975_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
return v_res_977_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_980_ = l_Lean_stringToMessageData(v___x_979_);
return v___x_980_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_983_ = l_Lean_stringToMessageData(v___x_982_);
return v___x_983_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_986_ = l_Lean_stringToMessageData(v___x_985_);
return v___x_986_;
}
}
lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_987_, lean_object* v_inst_988_, lean_object* v_name_989_, uint8_t v_kind_990_){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___y_997_; 
v___x_991_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_992_ = l_Lean_MessageData_ofName(v_name_989_);
v___x_993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_991_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
switch(v_kind_990_)
{
case 0:
{
lean_object* v___x_1004_; 
v___x_1004_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_997_ = v___x_1004_;
goto v___jp_996_;
}
case 1:
{
lean_object* v___x_1005_; 
v___x_1005_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_997_ = v___x_1005_;
goto v___jp_996_;
}
default: 
{
lean_object* v___x_1006_; 
v___x_1006_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_997_ = v___x_1006_;
goto v___jp_996_;
}
}
v___jp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_inc_ref(v___y_997_);
v___x_998_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_998_, 0, v___y_997_);
v___x_999_ = l_Lean_MessageData_ofFormat(v___x_998_);
v___x_1000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_995_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = l_Lean_throwError___redArg(v_inst_987_, v_inst_988_, v___x_1002_);
return v___x_1003_;
}
}
}
LEAN_EXPORT void l_Lean_throwAttrMustBeGlobal___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_987_ = stack[0].m_obj;
lean_object* v_inst_988_ = stack[1].m_obj;
lean_object* v_name_989_ = stack[2].m_obj;
uint8_t v_kind_990_ = stack[3].m_num;
lean_object* v_res_1007_;
v_res_1007_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_987_, v_inst_988_, v_name_989_, v_kind_990_);
stack->m_obj
 = v_res_1007_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_1008_, lean_object* v_inst_1009_, lean_object* v_name_1010_, lean_object* v_kind_1011_){
_start:
{
uint8_t v_kind_boxed_1012_; lean_object* v_res_1013_; 
v_kind_boxed_1012_ = lean_unbox(v_kind_1011_);
v_res_1013_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_1008_, v_inst_1009_, v_name_1010_, v_kind_boxed_1012_);
return v_res_1013_;
}
}
lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_1014_, lean_object* v_inst_1015_, lean_object* v_inst_1016_, lean_object* v_00_u03b1_1017_, lean_object* v_name_1018_, uint8_t v_kind_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_1015_, v_inst_1016_, v_name_1018_, v_kind_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT void l_Lean_throwAttrMustBeGlobal_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1015_ = stack[1].m_obj;
lean_object* v_inst_1016_ = stack[2].m_obj;
lean_object* v_name_1018_ = stack[4].m_obj;
uint8_t v_kind_1019_ = stack[5].m_num;
lean_object* v_res_1021_;
v_res_1021_ = l_Lean_throwAttrMustBeGlobal(lean_box(0), v_inst_1015_, v_inst_1016_, lean_box(0), v_name_1018_, v_kind_1019_);
stack->m_obj
 = v_res_1021_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_1022_, lean_object* v_inst_1023_, lean_object* v_inst_1024_, lean_object* v_00_u03b1_1025_, lean_object* v_name_1026_, lean_object* v_kind_1027_){
_start:
{
uint8_t v_kind_boxed_1028_; lean_object* v_res_1029_; 
v_kind_boxed_1028_ = lean_unbox(v_kind_1027_);
v_res_1029_ = l_Lean_throwAttrMustBeGlobal(v_m_1022_, v_inst_1023_, v_inst_1024_, v_00_u03b1_1025_, v_name_1026_, v_kind_boxed_1028_);
return v_res_1029_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_1032_ = l_Lean_stringToMessageData(v___x_1031_);
return v___x_1032_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_1035_ = l_Lean_stringToMessageData(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_1038_ = l_Lean_stringToMessageData(v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_1039_, lean_object* v_inst_1040_, lean_object* v_attrName_1041_, lean_object* v_declName_1042_){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1043_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1044_ = l_Lean_MessageData_ofName(v_attrName_1041_);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = 0;
v___x_1049_ = l_Lean_MessageData_ofConstName(v_declName_1042_, v___x_1048_);
v___x_1050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1047_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = l_Lean_throwError___redArg(v_inst_1039_, v_inst_1040_, v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_, lean_object* v_00_u03b1_1057_, lean_object* v_attrName_1058_, lean_object* v_declName_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1055_, v_inst_1056_, v_attrName_1058_, v_declName_1059_);
return v___x_1060_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1063_ = l_Lean_stringToMessageData(v___x_1062_);
return v___x_1063_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1066_ = l_Lean_stringToMessageData(v___x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1067_, lean_object* v_inst_1068_, lean_object* v_attrName_1069_, lean_object* v_declName_1070_, lean_object* v_asyncPrefix_x3f_1071_){
_start:
{
lean_object* v___y_1073_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1071_) == 0)
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_MessageData_nil;
v___y_1073_ = v___x_1086_;
goto v___jp_1072_;
}
else
{
lean_object* v_val_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v_val_1087_ = lean_ctor_get(v_asyncPrefix_x3f_1071_, 0);
lean_inc(v_val_1087_);
lean_dec_ref_known(v_asyncPrefix_x3f_1071_, 1);
v___x_1088_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1089_ = l_Lean_MessageData_ofName(v_val_1087_);
v___x_1090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___y_1073_ = v___x_1092_;
goto v___jp_1072_;
}
v___jp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1074_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1075_ = l_Lean_MessageData_ofName(v_attrName_1069_);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = 0;
v___x_1080_ = l_Lean_MessageData_ofConstName(v_declName_1070_, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1078_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v___y_1073_);
v___x_1085_ = l_Lean_throwError___redArg(v_inst_1067_, v_inst_1068_, v___x_1084_);
return v___x_1085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1093_, lean_object* v_inst_1094_, lean_object* v_inst_1095_, lean_object* v_00_u03b1_1096_, lean_object* v_attrName_1097_, lean_object* v_declName_1098_, lean_object* v_asyncPrefix_x3f_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1094_, v_inst_1095_, v_attrName_1097_, v_declName_1098_, v_asyncPrefix_x3f_1099_);
return v___x_1100_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1103_ = l_Lean_stringToMessageData(v___x_1102_);
return v___x_1103_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1106_ = l_Lean_stringToMessageData(v___x_1105_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1109_ = l_Lean_stringToMessageData(v___x_1108_);
return v___x_1109_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1112_ = l_Lean_stringToMessageData(v___x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1113_, lean_object* v_inst_1114_, lean_object* v_attrName_1115_, lean_object* v_declName_1116_, lean_object* v_givenType_1117_, lean_object* v_expectedType_1118_){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1119_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1120_ = l_Lean_MessageData_ofName(v_attrName_1115_);
lean_inc_ref(v___x_1120_);
v___x_1121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1119_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = 0;
v___x_1125_ = l_Lean_MessageData_ofConstName(v_declName_1116_, v___x_1124_);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1123_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_indentExpr(v_givenType_1117_);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1128_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
lean_ctor_set(v___x_1133_, 1, v___x_1120_);
v___x_1134_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = l_Lean_indentExpr(v_expectedType_1118_);
v___x_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1135_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = l_Lean_throwError___redArg(v_inst_1113_, v_inst_1114_, v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1139_, lean_object* v_inst_1140_, lean_object* v_inst_1141_, lean_object* v_00_u03b1_1142_, lean_object* v_attrName_1143_, lean_object* v_declName_1144_, lean_object* v_givenType_1145_, lean_object* v_expectedType_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1140_, v_inst_1141_, v_attrName_1143_, v_declName_1144_, v_givenType_1145_, v_expectedType_1146_);
return v___x_1147_;
}
}
lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1148_, uint8_t v_skipRealize_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; lean_object* v_env_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1152_ = lean_st_ref_get(v___y_1150_);
v_env_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc_ref(v_env_1153_);
lean_dec(v___x_1152_);
v___x_1154_ = l_Lean_Environment_contains(v_env_1153_, v_constName_1148_, v_skipRealize_1149_);
v___x_1155_ = lean_box(v___x_1154_);
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT void l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1148_ = stack[0].m_obj;
uint8_t v_skipRealize_1149_ = stack[1].m_num;
lean_object* v___y_1150_ = stack[2].m_obj;
lean_object* v_res_1157_;
v_res_1157_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1148_, v_skipRealize_1149_, v___y_1150_);
stack->m_obj
 = v_res_1157_;
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object* v_constName_1158_, lean_object* v_skipRealize_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
uint8_t v_skipRealize_boxed_1162_; lean_object* v_res_1163_; 
v_skipRealize_boxed_1162_ = lean_unbox(v_skipRealize_1159_);
v_res_1163_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1158_, v_skipRealize_boxed_1162_, v___y_1160_);
lean_dec(v___y_1160_);
return v_res_1163_;
}
}
lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1164_, uint8_t v_skipRealize_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1164_, v_skipRealize_1165_, v___y_1167_);
return v___x_1169_;
}
}
LEAN_EXPORT void l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1164_ = stack[0].m_obj;
uint8_t v_skipRealize_1165_ = stack[1].m_num;
lean_object* v___y_1166_ = stack[2].m_obj;
lean_object* v___y_1167_ = stack[3].m_obj;
lean_object* v_res_1170_;
v_res_1170_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1164_, v_skipRealize_1165_, v___y_1166_, v___y_1167_);
stack->m_obj
 = v_res_1170_;
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1171_, lean_object* v_skipRealize_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
uint8_t v_skipRealize_boxed_1176_; lean_object* v_res_1177_; 
v_skipRealize_boxed_1176_ = lean_unbox(v_skipRealize_1172_);
v_res_1177_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1171_, v_skipRealize_boxed_1176_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
return v_res_1177_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1178_, uint8_t v_isExporting_1179_, lean_object* v___x_1180_, lean_object* v_a_x3f_1181_){
_start:
{
lean_object* v___x_1183_; lean_object* v_env_1184_; lean_object* v_nextMacroScope_1185_; lean_object* v_ngen_1186_; lean_object* v_auxDeclNGen_1187_; lean_object* v_traceState_1188_; lean_object* v_recordedDeps_1189_; lean_object* v_messages_1190_; lean_object* v_infoState_1191_; lean_object* v_snapshotTasks_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1203_; 
v___x_1183_ = lean_st_ref_take(v___y_1178_);
v_env_1184_ = lean_ctor_get(v___x_1183_, 0);
v_nextMacroScope_1185_ = lean_ctor_get(v___x_1183_, 1);
v_ngen_1186_ = lean_ctor_get(v___x_1183_, 2);
v_auxDeclNGen_1187_ = lean_ctor_get(v___x_1183_, 3);
v_traceState_1188_ = lean_ctor_get(v___x_1183_, 4);
v_recordedDeps_1189_ = lean_ctor_get(v___x_1183_, 6);
v_messages_1190_ = lean_ctor_get(v___x_1183_, 7);
v_infoState_1191_ = lean_ctor_get(v___x_1183_, 8);
v_snapshotTasks_1192_ = lean_ctor_get(v___x_1183_, 9);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1203_ == 0)
{
lean_object* v_unused_1204_; 
v_unused_1204_ = lean_ctor_get(v___x_1183_, 5);
lean_dec(v_unused_1204_);
v___x_1194_ = v___x_1183_;
v_isShared_1195_ = v_isSharedCheck_1203_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_snapshotTasks_1192_);
lean_inc(v_infoState_1191_);
lean_inc(v_messages_1190_);
lean_inc(v_recordedDeps_1189_);
lean_inc(v_traceState_1188_);
lean_inc(v_auxDeclNGen_1187_);
lean_inc(v_ngen_1186_);
lean_inc(v_nextMacroScope_1185_);
lean_inc(v_env_1184_);
lean_dec(v___x_1183_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1203_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1196_ = lean_box(0);
v___x_1197_ = l_Lean_Environment_setExporting(v_env_1184_, v_isExporting_1179_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 5, v___x_1180_);
lean_ctor_set(v___x_1194_, 0, v___x_1197_);
v___x_1199_ = v___x_1194_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_nextMacroScope_1185_);
lean_ctor_set(v_reuseFailAlloc_1202_, 2, v_ngen_1186_);
lean_ctor_set(v_reuseFailAlloc_1202_, 3, v_auxDeclNGen_1187_);
lean_ctor_set(v_reuseFailAlloc_1202_, 4, v_traceState_1188_);
lean_ctor_set(v_reuseFailAlloc_1202_, 5, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1202_, 6, v_recordedDeps_1189_);
lean_ctor_set(v_reuseFailAlloc_1202_, 7, v_messages_1190_);
lean_ctor_set(v_reuseFailAlloc_1202_, 8, v_infoState_1191_);
lean_ctor_set(v_reuseFailAlloc_1202_, 9, v_snapshotTasks_1192_);
v___x_1199_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_st_ref_put(v___y_1178_, v___x_1199_);
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1196_);
return v___x_1201_;
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1178_ = stack[0].m_obj;
uint8_t v_isExporting_1179_ = stack[1].m_num;
lean_object* v___x_1180_ = stack[2].m_obj;
lean_object* v_a_x3f_1181_ = stack[3].m_obj;
lean_object* v_res_1205_;
v_res_1205_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1178_, v_isExporting_1179_, v___x_1180_, v_a_x3f_1181_);
stack->m_obj
 = v_res_1205_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1206_, lean_object* v_isExporting_1207_, lean_object* v___x_1208_, lean_object* v_a_x3f_1209_, lean_object* v___y_1210_){
_start:
{
uint8_t v_isExporting_boxed_1211_; lean_object* v_res_1212_; 
v_isExporting_boxed_1211_ = lean_unbox(v_isExporting_1207_);
v_res_1212_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1206_, v_isExporting_boxed_1211_, v___x_1208_, v_a_x3f_1209_);
lean_dec(v_a_x3f_1209_);
lean_dec(v___y_1206_);
return v_res_1212_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
return v___x_1214_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
return v___x_1216_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1217_, uint8_t v_isExporting_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___x_1222_; lean_object* v_env_1223_; lean_object* v___x_1224_; uint8_t v_isModule_1225_; 
v___x_1222_ = lean_st_ref_get(v___y_1220_);
v_env_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc_ref(v_env_1223_);
lean_dec(v___x_1222_);
v___x_1224_ = l_Lean_Environment_header(v_env_1223_);
v_isModule_1225_ = lean_ctor_get_uint8(v___x_1224_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1224_);
if (v_isModule_1225_ == 0)
{
lean_object* v___x_1226_; 
lean_dec_ref(v_env_1223_);
lean_inc(v___y_1220_);
lean_inc_ref(v___y_1219_);
v___x_1226_ = lean_apply_3(v_x_1217_, v___y_1219_, v___y_1220_, lean_box(0));
return v___x_1226_;
}
else
{
uint8_t v_isExporting_1227_; 
v_isExporting_1227_ = lean_ctor_get_uint8(v_env_1223_, sizeof(void*)*13);
lean_dec_ref(v_env_1223_);
if (v_isExporting_1218_ == 0)
{
if (v_isExporting_1227_ == 0)
{
lean_object* v___x_1279_; 
lean_inc(v___y_1220_);
lean_inc_ref(v___y_1219_);
v___x_1279_ = lean_apply_3(v_x_1217_, v___y_1219_, v___y_1220_, lean_box(0));
return v___x_1279_;
}
else
{
goto v___jp_1228_;
}
}
else
{
if (v_isExporting_1227_ == 0)
{
goto v___jp_1228_;
}
else
{
lean_object* v___x_1280_; 
lean_inc(v___y_1220_);
lean_inc_ref(v___y_1219_);
v___x_1280_ = lean_apply_3(v_x_1217_, v___y_1219_, v___y_1220_, lean_box(0));
return v___x_1280_;
}
}
v___jp_1228_:
{
lean_object* v___x_1229_; lean_object* v_env_1230_; lean_object* v_nextMacroScope_1231_; lean_object* v_ngen_1232_; lean_object* v_auxDeclNGen_1233_; lean_object* v_traceState_1234_; lean_object* v_recordedDeps_1235_; lean_object* v_messages_1236_; lean_object* v_infoState_1237_; lean_object* v_snapshotTasks_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1277_; 
v___x_1229_ = lean_st_ref_take(v___y_1220_);
v_env_1230_ = lean_ctor_get(v___x_1229_, 0);
v_nextMacroScope_1231_ = lean_ctor_get(v___x_1229_, 1);
v_ngen_1232_ = lean_ctor_get(v___x_1229_, 2);
v_auxDeclNGen_1233_ = lean_ctor_get(v___x_1229_, 3);
v_traceState_1234_ = lean_ctor_get(v___x_1229_, 4);
v_recordedDeps_1235_ = lean_ctor_get(v___x_1229_, 6);
v_messages_1236_ = lean_ctor_get(v___x_1229_, 7);
v_infoState_1237_ = lean_ctor_get(v___x_1229_, 8);
v_snapshotTasks_1238_ = lean_ctor_get(v___x_1229_, 9);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v___x_1229_, 5);
lean_dec(v_unused_1278_);
v___x_1240_ = v___x_1229_;
v_isShared_1241_ = v_isSharedCheck_1277_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_snapshotTasks_1238_);
lean_inc(v_infoState_1237_);
lean_inc(v_messages_1236_);
lean_inc(v_recordedDeps_1235_);
lean_inc(v_traceState_1234_);
lean_inc(v_auxDeclNGen_1233_);
lean_inc(v_ngen_1232_);
lean_inc(v_nextMacroScope_1231_);
lean_inc(v_env_1230_);
lean_dec(v___x_1229_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1277_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___x_1242_ = l_Lean_Environment_setExporting(v_env_1230_, v_isExporting_1218_);
v___x_1243_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 5, v___x_1243_);
lean_ctor_set(v___x_1240_, 0, v___x_1242_);
v___x_1245_ = v___x_1240_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_nextMacroScope_1231_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v_ngen_1232_);
lean_ctor_set(v_reuseFailAlloc_1276_, 3, v_auxDeclNGen_1233_);
lean_ctor_set(v_reuseFailAlloc_1276_, 4, v_traceState_1234_);
lean_ctor_set(v_reuseFailAlloc_1276_, 5, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1276_, 6, v_recordedDeps_1235_);
lean_ctor_set(v_reuseFailAlloc_1276_, 7, v_messages_1236_);
lean_ctor_set(v_reuseFailAlloc_1276_, 8, v_infoState_1237_);
lean_ctor_set(v_reuseFailAlloc_1276_, 9, v_snapshotTasks_1238_);
v___x_1245_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1246_; lean_object* v_r_1247_; 
v___x_1246_ = lean_st_ref_put(v___y_1220_, v___x_1245_);
lean_inc(v___y_1220_);
lean_inc_ref(v___y_1219_);
v_r_1247_ = lean_apply_3(v_x_1217_, v___y_1219_, v___y_1220_, lean_box(0));
if (lean_obj_tag(v_r_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1264_; 
v_a_1248_ = lean_ctor_get(v_r_1247_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_r_1247_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1250_ = v_r_1247_;
v_isShared_1251_ = v_isSharedCheck_1264_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v_r_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1264_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
lean_inc(v_a_1248_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set_tag(v___x_1250_, 1);
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
v___x_1254_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1220_, v_isExporting_1227_, v___x_1243_, v___x_1253_);
lean_dec_ref(v___x_1253_);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1261_ == 0)
{
lean_object* v_unused_1262_; 
v_unused_1262_ = lean_ctor_get(v___x_1254_, 0);
lean_dec(v_unused_1262_);
v___x_1256_ = v___x_1254_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_dec(v___x_1254_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v_a_1248_);
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1248_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
v_a_1265_ = lean_ctor_get(v_r_1247_, 0);
lean_inc(v_a_1265_);
lean_dec_ref_known(v_r_1247_, 1);
v___x_1266_ = lean_box(0);
v___x_1267_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1220_, v_isExporting_1227_, v___x_1243_, v___x_1266_);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v___x_1267_, 0);
lean_dec(v_unused_1275_);
v___x_1269_ = v___x_1267_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_dec(v___x_1267_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set_tag(v___x_1269_, 1);
lean_ctor_set(v___x_1269_, 0, v_a_1265_);
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1265_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1217_ = stack[0].m_obj;
uint8_t v_isExporting_1218_ = stack[1].m_num;
lean_object* v___y_1219_ = stack[2].m_obj;
lean_object* v___y_1220_ = stack[3].m_obj;
lean_object* v_res_1281_;
v_res_1281_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1217_, v_isExporting_1218_, v___y_1219_, v___y_1220_);
stack->m_obj
 = v_res_1281_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1282_, lean_object* v_isExporting_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
uint8_t v_isExporting_boxed_1287_; lean_object* v_res_1288_; 
v_isExporting_boxed_1287_ = lean_unbox(v_isExporting_1283_);
v_res_1288_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1282_, v_isExporting_boxed_1287_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
return v_res_1288_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1289_, lean_object* v_x_1290_, uint8_t v_isExporting_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1290_, v_isExporting_1291_, v___y_1292_, v___y_1293_);
return v___x_1295_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1290_ = stack[1].m_obj;
uint8_t v_isExporting_1291_ = stack[2].m_num;
lean_object* v___y_1292_ = stack[3].m_obj;
lean_object* v___y_1293_ = stack[4].m_obj;
lean_object* v_res_1296_;
v_res_1296_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_box(0), v_x_1290_, v_isExporting_1291_, v___y_1292_, v___y_1293_);
stack->m_obj
 = v_res_1296_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1297_, lean_object* v_x_1298_, lean_object* v_isExporting_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
uint8_t v_isExporting_boxed_1303_; lean_object* v_res_1304_; 
v_isExporting_boxed_1303_ = lean_unbox(v_isExporting_1299_);
v_res_1304_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1297_, v_x_1298_, v_isExporting_boxed_1303_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
return v_res_1304_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1305_, lean_object* v_opt_1306_){
_start:
{
lean_object* v_name_1307_; lean_object* v_defValue_1308_; lean_object* v_map_1309_; lean_object* v___x_1310_; 
v_name_1307_ = lean_ctor_get(v_opt_1306_, 0);
v_defValue_1308_ = lean_ctor_get(v_opt_1306_, 1);
v_map_1309_ = lean_ctor_get(v_opts_1305_, 0);
v___x_1310_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1309_, v_name_1307_);
if (lean_obj_tag(v___x_1310_) == 0)
{
uint8_t v___x_1311_; 
v___x_1311_ = lean_unbox(v_defValue_1308_);
return v___x_1311_;
}
else
{
lean_object* v_val_1312_; 
v_val_1312_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_val_1312_);
lean_dec_ref_known(v___x_1310_, 1);
if (lean_obj_tag(v_val_1312_) == 1)
{
uint8_t v_v_1313_; 
v_v_1313_ = lean_ctor_get_uint8(v_val_1312_, 0);
lean_dec_ref_known(v_val_1312_, 0);
return v_v_1313_;
}
else
{
uint8_t v___x_1314_; 
lean_dec(v_val_1312_);
v___x_1314_ = lean_unbox(v_defValue_1308_);
return v___x_1314_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1305_ = stack[0].m_obj;
lean_object* v_opt_1306_ = stack[1].m_obj;
uint8_t v_res_1315_;
v_res_1315_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1305_, v_opt_1306_);
stack->m_num = v_res_1315_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1316_, lean_object* v_opt_1317_){
_start:
{
uint8_t v_res_1318_; lean_object* v_r_1319_; 
v_res_1318_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1316_, v_opt_1317_);
lean_dec_ref(v_opt_1317_);
lean_dec_ref(v_opts_1316_);
v_r_1319_ = lean_box(v_res_1318_);
return v_r_1319_;
}
}
uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_1327_, uint8_t v___y_1328_, lean_object* v_x_1329_){
_start:
{
if (lean_obj_tag(v_x_1329_) == 1)
{
lean_object* v_pre_1330_; 
v_pre_1330_ = lean_ctor_get(v_x_1329_, 0);
switch(lean_obj_tag(v_pre_1330_))
{
case 1:
{
lean_object* v_pre_1331_; 
v_pre_1331_ = lean_ctor_get(v_pre_1330_, 0);
switch(lean_obj_tag(v_pre_1331_))
{
case 0:
{
lean_object* v_str_1332_; lean_object* v_str_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v_str_1332_ = lean_ctor_get(v_x_1329_, 1);
v_str_1333_ = lean_ctor_get(v_pre_1330_, 1);
v___x_1334_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1335_ = lean_string_dec_eq(v_str_1333_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1337_ = lean_string_dec_eq(v_str_1333_, v___x_1336_);
if (v___x_1337_ == 0)
{
return v___x_1337_;
}
else
{
lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1338_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1339_ = lean_string_dec_eq(v_str_1332_, v___x_1338_);
if (v___x_1339_ == 0)
{
return v___x_1339_;
}
else
{
return v_suppressElabErrors_1327_;
}
}
}
else
{
lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1340_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1341_ = lean_string_dec_eq(v_str_1332_, v___x_1340_);
if (v___x_1341_ == 0)
{
return v___x_1341_;
}
else
{
return v_suppressElabErrors_1327_;
}
}
}
case 1:
{
lean_object* v_pre_1342_; 
v_pre_1342_ = lean_ctor_get(v_pre_1331_, 0);
if (lean_obj_tag(v_pre_1342_) == 0)
{
lean_object* v_str_1343_; lean_object* v_str_1344_; lean_object* v_str_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v_str_1343_ = lean_ctor_get(v_x_1329_, 1);
v_str_1344_ = lean_ctor_get(v_pre_1330_, 1);
v_str_1345_ = lean_ctor_get(v_pre_1331_, 1);
v___x_1346_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1347_ = lean_string_dec_eq(v_str_1345_, v___x_1346_);
if (v___x_1347_ == 0)
{
return v___x_1347_;
}
else
{
lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1348_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1349_ = lean_string_dec_eq(v_str_1344_, v___x_1348_);
if (v___x_1349_ == 0)
{
return v___x_1349_;
}
else
{
lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1350_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1351_ = lean_string_dec_eq(v_str_1343_, v___x_1350_);
if (v___x_1351_ == 0)
{
return v___x_1351_;
}
else
{
return v_suppressElabErrors_1327_;
}
}
}
}
else
{
return v___y_1328_;
}
}
default: 
{
return v___y_1328_;
}
}
}
case 0:
{
lean_object* v_str_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v_str_1352_ = lean_ctor_get(v_x_1329_, 1);
v___x_1353_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1354_ = lean_string_dec_eq(v_str_1352_, v___x_1353_);
if (v___x_1354_ == 0)
{
return v___x_1354_;
}
else
{
return v_suppressElabErrors_1327_;
}
}
default: 
{
return v___y_1328_;
}
}
}
else
{
return v___y_1328_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_1327_ = stack[0].m_num;
uint8_t v___y_1328_ = stack[1].m_num;
lean_object* v_x_1329_ = stack[2].m_obj;
uint8_t v_res_1355_;
v_res_1355_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v_suppressElabErrors_1327_, v___y_1328_, v_x_1329_);
stack->m_num = v_res_1355_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_1356_, lean_object* v___y_1357_, lean_object* v_x_1358_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1359_; uint8_t v___y_5184__boxed_1360_; uint8_t v_res_1361_; lean_object* v_r_1362_; 
v_suppressElabErrors_boxed_1359_ = lean_unbox(v_suppressElabErrors_1356_);
v___y_5184__boxed_1360_ = lean_unbox(v___y_1357_);
v_res_1361_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_1359_, v___y_5184__boxed_1360_, v_x_1358_);
lean_dec(v_x_1358_);
v_r_1362_ = lean_box(v_res_1361_);
return v_r_1362_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1363_, lean_object* v_msgData_1364_, uint8_t v_severity_1365_, uint8_t v_isSilent_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
uint8_t v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; uint8_t v___y_1377_; lean_object* v_toCold_1378_; lean_object* v___y_1379_; lean_object* v___y_1408_; lean_object* v___y_1409_; uint8_t v___y_1410_; uint8_t v___y_1411_; lean_object* v___y_1412_; uint8_t v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; uint8_t v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; uint8_t v___y_1438_; lean_object* v___y_1439_; uint8_t v___y_1440_; lean_object* v___y_1441_; uint8_t v___y_1445_; uint8_t v___y_1446_; uint8_t v___y_1447_; uint8_t v___x_1458_; uint8_t v___y_1460_; uint8_t v___y_1461_; uint8_t v___y_1462_; uint8_t v___y_1464_; uint8_t v___x_1472_; 
v___x_1458_ = 2;
v___x_1472_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1365_, v___x_1458_);
if (v___x_1472_ == 0)
{
v___y_1464_ = v___x_1472_;
goto v___jp_1463_;
}
else
{
uint8_t v___x_1473_; 
lean_inc_ref(v_msgData_1364_);
v___x_1473_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1364_);
v___y_1464_ = v___x_1473_;
goto v___jp_1463_;
}
v___jp_1370_:
{
lean_object* v_currNamespace_1380_; lean_object* v_openDecls_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v_env_1386_; lean_object* v_nextMacroScope_1387_; lean_object* v_ngen_1388_; lean_object* v_auxDeclNGen_1389_; lean_object* v_traceState_1390_; lean_object* v_cache_1391_; lean_object* v_recordedDeps_1392_; lean_object* v_messages_1393_; lean_object* v_infoState_1394_; lean_object* v_snapshotTasks_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1406_; 
v_currNamespace_1380_ = lean_ctor_get(v_toCold_1378_, 4);
v_openDecls_1381_ = lean_ctor_get(v_toCold_1378_, 5);
lean_inc(v_openDecls_1381_);
lean_inc(v_currNamespace_1380_);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v_currNamespace_1380_);
lean_ctor_set(v___x_1382_, 1, v_openDecls_1381_);
v___x_1383_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v___y_1373_);
lean_inc_ref(v___y_1376_);
lean_inc_ref(v___y_1375_);
v___x_1384_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1384_, 0, v___y_1375_);
lean_ctor_set(v___x_1384_, 1, v___y_1374_);
lean_ctor_set(v___x_1384_, 2, v___y_1372_);
lean_ctor_set(v___x_1384_, 3, v___y_1376_);
lean_ctor_set(v___x_1384_, 4, v___x_1383_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*5, v___y_1377_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*5 + 1, v___y_1371_);
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*5 + 2, v_isSilent_1366_);
v___x_1385_ = lean_st_ref_take(v___y_1379_);
v_env_1386_ = lean_ctor_get(v___x_1385_, 0);
v_nextMacroScope_1387_ = lean_ctor_get(v___x_1385_, 1);
v_ngen_1388_ = lean_ctor_get(v___x_1385_, 2);
v_auxDeclNGen_1389_ = lean_ctor_get(v___x_1385_, 3);
v_traceState_1390_ = lean_ctor_get(v___x_1385_, 4);
v_cache_1391_ = lean_ctor_get(v___x_1385_, 5);
v_recordedDeps_1392_ = lean_ctor_get(v___x_1385_, 6);
v_messages_1393_ = lean_ctor_get(v___x_1385_, 7);
v_infoState_1394_ = lean_ctor_get(v___x_1385_, 8);
v_snapshotTasks_1395_ = lean_ctor_get(v___x_1385_, 9);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1397_ = v___x_1385_;
v_isShared_1398_ = v_isSharedCheck_1406_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_snapshotTasks_1395_);
lean_inc(v_infoState_1394_);
lean_inc(v_messages_1393_);
lean_inc(v_recordedDeps_1392_);
lean_inc(v_cache_1391_);
lean_inc(v_traceState_1390_);
lean_inc(v_auxDeclNGen_1389_);
lean_inc(v_ngen_1388_);
lean_inc(v_nextMacroScope_1387_);
lean_inc(v_env_1386_);
lean_dec(v___x_1385_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1406_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1399_ = lean_box(0);
v___x_1400_ = l_Lean_MessageLog_add(v___x_1384_, v_messages_1393_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 7, v___x_1400_);
v___x_1402_ = v___x_1397_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_env_1386_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_nextMacroScope_1387_);
lean_ctor_set(v_reuseFailAlloc_1405_, 2, v_ngen_1388_);
lean_ctor_set(v_reuseFailAlloc_1405_, 3, v_auxDeclNGen_1389_);
lean_ctor_set(v_reuseFailAlloc_1405_, 4, v_traceState_1390_);
lean_ctor_set(v_reuseFailAlloc_1405_, 5, v_cache_1391_);
lean_ctor_set(v_reuseFailAlloc_1405_, 6, v_recordedDeps_1392_);
lean_ctor_set(v_reuseFailAlloc_1405_, 7, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1405_, 8, v_infoState_1394_);
lean_ctor_set(v_reuseFailAlloc_1405_, 9, v_snapshotTasks_1395_);
v___x_1402_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_st_ref_put(v___y_1379_, v___x_1402_);
v___x_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1399_);
return v___x_1404_;
}
}
}
v___jp_1407_:
{
lean_object* v_fileName_1416_; lean_object* v_fileMap_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1433_; 
v_fileName_1416_ = lean_ctor_get(v___y_1414_, 0);
v_fileMap_1417_ = lean_ctor_get(v___y_1414_, 1);
v___x_1418_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1364_);
v___x_1419_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v___x_1418_, v___y_1367_, v___y_1368_);
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1422_ = v___x_1419_;
v_isShared_1423_ = v_isSharedCheck_1433_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1419_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1433_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_inc_ref_n(v_fileMap_1417_, 2);
v___x_1424_ = l_Lean_FileMap_toPosition(v_fileMap_1417_, v___y_1412_);
lean_dec(v___y_1412_);
v___x_1425_ = l_Lean_FileMap_toPosition(v_fileMap_1417_, v___y_1415_);
lean_dec(v___y_1415_);
v___x_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
v___x_1427_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1411_ == 0)
{
lean_del_object(v___x_1422_);
lean_dec_ref(v___y_1408_);
v___y_1371_ = v___y_1410_;
v___y_1372_ = v___x_1426_;
v___y_1373_ = v_a_1420_;
v___y_1374_ = v___x_1424_;
v___y_1375_ = v_fileName_1416_;
v___y_1376_ = v___x_1427_;
v___y_1377_ = v___y_1413_;
v_toCold_1378_ = v___y_1409_;
v___y_1379_ = v___y_1368_;
goto v___jp_1370_;
}
else
{
uint8_t v___x_1428_; 
lean_inc(v_a_1420_);
v___x_1428_ = l_Lean_MessageData_hasTag(v___y_1408_, v_a_1420_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
lean_dec_ref_known(v___x_1426_, 1);
lean_dec_ref(v___x_1424_);
lean_dec(v_a_1420_);
v___x_1429_ = lean_box(0);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v___x_1429_);
v___x_1431_ = v___x_1422_;
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
else
{
lean_del_object(v___x_1422_);
v___y_1371_ = v___y_1410_;
v___y_1372_ = v___x_1426_;
v___y_1373_ = v_a_1420_;
v___y_1374_ = v___x_1424_;
v___y_1375_ = v_fileName_1416_;
v___y_1376_ = v___x_1427_;
v___y_1377_ = v___y_1413_;
v_toCold_1378_ = v___y_1409_;
v___y_1379_ = v___y_1368_;
goto v___jp_1370_;
}
}
}
}
v___jp_1434_:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_Syntax_getTailPos_x3f(v___y_1439_, v___y_1440_);
lean_dec(v___y_1439_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_inc(v___y_1441_);
v___y_1408_ = v___y_1436_;
v___y_1409_ = v___y_1437_;
v___y_1410_ = v___y_1438_;
v___y_1411_ = v___y_1435_;
v___y_1412_ = v___y_1441_;
v___y_1413_ = v___y_1440_;
v___y_1414_ = v___y_1437_;
v___y_1415_ = v___y_1441_;
goto v___jp_1407_;
}
else
{
lean_object* v_val_1443_; 
v_val_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_val_1443_);
lean_dec_ref_known(v___x_1442_, 1);
v___y_1408_ = v___y_1436_;
v___y_1409_ = v___y_1437_;
v___y_1410_ = v___y_1438_;
v___y_1411_ = v___y_1435_;
v___y_1412_ = v___y_1441_;
v___y_1413_ = v___y_1440_;
v___y_1414_ = v___y_1437_;
v___y_1415_ = v_val_1443_;
goto v___jp_1407_;
}
}
v___jp_1444_:
{
lean_object* v_toCold_1448_; lean_object* v_ref_1449_; uint8_t v_suppressElabErrors_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___f_1453_; lean_object* v_ref_1454_; lean_object* v___x_1455_; 
v_toCold_1448_ = lean_ctor_get(v___y_1367_, 0);
v_ref_1449_ = lean_ctor_get(v___y_1367_, 2);
v_suppressElabErrors_1450_ = lean_ctor_get_uint8(v___y_1367_, sizeof(void*)*3 + 2);
v___x_1451_ = lean_box(v_suppressElabErrors_1450_);
v___x_1452_ = lean_box(v___y_1445_);
v___f_1453_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1453_, 0, v___x_1451_);
lean_closure_set(v___f_1453_, 1, v___x_1452_);
v_ref_1454_ = l_Lean_replaceRef(v_ref_1363_, v_ref_1449_);
v___x_1455_ = l_Lean_Syntax_getPos_x3f(v_ref_1454_, v___y_1446_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_unsigned_to_nat(0u);
v___y_1435_ = v_suppressElabErrors_1450_;
v___y_1436_ = v___f_1453_;
v___y_1437_ = v_toCold_1448_;
v___y_1438_ = v___y_1447_;
v___y_1439_ = v_ref_1454_;
v___y_1440_ = v___y_1446_;
v___y_1441_ = v___x_1456_;
goto v___jp_1434_;
}
else
{
lean_object* v_val_1457_; 
v_val_1457_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_val_1457_);
lean_dec_ref_known(v___x_1455_, 1);
v___y_1435_ = v_suppressElabErrors_1450_;
v___y_1436_ = v___f_1453_;
v___y_1437_ = v_toCold_1448_;
v___y_1438_ = v___y_1447_;
v___y_1439_ = v_ref_1454_;
v___y_1440_ = v___y_1446_;
v___y_1441_ = v_val_1457_;
goto v___jp_1434_;
}
}
v___jp_1459_:
{
if (v___y_1462_ == 0)
{
v___y_1445_ = v___y_1460_;
v___y_1446_ = v___y_1461_;
v___y_1447_ = v_severity_1365_;
goto v___jp_1444_;
}
else
{
v___y_1445_ = v___y_1460_;
v___y_1446_ = v___y_1461_;
v___y_1447_ = v___x_1458_;
goto v___jp_1444_;
}
}
v___jp_1463_:
{
if (v___y_1464_ == 0)
{
uint8_t v___x_1465_; uint8_t v___x_1466_; 
v___x_1465_ = 1;
v___x_1466_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1365_, v___x_1465_);
if (v___x_1466_ == 0)
{
v___y_1460_ = v___y_1464_;
v___y_1461_ = v___y_1464_;
v___y_1462_ = v___x_1466_;
goto v___jp_1459_;
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1467_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1367_);
v___x_1468_ = l_Lean_warningAsError;
v___x_1469_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v___x_1467_, v___x_1468_);
lean_dec_ref(v___x_1467_);
v___y_1460_ = v___y_1464_;
v___y_1461_ = v___y_1464_;
v___y_1462_ = v___x_1469_;
goto v___jp_1459_;
}
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec_ref(v_msgData_1364_);
v___x_1470_ = lean_box(0);
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1363_ = stack[0].m_obj;
lean_object* v_msgData_1364_ = stack[1].m_obj;
uint8_t v_severity_1365_ = stack[2].m_num;
uint8_t v_isSilent_1366_ = stack[3].m_num;
lean_object* v___y_1367_ = stack[4].m_obj;
lean_object* v___y_1368_ = stack[5].m_obj;
lean_object* v_res_1474_;
v_res_1474_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1363_, v_msgData_1364_, v_severity_1365_, v_isSilent_1366_, v___y_1367_, v___y_1368_);
stack->m_obj
 = v_res_1474_;
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
lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1485_, uint8_t v_severity_1486_, uint8_t v_isSilent_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_ref_1491_; lean_object* v___x_1492_; 
v_ref_1491_ = lean_ctor_get(v___y_1488_, 2);
v___x_1492_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1491_, v_msgData_1485_, v_severity_1486_, v_isSilent_1487_, v___y_1488_, v___y_1489_);
return v___x_1492_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1485_ = stack[0].m_obj;
uint8_t v_severity_1486_ = stack[1].m_num;
uint8_t v_isSilent_1487_ = stack[2].m_num;
lean_object* v___y_1488_ = stack[3].m_obj;
lean_object* v___y_1489_ = stack[4].m_obj;
lean_object* v_res_1493_;
v_res_1493_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1485_, v_severity_1486_, v_isSilent_1487_, v___y_1488_, v___y_1489_);
stack->m_obj
 = v_res_1493_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1494_, lean_object* v_severity_1495_, lean_object* v_isSilent_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
uint8_t v_severity_boxed_1500_; uint8_t v_isSilent_boxed_1501_; lean_object* v_res_1502_; 
v_severity_boxed_1500_ = lean_unbox(v_severity_1495_);
v_isSilent_boxed_1501_ = lean_unbox(v_isSilent_1496_);
v_res_1502_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1494_, v_severity_boxed_1500_, v_isSilent_boxed_1501_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
return v_res_1502_;
}
}
lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
uint8_t v___x_1507_; uint8_t v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = 1;
v___x_1508_ = 0;
v___x_1509_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1503_, v___x_1507_, v___x_1508_, v___y_1504_, v___y_1505_);
return v___x_1509_;
}
}
LEAN_EXPORT void l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1503_ = stack[0].m_obj;
lean_object* v___y_1504_ = stack[1].m_obj;
lean_object* v___y_1505_ = stack[2].m_obj;
lean_object* v_res_1510_;
v_res_1510_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1503_, v___y_1504_, v___y_1505_);
stack->m_obj
 = v_res_1510_;
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
return v_res_1515_;
}
}
lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v___x_1519_; uint8_t v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1519_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1517_);
v___x_1520_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v___x_1519_, v_opt_1516_);
lean_dec_ref(v___x_1519_);
v___x_1521_ = lean_box(v___x_1520_);
v___x_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT void l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_1516_ = stack[0].m_obj;
lean_object* v___y_1517_ = stack[1].m_obj;
lean_object* v_res_1523_;
v_res_1523_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1516_, v___y_1517_);
stack->m_obj
 = v_res_1523_;
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1524_, v___y_1525_);
lean_dec_ref(v___y_1525_);
lean_dec_ref(v_opt_1524_);
return v_res_1527_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1530_ = l_Lean_stringToMessageData(v___x_1529_);
return v___x_1530_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1533_ = l_Lean_stringToMessageData(v___x_1532_);
return v___x_1533_;
}
}
lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; lean_object* v_env_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1561_; 
v___x_1538_ = lean_st_ref_get(v___y_1536_);
v_env_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc_ref(v_env_1539_);
lean_dec(v___x_1538_);
v___x_1540_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1541_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1540_, v___y_1535_);
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1544_ = v___x_1541_;
v_isShared_1545_ = v_isSharedCheck_1561_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1561_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
uint8_t v_isExporting_1551_; 
v_isExporting_1551_ = lean_ctor_get_uint8(v_env_1539_, sizeof(void*)*13);
lean_dec_ref(v_env_1539_);
if (v_isExporting_1551_ == 0)
{
lean_dec(v_a_1542_);
lean_dec(v_id_1534_);
goto v___jp_1546_;
}
else
{
uint8_t v___x_1552_; 
v___x_1552_ = l_Lean_isPrivateName(v_id_1534_);
if (v___x_1552_ == 0)
{
lean_dec(v_a_1542_);
lean_dec(v_id_1534_);
goto v___jp_1546_;
}
else
{
uint8_t v___x_1553_; 
v___x_1553_ = lean_unbox(v_a_1542_);
lean_dec(v_a_1542_);
if (v___x_1553_ == 0)
{
lean_dec(v_id_1534_);
goto v___jp_1546_;
}
else
{
lean_object* v___x_1554_; uint8_t v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
lean_del_object(v___x_1544_);
v___x_1554_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1555_ = 0;
v___x_1556_ = l_Lean_MessageData_ofConstName(v_id_1534_, v___x_1555_);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1554_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1559_, v___y_1535_, v___y_1536_);
return v___x_1560_;
}
}
}
v___jp_1546_:
{
lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1547_ = lean_box(0);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1547_);
v___x_1549_ = v___x_1544_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_1534_ = stack[0].m_obj;
lean_object* v___y_1535_ = stack[1].m_obj;
lean_object* v___y_1536_ = stack[2].m_obj;
lean_object* v_res_1562_;
v_res_1562_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1534_, v___y_1535_, v___y_1536_);
stack->m_obj
 = v_res_1562_;
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1563_, v___y_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
return v_res_1567_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1570_ = l_Lean_stringToMessageData(v___x_1569_);
return v___x_1570_;
}
}
lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1571_, uint8_t v_isModule_1572_, lean_object* v_attrName_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1577_; 
lean_inc(v_declName_1571_);
v___x_1577_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1571_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v___x_1578_; lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1599_; 
lean_dec_ref_known(v___x_1577_, 1);
lean_inc(v_declName_1571_);
v___x_1578_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1571_, v_isModule_1572_, v___y_1575_);
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1581_ = v___x_1578_;
v_isShared_1582_ = v_isSharedCheck_1599_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1578_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1599_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
uint8_t v___x_1583_; 
v___x_1583_ = lean_unbox(v_a_1579_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
lean_del_object(v___x_1581_);
v___x_1584_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1585_ = l_Lean_MessageData_ofName(v_attrName_1573_);
v___x_1586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1584_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = lean_unbox(v_a_1579_);
lean_dec(v_a_1579_);
v___x_1590_ = l_Lean_MessageData_ofConstName(v_declName_1571_, v___x_1589_);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1588_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1593_, v___y_1574_, v___y_1575_);
return v___x_1594_;
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1597_; 
lean_dec(v_a_1579_);
lean_dec(v_attrName_1573_);
lean_dec(v_declName_1571_);
v___x_1595_ = lean_box(0);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v___x_1595_);
v___x_1597_ = v___x_1581_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
else
{
lean_dec(v_attrName_1573_);
lean_dec(v_declName_1571_);
return v___x_1577_;
}
}
}
LEAN_EXPORT void l_Lean_ensureAttrDeclIsPublic___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1571_ = stack[0].m_obj;
uint8_t v_isModule_1572_ = stack[1].m_num;
lean_object* v_attrName_1573_ = stack[2].m_obj;
lean_object* v___y_1574_ = stack[3].m_obj;
lean_object* v___y_1575_ = stack[4].m_obj;
lean_object* v_res_1600_;
v_res_1600_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1571_, v_isModule_1572_, v_attrName_1573_, v___y_1574_, v___y_1575_);
stack->m_obj
 = v_res_1600_;
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1601_, lean_object* v_isModule_1602_, lean_object* v_attrName_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
uint8_t v_isModule_boxed_1607_; lean_object* v_res_1608_; 
v_isModule_boxed_1607_ = lean_unbox(v_isModule_1602_);
v_res_1608_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1601_, v_isModule_boxed_1607_, v_attrName_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
return v_res_1608_;
}
}
lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1609_, lean_object* v_declName_1610_, uint8_t v_attrKind_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v___x_1615_; lean_object* v_env_1619_; lean_object* v___x_1620_; uint8_t v_isModule_1621_; 
v___x_1615_ = lean_st_ref_get(v_a_1613_);
v_env_1619_ = lean_ctor_get(v___x_1615_, 0);
lean_inc_ref(v_env_1619_);
lean_dec(v___x_1615_);
v___x_1620_ = l_Lean_Environment_header(v_env_1619_);
lean_dec_ref(v_env_1619_);
v_isModule_1621_ = lean_ctor_get_uint8(v___x_1620_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1620_);
if (v_isModule_1621_ == 0)
{
lean_dec(v_declName_1610_);
lean_dec(v_attrName_1609_);
goto v___jp_1616_;
}
else
{
uint8_t v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = 1;
v___x_1623_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1611_, v___x_1622_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; lean_object* v___f_1625_; lean_object* v___x_1626_; 
v___x_1624_ = lean_box(v_isModule_1621_);
v___f_1625_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1625_, 0, v_declName_1610_);
lean_closure_set(v___f_1625_, 1, v___x_1624_);
lean_closure_set(v___f_1625_, 2, v_attrName_1609_);
v___x_1626_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1625_, v_isModule_1621_, v_a_1612_, v_a_1613_);
return v___x_1626_;
}
else
{
lean_dec(v_declName_1610_);
lean_dec(v_attrName_1609_);
goto v___jp_1616_;
}
}
v___jp_1616_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = lean_box(0);
v___x_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
return v___x_1618_;
}
}
}
LEAN_EXPORT void l_Lean_ensureAttrDeclIsPublic_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_1609_ = stack[0].m_obj;
lean_object* v_declName_1610_ = stack[1].m_obj;
uint8_t v_attrKind_1611_ = stack[2].m_num;
lean_object* v_a_1612_ = stack[3].m_obj;
lean_object* v_a_1613_ = stack[4].m_obj;
lean_object* v_res_1627_;
v_res_1627_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1609_, v_declName_1610_, v_attrKind_1611_, v_a_1612_, v_a_1613_);
stack->m_obj
 = v_res_1627_;
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1628_, lean_object* v_declName_1629_, lean_object* v_attrKind_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
uint8_t v_attrKind_boxed_1634_; lean_object* v_res_1635_; 
v_attrKind_boxed_1634_ = lean_unbox(v_attrKind_1630_);
v_res_1635_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1628_, v_declName_1629_, v_attrKind_boxed_1634_, v_a_1631_, v_a_1632_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
return v_res_1635_;
}
}
lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1636_, v___y_1637_);
return v___x_1640_;
}
}
LEAN_EXPORT void l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_1636_ = stack[0].m_obj;
lean_object* v___y_1637_ = stack[1].m_obj;
lean_object* v___y_1638_ = stack[2].m_obj;
lean_object* v_res_1641_;
v_res_1641_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1636_, v___y_1637_, v___y_1638_);
stack->m_obj
 = v_res_1641_;
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec_ref(v_opt_1642_);
return v_res_1646_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1649_ = l_Lean_stringToMessageData(v___x_1648_);
return v___x_1649_;
}
}
lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1650_, lean_object* v_declName_1651_, uint8_t v_attrKind_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v___x_1656_; lean_object* v_env_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; uint8_t v_isModule_1660_; 
v___x_1656_ = lean_st_ref_get(v_a_1654_);
v_env_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc_ref(v_env_1657_);
lean_dec(v___x_1656_);
v___x_1658_ = lean_st_ref_get(v_a_1654_);
v___x_1659_ = l_Lean_Environment_header(v_env_1657_);
lean_dec_ref(v_env_1657_);
v_isModule_1660_ = lean_ctor_get_uint8(v___x_1659_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1659_);
if (v_isModule_1660_ == 0)
{
lean_object* v___x_1661_; 
lean_dec(v___x_1658_);
v___x_1661_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1650_, v_declName_1651_, v_attrKind_1652_, v_a_1653_, v_a_1654_);
return v___x_1661_;
}
else
{
lean_object* v_env_1662_; uint8_t v___x_1663_; 
v_env_1662_ = lean_ctor_get(v___x_1658_, 0);
lean_inc_ref(v_env_1662_);
lean_dec(v___x_1658_);
lean_inc(v_declName_1651_);
v___x_1663_ = l_Lean_isMarkedMeta(v_env_1662_, v_declName_1651_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1664_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1665_ = l_Lean_MessageData_ofName(v_attrName_1650_);
v___x_1666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1664_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1666_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
v___x_1669_ = l_Lean_MessageData_ofConstName(v_declName_1651_, v___x_1663_);
v___x_1670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1668_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1672_, v_a_1653_, v_a_1654_);
return v___x_1673_;
}
else
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1650_, v_declName_1651_, v_attrKind_1652_, v_a_1653_, v_a_1654_);
return v___x_1674_;
}
}
}
}
LEAN_EXPORT void l_Lean_ensureAttrDeclIsMeta_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_1650_ = stack[0].m_obj;
lean_object* v_declName_1651_ = stack[1].m_obj;
uint8_t v_attrKind_1652_ = stack[2].m_num;
lean_object* v_a_1653_ = stack[3].m_obj;
lean_object* v_a_1654_ = stack[4].m_obj;
lean_object* v_res_1675_;
v_res_1675_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1650_, v_declName_1651_, v_attrKind_1652_, v_a_1653_, v_a_1654_);
stack->m_obj
 = v_res_1675_;
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1676_, lean_object* v_declName_1677_, lean_object* v_attrKind_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
uint8_t v_attrKind_boxed_1682_; lean_object* v_res_1683_; 
v_attrKind_boxed_1682_ = lean_unbox(v_attrKind_1678_);
v_res_1683_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1676_, v_declName_1677_, v_attrKind_boxed_1682_, v_a_1679_, v_a_1680_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
return v_res_1683_;
}
}
lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedTagAttribute_default___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1687_ = stack[0].m_obj;
lean_object* v___y_1688_ = stack[1].m_obj;
lean_object* v_res_1692_;
v_res_1692_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1687_, v___y_1688_);
stack->m_obj
 = v_res_1692_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1693_, v___y_1694_);
lean_dec_ref(v___y_1694_);
lean_dec_ref(v_x_1693_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1697_, lean_object* v_x_1698_){
_start:
{
lean_inc(v_s_1697_);
return v_s_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1699_, lean_object* v_x_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1699_, v_x_1700_);
lean_dec(v_x_1700_);
lean_dec(v_s_1699_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1706_, lean_object* v_x_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1709_, lean_object* v_x_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1709_, v_x_1710_);
lean_dec(v_x_1710_);
lean_dec_ref(v_x_1709_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1712_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = lean_box(0);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1714_);
lean_dec(v_x_1714_);
return v_res_1715_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_1720_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1721_; lean_object* v___f_1722_; lean_object* v___f_1723_; lean_object* v___f_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___f_1721_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1722_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1723_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1724_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1725_ = lean_box(0);
v___x_1726_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1727_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
lean_ctor_set(v___x_1727_, 1, v___x_1725_);
lean_ctor_set(v___x_1727_, 2, v___f_1724_);
lean_ctor_set(v___x_1727_, 3, v___f_1723_);
lean_ctor_set(v___x_1727_, 4, v___f_1722_);
lean_ctor_set(v___x_1727_, 5, v___f_1721_);
return v___x_1727_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1728_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1729_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
lean_ctor_set(v___x_1730_, 1, v___x_1728_);
return v___x_1730_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1731_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1732_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_registerTagAttribute___lam__0(v_x_1736_);
lean_dec(v_x_1736_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1738_, lean_object* v_x_1739_, lean_object* v_x_1740_){
_start:
{
if (lean_obj_tag(v_x_1740_) == 0)
{
return v_x_1739_;
}
else
{
lean_object* v_head_1741_; lean_object* v_tail_1742_; uint8_t v___x_1743_; 
v_head_1741_ = lean_ctor_get(v_x_1740_, 0);
lean_inc(v_head_1741_);
v_tail_1742_ = lean_ctor_get(v_x_1740_, 1);
lean_inc(v_tail_1742_);
lean_dec_ref_known(v_x_1740_, 2);
v___x_1743_ = l_Lean_NameSet_contains(v_newState_1738_, v_head_1741_);
if (v___x_1743_ == 0)
{
lean_dec(v_head_1741_);
v_x_1740_ = v_tail_1742_;
goto _start;
}
else
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_NameSet_insert(v_x_1739_, v_head_1741_);
v_x_1739_ = v___x_1745_;
v_x_1740_ = v_tail_1742_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1747_, lean_object* v_x_1748_, lean_object* v_x_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1747_, v_x_1748_, v_x_1749_);
lean_dec(v_newState_1747_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1751_, lean_object* v_newState_1752_, lean_object* v_newConsts_1753_, lean_object* v_s_1754_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1752_, v_s_1754_, v_newConsts_1753_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1756_, lean_object* v_newState_1757_, lean_object* v_newConsts_1758_, lean_object* v_s_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_registerTagAttribute___lam__1(v_x_1756_, v_newState_1757_, v_newConsts_1758_, v_s_1759_);
lean_dec(v_newState_1757_);
lean_dec(v_x_1756_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1773_){
_start:
{
lean_object* v___x_1774_; lean_object* v___y_1776_; 
v___x_1774_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1773_) == 0)
{
lean_object* v_size_1780_; 
v_size_1780_ = lean_ctor_get(v_s_1773_, 0);
lean_inc(v_size_1780_);
lean_dec_ref_known(v_s_1773_, 5);
v___y_1776_ = v_size_1780_;
goto v___jp_1775_;
}
else
{
lean_object* v___x_1781_; 
v___x_1781_ = lean_unsigned_to_nat(0u);
v___y_1776_ = v___x_1781_;
goto v___jp_1775_;
}
v___jp_1775_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1777_ = l_Nat_reprFast(v___y_1776_);
v___x_1778_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
v___x_1779_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1774_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
return v___x_1779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1782_, lean_object* v_pivot_1783_, lean_object* v_as_1784_, lean_object* v_i_1785_, lean_object* v_k_1786_){
_start:
{
uint8_t v___x_1787_; 
v___x_1787_ = lean_nat_dec_lt(v_k_1786_, v_hi_1782_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
lean_dec(v_k_1786_);
v___x_1788_ = lean_array_fswap(v_as_1784_, v_i_1785_, v_hi_1782_);
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v_i_1785_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
return v___x_1789_;
}
else
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = lean_array_fget_borrowed(v_as_1784_, v_k_1786_);
v___x_1791_ = l_Lean_Name_quickLt(v___x_1790_, v_pivot_1783_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = lean_unsigned_to_nat(1u);
v___x_1793_ = lean_nat_add(v_k_1786_, v___x_1792_);
lean_dec(v_k_1786_);
v_k_1786_ = v___x_1793_;
goto _start;
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1795_ = lean_array_fswap(v_as_1784_, v_i_1785_, v_k_1786_);
v___x_1796_ = lean_unsigned_to_nat(1u);
v___x_1797_ = lean_nat_add(v_i_1785_, v___x_1796_);
lean_dec(v_i_1785_);
v___x_1798_ = lean_nat_add(v_k_1786_, v___x_1796_);
lean_dec(v_k_1786_);
v_as_1784_ = v___x_1795_;
v_i_1785_ = v___x_1797_;
v_k_1786_ = v___x_1798_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1800_, lean_object* v_pivot_1801_, lean_object* v_as_1802_, lean_object* v_i_1803_, lean_object* v_k_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1800_, v_pivot_1801_, v_as_1802_, v_i_1803_, v_k_1804_);
lean_dec(v_pivot_1801_);
lean_dec(v_hi_1800_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1806_, lean_object* v_as_1807_, lean_object* v_lo_1808_, lean_object* v_hi_1809_){
_start:
{
lean_object* v___y_1811_; uint8_t v___x_1821_; 
v___x_1821_ = lean_nat_dec_lt(v_lo_1808_, v_hi_1809_);
if (v___x_1821_ == 0)
{
lean_dec(v_lo_1808_);
return v_as_1807_;
}
else
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v_mid_1824_; lean_object* v___y_1826_; lean_object* v___y_1832_; lean_object* v___x_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1822_ = lean_nat_add(v_lo_1808_, v_hi_1809_);
v___x_1823_ = lean_unsigned_to_nat(1u);
v_mid_1824_ = lean_nat_shiftr(v___x_1822_, v___x_1823_);
lean_dec(v___x_1822_);
v___x_1837_ = lean_array_fget_borrowed(v_as_1807_, v_mid_1824_);
v___x_1838_ = lean_array_fget_borrowed(v_as_1807_, v_lo_1808_);
v___x_1839_ = l_Lean_Name_quickLt(v___x_1837_, v___x_1838_);
if (v___x_1839_ == 0)
{
v___y_1832_ = v_as_1807_;
goto v___jp_1831_;
}
else
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_array_fswap(v_as_1807_, v_lo_1808_, v_mid_1824_);
v___y_1832_ = v___x_1840_;
goto v___jp_1831_;
}
v___jp_1825_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1827_ = lean_array_fget_borrowed(v___y_1826_, v_mid_1824_);
v___x_1828_ = lean_array_fget_borrowed(v___y_1826_, v_hi_1809_);
v___x_1829_ = l_Lean_Name_quickLt(v___x_1827_, v___x_1828_);
if (v___x_1829_ == 0)
{
lean_dec(v_mid_1824_);
v___y_1811_ = v___y_1826_;
goto v___jp_1810_;
}
else
{
lean_object* v___x_1830_; 
v___x_1830_ = lean_array_fswap(v___y_1826_, v_mid_1824_, v_hi_1809_);
lean_dec(v_mid_1824_);
v___y_1811_ = v___x_1830_;
goto v___jp_1810_;
}
}
v___jp_1831_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1833_ = lean_array_fget_borrowed(v___y_1832_, v_hi_1809_);
v___x_1834_ = lean_array_fget_borrowed(v___y_1832_, v_lo_1808_);
v___x_1835_ = l_Lean_Name_quickLt(v___x_1833_, v___x_1834_);
if (v___x_1835_ == 0)
{
v___y_1826_ = v___y_1832_;
goto v___jp_1825_;
}
else
{
lean_object* v___x_1836_; 
v___x_1836_ = lean_array_fswap(v___y_1832_, v_lo_1808_, v_hi_1809_);
v___y_1826_ = v___x_1836_;
goto v___jp_1825_;
}
}
}
v___jp_1810_:
{
lean_object* v_pivot_1812_; lean_object* v___x_1813_; lean_object* v_fst_1814_; lean_object* v_snd_1815_; uint8_t v___x_1816_; 
v_pivot_1812_ = lean_array_fget(v___y_1811_, v_hi_1809_);
lean_inc_n(v_lo_1808_, 2);
v___x_1813_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1809_, v_pivot_1812_, v___y_1811_, v_lo_1808_, v_lo_1808_);
lean_dec(v_pivot_1812_);
v_fst_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_fst_1814_);
v_snd_1815_ = lean_ctor_get(v___x_1813_, 1);
lean_inc(v_snd_1815_);
lean_dec_ref(v___x_1813_);
v___x_1816_ = lean_nat_dec_le(v_hi_1809_, v_fst_1814_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1806_, v_snd_1815_, v_lo_1808_, v_fst_1814_);
v___x_1818_ = lean_unsigned_to_nat(1u);
v___x_1819_ = lean_nat_add(v_fst_1814_, v___x_1818_);
lean_dec(v_fst_1814_);
v_as_1807_ = v___x_1817_;
v_lo_1808_ = v___x_1819_;
goto _start;
}
else
{
lean_dec(v_fst_1814_);
lean_dec(v_lo_1808_);
return v_snd_1815_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1841_, lean_object* v_as_1842_, lean_object* v_lo_1843_, lean_object* v_hi_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1841_, v_as_1842_, v_lo_1843_, v_hi_1844_);
lean_dec(v_hi_1844_);
lean_dec(v_n_1841_);
return v_res_1845_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1846_, lean_object* v_as_1847_, size_t v_i_1848_, size_t v_stop_1849_, lean_object* v_b_1850_){
_start:
{
lean_object* v___y_1852_; uint8_t v___x_1856_; 
v___x_1856_ = lean_usize_dec_eq(v_i_1848_, v_stop_1849_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; uint8_t v___x_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; 
v___x_1857_ = lean_array_uget_borrowed(v_as_1847_, v_i_1848_);
v___x_1858_ = 1;
lean_inc_ref(v_env_1846_);
v___x_1859_ = l_Lean_Environment_setExporting(v_env_1846_, v___x_1858_);
lean_inc(v___x_1857_);
v___x_1860_ = l_Lean_Environment_contains(v___x_1859_, v___x_1857_, v___x_1858_);
if (v___x_1860_ == 0)
{
v___y_1852_ = v_b_1850_;
goto v___jp_1851_;
}
else
{
lean_object* v___x_1861_; 
lean_inc(v___x_1857_);
v___x_1861_ = lean_array_push(v_b_1850_, v___x_1857_);
v___y_1852_ = v___x_1861_;
goto v___jp_1851_;
}
}
else
{
lean_dec_ref(v_env_1846_);
return v_b_1850_;
}
v___jp_1851_:
{
size_t v___x_1853_; size_t v___x_1854_; 
v___x_1853_ = ((size_t)1ULL);
v___x_1854_ = lean_usize_add(v_i_1848_, v___x_1853_);
v_i_1848_ = v___x_1854_;
v_b_1850_ = v___y_1852_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1846_ = stack[0].m_obj;
lean_object* v_as_1847_ = stack[1].m_obj;
size_t v_i_1848_ = stack[2].m_num;
size_t v_stop_1849_ = stack[3].m_num;
lean_object* v_b_1850_ = stack[4].m_obj;
lean_object* v_res_1862_;
v_res_1862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1846_, v_as_1847_, v_i_1848_, v_stop_1849_, v_b_1850_);
stack->m_obj
 = v_res_1862_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1863_, lean_object* v_as_1864_, lean_object* v_i_1865_, lean_object* v_stop_1866_, lean_object* v_b_1867_){
_start:
{
size_t v_i_boxed_1868_; size_t v_stop_boxed_1869_; lean_object* v_res_1870_; 
v_i_boxed_1868_ = lean_unbox_usize(v_i_1865_);
lean_dec(v_i_1865_);
v_stop_boxed_1869_ = lean_unbox_usize(v_stop_1866_);
lean_dec(v_stop_1866_);
v_res_1870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1863_, v_as_1864_, v_i_boxed_1868_, v_stop_boxed_1869_, v_b_1867_);
lean_dec_ref(v_as_1864_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1871_, lean_object* v_x_1872_){
_start:
{
if (lean_obj_tag(v_x_1872_) == 0)
{
lean_object* v_k_1873_; lean_object* v_l_1874_; lean_object* v_r_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_k_1873_ = lean_ctor_get(v_x_1872_, 1);
lean_inc(v_k_1873_);
v_l_1874_ = lean_ctor_get(v_x_1872_, 3);
lean_inc(v_l_1874_);
v_r_1875_ = lean_ctor_get(v_x_1872_, 4);
lean_inc(v_r_1875_);
lean_dec_ref_known(v_x_1872_, 5);
v___x_1876_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1871_, v_l_1874_);
v___x_1877_ = lean_array_push(v___x_1876_, v_k_1873_);
v_init_1871_ = v___x_1877_;
v_x_1872_ = v_r_1875_;
goto _start;
}
else
{
return v_init_1871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1879_, lean_object* v_es_1880_){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___y_1884_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___y_1901_; lean_object* v___y_1902_; uint8_t v___x_1904_; 
v___x_1881_ = lean_unsigned_to_nat(0u);
v___x_1882_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1898_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1882_, v_es_1880_);
v___x_1899_ = lean_array_get_size(v___x_1898_);
v___x_1904_ = lean_nat_dec_eq(v___x_1899_, v___x_1881_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___y_1908_; uint8_t v___x_1910_; 
v___x_1905_ = lean_unsigned_to_nat(1u);
v___x_1906_ = lean_nat_sub(v___x_1899_, v___x_1905_);
v___x_1910_ = lean_nat_dec_le(v___x_1881_, v___x_1906_);
if (v___x_1910_ == 0)
{
lean_inc(v___x_1906_);
v___y_1908_ = v___x_1906_;
goto v___jp_1907_;
}
else
{
v___y_1908_ = v___x_1881_;
goto v___jp_1907_;
}
v___jp_1907_:
{
uint8_t v___x_1909_; 
v___x_1909_ = lean_nat_dec_le(v___y_1908_, v___x_1906_);
if (v___x_1909_ == 0)
{
lean_dec(v___x_1906_);
lean_inc(v___y_1908_);
v___y_1901_ = v___y_1908_;
v___y_1902_ = v___y_1908_;
goto v___jp_1900_;
}
else
{
v___y_1901_ = v___y_1908_;
v___y_1902_ = v___x_1906_;
goto v___jp_1900_;
}
}
}
else
{
v___y_1884_ = v___x_1898_;
goto v___jp_1883_;
}
v___jp_1883_:
{
lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___x_1885_ = lean_array_get_size(v___y_1884_);
v___x_1886_ = lean_nat_dec_lt(v___x_1881_, v___x_1885_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; 
lean_dec_ref(v_env_1879_);
v___x_1887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1882_);
lean_ctor_set(v___x_1887_, 1, v___x_1882_);
lean_ctor_set(v___x_1887_, 2, v___y_1884_);
return v___x_1887_;
}
else
{
uint8_t v___x_1888_; 
v___x_1888_ = lean_nat_dec_le(v___x_1885_, v___x_1885_);
if (v___x_1888_ == 0)
{
if (v___x_1886_ == 0)
{
lean_object* v___x_1889_; 
lean_dec_ref(v_env_1879_);
v___x_1889_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1882_);
lean_ctor_set(v___x_1889_, 1, v___x_1882_);
lean_ctor_set(v___x_1889_, 2, v___y_1884_);
return v___x_1889_;
}
else
{
size_t v___x_1890_; size_t v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1890_ = ((size_t)0ULL);
v___x_1891_ = lean_usize_of_nat(v___x_1885_);
v___x_1892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1879_, v___y_1884_, v___x_1890_, v___x_1891_, v___x_1882_);
lean_inc_ref(v___x_1892_);
v___x_1893_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
lean_ctor_set(v___x_1893_, 2, v___y_1884_);
return v___x_1893_;
}
}
else
{
size_t v___x_1894_; size_t v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1894_ = ((size_t)0ULL);
v___x_1895_ = lean_usize_of_nat(v___x_1885_);
v___x_1896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1879_, v___y_1884_, v___x_1894_, v___x_1895_, v___x_1882_);
lean_inc_ref(v___x_1896_);
v___x_1897_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
lean_ctor_set(v___x_1897_, 2, v___y_1884_);
return v___x_1897_;
}
}
}
v___jp_1900_:
{
lean_object* v___x_1903_; 
v___x_1903_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1899_, v___x_1898_, v___y_1901_, v___y_1902_);
lean_dec(v___y_1902_);
v___y_1884_ = v___x_1903_;
goto v___jp_1883_;
}
}
}
lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v_name_1911_, lean_object* v_decl_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1916_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1917_ = l_Lean_MessageData_ofName(v_name_1911_);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1920_, v___y_1913_, v___y_1914_);
return v___x_1921_;
}
}
LEAN_EXPORT void l_Lean_registerTagAttribute___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1911_ = stack[0].m_obj;
lean_object* v_decl_1912_ = stack[1].m_obj;
lean_object* v___y_1913_ = stack[2].m_obj;
lean_object* v___y_1914_ = stack[3].m_obj;
lean_object* v_res_1922_;
v_res_1922_ = l_Lean_registerTagAttribute___lam__4(v_name_1911_, v_decl_1912_, v___y_1913_, v___y_1914_);
stack->m_obj
 = v_res_1922_;
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v_name_1923_, lean_object* v_decl_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Lean_registerTagAttribute___lam__4(v_name_1923_, v_decl_1924_, v___y_1925_, v___y_1926_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v_decl_1924_);
return v_res_1928_;
}
}
lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1929_, lean_object* v_x_1930_, lean_object* v_x_1931_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1929_);
return v___x_1933_;
}
}
LEAN_EXPORT void l_Lean_registerTagAttribute___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1929_ = stack[0].m_obj;
lean_object* v_x_1930_ = stack[1].m_obj;
lean_object* v_x_1931_ = stack[2].m_obj;
lean_object* v_res_1934_;
v_res_1934_ = l_Lean_registerTagAttribute___lam__5(v___x_1929_, v_x_1930_, v_x_1931_);
stack->m_obj
 = v_res_1934_;
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1935_, lean_object* v_x_1936_, lean_object* v_x_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Lean_registerTagAttribute___lam__5(v___x_1935_, v_x_1936_, v_x_1937_);
lean_dec_ref(v_x_1937_);
lean_dec_ref(v_x_1936_);
return v_res_1939_;
}
}
lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v___x_1940_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1940_);
return v___x_1942_;
}
}
LEAN_EXPORT void l_Lean_registerTagAttribute___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1940_ = stack[0].m_obj;
lean_object* v_res_1943_;
v_res_1943_ = l_Lean_registerTagAttribute___lam__6(v___x_1940_);
stack->m_obj
 = v_res_1943_;
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v___x_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Lean_registerTagAttribute___lam__6(v___x_1944_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_a_1947_, lean_object* v_decl_1948_, lean_object* v_s_1949_){
_start:
{
lean_object* v_addEntryFn_1950_; lean_object* v_importedEntries_1951_; lean_object* v_state_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1960_; 
v_addEntryFn_1950_ = lean_ctor_get(v_a_1947_, 3);
lean_inc(v_addEntryFn_1950_);
lean_dec_ref(v_a_1947_);
v_importedEntries_1951_ = lean_ctor_get(v_s_1949_, 0);
v_state_1952_ = lean_ctor_get(v_s_1949_, 1);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_s_1949_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1954_ = v_s_1949_;
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_state_1952_);
lean_inc(v_importedEntries_1951_);
lean_dec(v_s_1949_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v_state_1956_; lean_object* v___x_1958_; 
v_state_1956_ = lean_apply_2(v_addEntryFn_1950_, v_state_1952_, v_decl_1948_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 1, v_state_1956_);
v___x_1958_ = v___x_1954_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_importedEntries_1951_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_state_1956_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1961_, lean_object* v_declName_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1966_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1967_ = l_Lean_MessageData_ofName(v_attrName_1961_);
v___x_1968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1966_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1968_);
lean_ctor_set(v___x_1970_, 1, v___x_1969_);
v___x_1971_ = 0;
v___x_1972_ = l_Lean_MessageData_ofConstName(v_declName_1962_, v___x_1971_);
v___x_1973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1970_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
v___x_1974_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1973_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1975_, v___y_1963_, v___y_1964_);
return v___x_1976_;
}
}
LEAN_EXPORT void l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_1961_ = stack[0].m_obj;
lean_object* v_declName_1962_ = stack[1].m_obj;
lean_object* v___y_1963_ = stack[2].m_obj;
lean_object* v___y_1964_ = stack[3].m_obj;
lean_object* v_res_1977_;
v_res_1977_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1961_, v_declName_1962_, v___y_1963_, v___y_1964_);
stack->m_obj
 = v_res_1977_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1978_, lean_object* v_declName_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1978_, v_declName_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
return v_res_1983_;
}
}
lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1984_, lean_object* v_declName_1985_, lean_object* v_asyncPrefix_x3f_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v___y_1991_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1986_) == 0)
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_MessageData_nil;
v___y_1991_ = v___x_2004_;
goto v___jp_1990_;
}
else
{
lean_object* v_val_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v_val_2005_ = lean_ctor_get(v_asyncPrefix_x3f_1986_, 0);
lean_inc(v_val_2005_);
lean_dec_ref_known(v_asyncPrefix_x3f_1986_, 1);
v___x_2006_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_2007_ = l_Lean_MessageData_ofName(v_val_2005_);
v___x_2008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2006_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_2010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2008_);
lean_ctor_set(v___x_2010_, 1, v___x_2009_);
v___y_1991_ = v___x_2010_;
goto v___jp_1990_;
}
v___jp_1990_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_1992_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1993_ = l_Lean_MessageData_ofName(v_attrName_1984_);
v___x_1994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1994_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = 0;
v___x_1998_ = l_Lean_MessageData_ofConstName(v_declName_1985_, v___x_1997_);
v___x_1999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1996_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v___x_2000_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_2001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1999_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
lean_ctor_set(v___x_2002_, 1, v___y_1991_);
v___x_2003_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2002_, v___y_1987_, v___y_1988_);
return v___x_2003_;
}
}
}
LEAN_EXPORT void l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_1984_ = stack[0].m_obj;
lean_object* v_declName_1985_ = stack[1].m_obj;
lean_object* v_asyncPrefix_x3f_1986_ = stack[2].m_obj;
lean_object* v___y_1987_ = stack[3].m_obj;
lean_object* v___y_1988_ = stack[4].m_obj;
lean_object* v_res_2011_;
v_res_2011_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1984_, v_declName_1985_, v_asyncPrefix_x3f_1986_, v___y_1987_, v___y_1988_);
stack->m_obj
 = v_res_2011_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_2012_, lean_object* v_declName_2013_, lean_object* v_asyncPrefix_x3f_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2012_, v_declName_2013_, v_asyncPrefix_x3f_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
return v_res_2018_;
}
}
lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_2019_, uint8_t v_kind_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___y_2030_; 
v___x_2024_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_2025_ = l_Lean_MessageData_ofName(v_name_2019_);
v___x_2026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2024_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
v___x_2027_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_2028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2026_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
switch(v_kind_2020_)
{
case 0:
{
lean_object* v___x_2037_; 
v___x_2037_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_2030_ = v___x_2037_;
goto v___jp_2029_;
}
case 1:
{
lean_object* v___x_2038_; 
v___x_2038_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_2030_ = v___x_2038_;
goto v___jp_2029_;
}
default: 
{
lean_object* v___x_2039_; 
v___x_2039_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_2030_ = v___x_2039_;
goto v___jp_2029_;
}
}
v___jp_2029_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
lean_inc_ref(v___y_2030_);
v___x_2031_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___y_2030_);
v___x_2032_ = l_Lean_MessageData_ofFormat(v___x_2031_);
v___x_2033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2028_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_2035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2033_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
v___x_2036_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2035_, v___y_2021_, v___y_2022_);
return v___x_2036_;
}
}
}
LEAN_EXPORT void l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2019_ = stack[0].m_obj;
uint8_t v_kind_2020_ = stack[1].m_num;
lean_object* v___y_2021_ = stack[2].m_obj;
lean_object* v___y_2022_ = stack[3].m_obj;
lean_object* v_res_2040_;
v_res_2040_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2019_, v_kind_2020_, v___y_2021_, v___y_2022_);
stack->m_obj
 = v_res_2040_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_2041_, lean_object* v_kind_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
uint8_t v_kind_boxed_2046_; lean_object* v_res_2047_; 
v_kind_boxed_2046_ = lean_unbox(v_kind_2042_);
v_res_2047_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2041_, v_kind_boxed_2046_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
return v_res_2047_;
}
}
lean_object* l_Lean_registerTagAttribute___lam__8(lean_object* v_a_2048_, lean_object* v_validate_2049_, lean_object* v_name_2050_, lean_object* v_decl_2051_, lean_object* v_stx_2052_, uint8_t v_kind_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v_nextMacroScope_2058_; lean_object* v_ngen_2059_; lean_object* v_auxDeclNGen_2060_; lean_object* v_traceState_2061_; lean_object* v_recordedDeps_2062_; lean_object* v_messages_2063_; lean_object* v_infoState_2064_; lean_object* v_snapshotTasks_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___f_2073_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___x_2110_; 
lean_inc(v_decl_2051_);
lean_inc_ref(v_a_2048_);
v___f_2073_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7), 3, 2);
lean_closure_set(v___f_2073_, 0, v_a_2048_);
lean_closure_set(v___f_2073_, 1, v_decl_2051_);
v___x_2110_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2052_, v___y_2054_, v___y_2055_);
if (lean_obj_tag(v___x_2110_) == 0)
{
uint8_t v___x_2111_; uint8_t v___x_2112_; 
lean_dec_ref_known(v___x_2110_, 1);
v___x_2111_ = 0;
v___x_2112_ = l_Lean_instBEqAttributeKind_beq(v_kind_2053_, v___x_2111_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; 
lean_dec_ref(v___f_2073_);
lean_dec(v_decl_2051_);
lean_dec_ref(v_validate_2049_);
lean_dec_ref(v_a_2048_);
v___x_2113_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2050_, v_kind_2053_, v___y_2054_, v___y_2055_);
return v___x_2113_;
}
else
{
goto v___jp_2105_;
}
}
else
{
lean_dec_ref(v___f_2073_);
lean_dec(v_decl_2051_);
lean_dec(v_name_2050_);
lean_dec_ref(v_validate_2049_);
lean_dec_ref(v_a_2048_);
return v___x_2110_;
}
v___jp_2057_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2069_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_2070_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2070_, 0, v___y_2068_);
lean_ctor_set(v___x_2070_, 1, v_nextMacroScope_2058_);
lean_ctor_set(v___x_2070_, 2, v_ngen_2059_);
lean_ctor_set(v___x_2070_, 3, v_auxDeclNGen_2060_);
lean_ctor_set(v___x_2070_, 4, v_traceState_2061_);
lean_ctor_set(v___x_2070_, 5, v___x_2069_);
lean_ctor_set(v___x_2070_, 6, v_recordedDeps_2062_);
lean_ctor_set(v___x_2070_, 7, v_messages_2063_);
lean_ctor_set(v___x_2070_, 8, v_infoState_2064_);
lean_ctor_set(v___x_2070_, 9, v_snapshotTasks_2065_);
v___x_2071_ = lean_st_ref_put(v___y_2067_, v___x_2070_);
v___x_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2072_, 0, v___y_2066_);
return v___x_2072_;
}
v___jp_2074_:
{
lean_object* v___x_2077_; 
lean_inc(v___y_2076_);
lean_inc_ref(v___y_2075_);
lean_inc(v_decl_2051_);
v___x_2077_ = lean_apply_4(v_validate_2049_, v_decl_2051_, v___y_2075_, v___y_2076_, lean_box(0));
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v___x_2078_; lean_object* v_toEnvExtension_2079_; lean_object* v_env_2080_; lean_object* v_nextMacroScope_2081_; lean_object* v_ngen_2082_; lean_object* v_auxDeclNGen_2083_; lean_object* v_traceState_2084_; lean_object* v_recordedDeps_2085_; lean_object* v_messages_2086_; lean_object* v_infoState_2087_; lean_object* v_snapshotTasks_2088_; lean_object* v_asyncMode_2089_; uint8_t v_logWrites_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
lean_dec_ref_known(v___x_2077_, 1);
v___x_2078_ = lean_st_ref_take(v___y_2076_);
v_toEnvExtension_2079_ = lean_ctor_get(v_a_2048_, 0);
lean_inc_ref(v_toEnvExtension_2079_);
lean_dec_ref(v_a_2048_);
v_env_2080_ = lean_ctor_get(v___x_2078_, 0);
lean_inc_ref(v_env_2080_);
v_nextMacroScope_2081_ = lean_ctor_get(v___x_2078_, 1);
lean_inc(v_nextMacroScope_2081_);
v_ngen_2082_ = lean_ctor_get(v___x_2078_, 2);
lean_inc_ref(v_ngen_2082_);
v_auxDeclNGen_2083_ = lean_ctor_get(v___x_2078_, 3);
lean_inc_ref(v_auxDeclNGen_2083_);
v_traceState_2084_ = lean_ctor_get(v___x_2078_, 4);
lean_inc_ref(v_traceState_2084_);
v_recordedDeps_2085_ = lean_ctor_get(v___x_2078_, 6);
lean_inc_ref(v_recordedDeps_2085_);
v_messages_2086_ = lean_ctor_get(v___x_2078_, 7);
lean_inc_ref(v_messages_2086_);
v_infoState_2087_ = lean_ctor_get(v___x_2078_, 8);
lean_inc_ref(v_infoState_2087_);
v_snapshotTasks_2088_ = lean_ctor_get(v___x_2078_, 9);
lean_inc_ref(v_snapshotTasks_2088_);
lean_dec(v___x_2078_);
v_asyncMode_2089_ = lean_ctor_get(v_toEnvExtension_2079_, 2);
lean_inc(v_asyncMode_2089_);
v_logWrites_2090_ = lean_ctor_get_uint8(v_toEnvExtension_2079_, sizeof(void*)*6);
v___x_2091_ = lean_box(0);
v___x_2092_ = 1;
if (v_logWrites_2090_ == 0)
{
lean_object* v___x_2093_; 
v___x_2093_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2079_, v_env_2080_, v___f_2073_, v_asyncMode_2089_, v_decl_2051_, v___x_2092_);
lean_dec(v_asyncMode_2089_);
v_nextMacroScope_2058_ = v_nextMacroScope_2081_;
v_ngen_2059_ = v_ngen_2082_;
v_auxDeclNGen_2060_ = v_auxDeclNGen_2083_;
v_traceState_2061_ = v_traceState_2084_;
v_recordedDeps_2062_ = v_recordedDeps_2085_;
v_messages_2063_ = v_messages_2086_;
v_infoState_2064_ = v_infoState_2087_;
v_snapshotTasks_2065_ = v_snapshotTasks_2088_;
v___y_2066_ = v___x_2091_;
v___y_2067_ = v___y_2076_;
v___y_2068_ = v___x_2093_;
goto v___jp_2057_;
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
lean_inc(v_decl_2051_);
v___x_2094_ = l_Lean_Environment_logDeclChange(v_env_2080_, v_decl_2051_);
v___x_2095_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2079_, v___x_2094_, v___f_2073_, v_asyncMode_2089_, v_decl_2051_, v___x_2092_);
lean_dec(v_asyncMode_2089_);
v_nextMacroScope_2058_ = v_nextMacroScope_2081_;
v_ngen_2059_ = v_ngen_2082_;
v_auxDeclNGen_2060_ = v_auxDeclNGen_2083_;
v_traceState_2061_ = v_traceState_2084_;
v_recordedDeps_2062_ = v_recordedDeps_2085_;
v_messages_2063_ = v_messages_2086_;
v_infoState_2064_ = v_infoState_2087_;
v_snapshotTasks_2065_ = v_snapshotTasks_2088_;
v___y_2066_ = v___x_2091_;
v___y_2067_ = v___y_2076_;
v___y_2068_ = v___x_2095_;
goto v___jp_2057_;
}
}
else
{
lean_dec_ref(v___f_2073_);
lean_dec(v_decl_2051_);
lean_dec_ref(v_a_2048_);
return v___x_2077_;
}
}
v___jp_2096_:
{
lean_object* v_toEnvExtension_2100_; lean_object* v_asyncMode_2101_; uint8_t v___x_2102_; 
v_toEnvExtension_2100_ = lean_ctor_get(v_a_2048_, 0);
v_asyncMode_2101_ = lean_ctor_get(v_toEnvExtension_2100_, 2);
lean_inc(v_decl_2051_);
lean_inc_ref(v___y_2097_);
v___x_2102_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2097_, v_decl_2051_, v_asyncMode_2101_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
lean_dec_ref(v___f_2073_);
lean_dec_ref(v_validate_2049_);
lean_dec_ref(v_a_2048_);
v___x_2103_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2097_);
v___x_2104_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_2050_, v_decl_2051_, v___x_2103_, v___y_2098_, v___y_2099_);
return v___x_2104_;
}
else
{
lean_dec_ref(v___y_2097_);
lean_dec(v_name_2050_);
v___y_2075_ = v___y_2098_;
v___y_2076_ = v___y_2099_;
goto v___jp_2074_;
}
}
v___jp_2105_:
{
lean_object* v___x_2106_; lean_object* v_env_2107_; lean_object* v___x_2108_; 
v___x_2106_ = lean_st_ref_get(v___y_2055_);
v_env_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc_ref(v_env_2107_);
lean_dec(v___x_2106_);
v___x_2108_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2107_, v_decl_2051_);
if (lean_obj_tag(v___x_2108_) == 0)
{
v___y_2097_ = v_env_2107_;
v___y_2098_ = v___y_2054_;
v___y_2099_ = v___y_2055_;
goto v___jp_2096_;
}
else
{
lean_object* v___x_2109_; 
lean_dec_ref_known(v___x_2108_, 1);
lean_dec_ref(v_env_2107_);
lean_dec_ref(v___f_2073_);
lean_dec_ref(v_validate_2049_);
lean_dec_ref(v_a_2048_);
v___x_2109_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2050_, v_decl_2051_, v___y_2054_, v___y_2055_);
return v___x_2109_;
}
}
}
}
LEAN_EXPORT void l_Lean_registerTagAttribute___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2048_ = stack[0].m_obj;
lean_object* v_validate_2049_ = stack[1].m_obj;
lean_object* v_name_2050_ = stack[2].m_obj;
lean_object* v_decl_2051_ = stack[3].m_obj;
lean_object* v_stx_2052_ = stack[4].m_obj;
uint8_t v_kind_2053_ = stack[5].m_num;
lean_object* v___y_2054_ = stack[6].m_obj;
lean_object* v___y_2055_ = stack[7].m_obj;
lean_object* v_res_2114_;
v_res_2114_ = l_Lean_registerTagAttribute___lam__8(v_a_2048_, v_validate_2049_, v_name_2050_, v_decl_2051_, v_stx_2052_, v_kind_2053_, v___y_2054_, v___y_2055_);
stack->m_obj
 = v_res_2114_;
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__8___boxed(lean_object* v_a_2115_, lean_object* v_validate_2116_, lean_object* v_name_2117_, lean_object* v_decl_2118_, lean_object* v_stx_2119_, lean_object* v_kind_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
uint8_t v_kind_boxed_2124_; lean_object* v_res_2125_; 
v_kind_boxed_2124_ = lean_unbox(v_kind_2120_);
v_res_2125_ = l_Lean_registerTagAttribute___lam__8(v_a_2115_, v_validate_2116_, v_name_2117_, v_decl_2118_, v_stx_2119_, v_kind_boxed_2124_, v___y_2121_, v___y_2122_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
return v_res_2125_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2131_; lean_object* v___f_2132_; 
v___x_2131_ = l_Lean_NameSet_empty;
v___f_2132_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 4, 1);
lean_closure_set(v___f_2132_, 0, v___x_2131_);
return v___f_2132_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___f_2134_; 
v___x_2133_ = l_Lean_NameSet_empty;
v___f_2134_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 2, 1);
lean_closure_set(v___f_2134_, 0, v___x_2133_);
return v___f_2134_;
}
}
lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2137_, lean_object* v_descr_2138_, lean_object* v_validate_2139_, lean_object* v_ref_2140_, uint8_t v_applicationTime_2141_, lean_object* v_asyncMode_2142_, uint8_t v_logWrites_2143_){
_start:
{
lean_object* v___f_2145_; lean_object* v___f_2146_; lean_object* v___f_2147_; lean_object* v___f_2148_; lean_object* v___f_2149_; lean_object* v___f_2150_; lean_object* v___f_2151_; lean_object* v___x_2152_; uint8_t v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___f_2145_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2146_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2147_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2148_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
lean_inc(v_name_2137_);
v___f_2149_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 5, 1);
lean_closure_set(v___f_2149_, 0, v_name_2137_);
v___f_2150_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2151_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2152_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
v___x_2153_ = 0;
lean_inc(v_ref_2140_);
v___x_2154_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2154_, 0, v_ref_2140_);
lean_ctor_set(v___x_2154_, 1, v___f_2151_);
lean_ctor_set(v___x_2154_, 2, v___f_2150_);
lean_ctor_set(v___x_2154_, 3, v___f_2148_);
lean_ctor_set(v___x_2154_, 4, v___f_2147_);
lean_ctor_set(v___x_2154_, 5, v___f_2146_);
lean_ctor_set(v___x_2154_, 6, v_asyncMode_2142_);
lean_ctor_set(v___x_2154_, 7, v___x_2152_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*8, v___x_2153_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*8 + 1, v_logWrites_2143_);
v___x_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
lean_ctor_set(v___x_2155_, 1, v___f_2145_);
v___x_2156_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2155_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___f_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc_n(v_a_2157_, 2);
lean_dec_ref_known(v___x_2156_, 1);
lean_inc(v_name_2137_);
v___f_2158_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__8___boxed), 9, 3);
lean_closure_set(v___f_2158_, 0, v_a_2157_);
lean_closure_set(v___f_2158_, 1, v_validate_2139_);
lean_closure_set(v___f_2158_, 2, v_name_2137_);
v___x_2159_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2159_, 0, v_ref_2140_);
lean_ctor_set(v___x_2159_, 1, v_name_2137_);
lean_ctor_set(v___x_2159_, 2, v_descr_2138_);
lean_ctor_set_uint8(v___x_2159_, sizeof(void*)*3, v_applicationTime_2141_);
v___x_2160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
lean_ctor_set(v___x_2160_, 1, v___f_2158_);
lean_ctor_set(v___x_2160_, 2, v___f_2149_);
lean_inc_ref(v___x_2160_);
v___x_2161_ = l_Lean_registerBuiltinAttribute(v___x_2160_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2169_; 
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2169_ == 0)
{
lean_object* v_unused_2170_; 
v_unused_2170_ = lean_ctor_get(v___x_2161_, 0);
lean_dec(v_unused_2170_);
v___x_2163_ = v___x_2161_;
v_isShared_2164_ = v_isSharedCheck_2169_;
goto v_resetjp_2162_;
}
else
{
lean_dec(v___x_2161_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2169_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
v___x_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2160_);
lean_ctor_set(v___x_2165_, 1, v_a_2157_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2165_);
v___x_2167_ = v___x_2163_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec_ref_known(v___x_2160_, 3);
lean_dec(v_a_2157_);
v_a_2171_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2161_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2161_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec_ref(v___f_2149_);
lean_dec(v_ref_2140_);
lean_dec_ref(v_validate_2139_);
lean_dec_ref(v_descr_2138_);
lean_dec(v_name_2137_);
v_a_2179_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2156_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2156_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_registerTagAttribute_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2137_ = stack[0].m_obj;
lean_object* v_descr_2138_ = stack[1].m_obj;
lean_object* v_validate_2139_ = stack[2].m_obj;
lean_object* v_ref_2140_ = stack[3].m_obj;
uint8_t v_applicationTime_2141_ = stack[4].m_num;
lean_object* v_asyncMode_2142_ = stack[5].m_obj;
uint8_t v_logWrites_2143_ = stack[6].m_num;
lean_object* v_res_2187_;
v_res_2187_ = l_Lean_registerTagAttribute(v_name_2137_, v_descr_2138_, v_validate_2139_, v_ref_2140_, v_applicationTime_2141_, v_asyncMode_2142_, v_logWrites_2143_);
stack->m_obj
 = v_res_2187_;
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2188_, lean_object* v_descr_2189_, lean_object* v_validate_2190_, lean_object* v_ref_2191_, lean_object* v_applicationTime_2192_, lean_object* v_asyncMode_2193_, lean_object* v_logWrites_2194_, lean_object* v_a_2195_){
_start:
{
uint8_t v_applicationTime_boxed_2196_; uint8_t v_logWrites_boxed_2197_; lean_object* v_res_2198_; 
v_applicationTime_boxed_2196_ = lean_unbox(v_applicationTime_2192_);
v_logWrites_boxed_2197_ = lean_unbox(v_logWrites_2194_);
v_res_2198_ = l_Lean_registerTagAttribute(v_name_2188_, v_descr_2189_, v_validate_2190_, v_ref_2191_, v_applicationTime_boxed_2196_, v_asyncMode_2193_, v_logWrites_boxed_2197_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2199_, lean_object* v_t_2200_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2199_, v_t_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2202_, lean_object* v_as_2203_, lean_object* v_lo_2204_, lean_object* v_hi_2205_, lean_object* v_w_2206_, lean_object* v_hlo_2207_, lean_object* v_hhi_2208_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2202_, v_as_2203_, v_lo_2204_, v_hi_2205_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2210_, lean_object* v_as_2211_, lean_object* v_lo_2212_, lean_object* v_hi_2213_, lean_object* v_w_2214_, lean_object* v_hlo_2215_, lean_object* v_hhi_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2210_, v_as_2211_, v_lo_2212_, v_hi_2213_, v_w_2214_, v_hlo_2215_, v_hhi_2216_);
lean_dec(v_hi_2213_);
lean_dec(v_n_2210_);
return v_res_2217_;
}
}
lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2218_, lean_object* v_attrName_2219_, lean_object* v_declName_2220_, lean_object* v_asyncPrefix_x3f_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2219_, v_declName_2220_, v_asyncPrefix_x3f_2221_, v___y_2222_, v___y_2223_);
return v___x_2225_;
}
}
LEAN_EXPORT void l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_2219_ = stack[1].m_obj;
lean_object* v_declName_2220_ = stack[2].m_obj;
lean_object* v_asyncPrefix_x3f_2221_ = stack[3].m_obj;
lean_object* v___y_2222_ = stack[4].m_obj;
lean_object* v___y_2223_ = stack[5].m_obj;
lean_object* v_res_2226_;
v_res_2226_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_box(0), v_attrName_2219_, v_declName_2220_, v_asyncPrefix_x3f_2221_, v___y_2222_, v___y_2223_);
stack->m_obj
 = v_res_2226_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2227_, lean_object* v_attrName_2228_, lean_object* v_declName_2229_, lean_object* v_asyncPrefix_x3f_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2227_, v_attrName_2228_, v_declName_2229_, v_asyncPrefix_x3f_2230_, v___y_2231_, v___y_2232_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
return v_res_2234_;
}
}
lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2235_, lean_object* v_attrName_2236_, lean_object* v_declName_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2236_, v_declName_2237_, v___y_2238_, v___y_2239_);
return v___x_2241_;
}
}
LEAN_EXPORT void l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_2236_ = stack[1].m_obj;
lean_object* v_declName_2237_ = stack[2].m_obj;
lean_object* v___y_2238_ = stack[3].m_obj;
lean_object* v___y_2239_ = stack[4].m_obj;
lean_object* v_res_2242_;
v_res_2242_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_box(0), v_attrName_2236_, v_declName_2237_, v___y_2238_, v___y_2239_);
stack->m_obj
 = v_res_2242_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2243_, lean_object* v_attrName_2244_, lean_object* v_declName_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2243_, v_attrName_2244_, v_declName_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
return v_res_2249_;
}
}
lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2250_, lean_object* v_name_2251_, uint8_t v_kind_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2251_, v_kind_2252_, v___y_2253_, v___y_2254_);
return v___x_2256_;
}
}
LEAN_EXPORT void l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2251_ = stack[1].m_obj;
uint8_t v_kind_2252_ = stack[2].m_num;
lean_object* v___y_2253_ = stack[3].m_obj;
lean_object* v___y_2254_ = stack[4].m_obj;
lean_object* v_res_2257_;
v_res_2257_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_box(0), v_name_2251_, v_kind_2252_, v___y_2253_, v___y_2254_);
stack->m_obj
 = v_res_2257_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2258_, lean_object* v_name_2259_, lean_object* v_kind_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
uint8_t v_kind_boxed_2264_; lean_object* v_res_2265_; 
v_kind_boxed_2264_ = lean_unbox(v_kind_2260_);
v_res_2265_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2258_, v_name_2259_, v_kind_boxed_2264_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2266_, lean_object* v_lo_2267_, lean_object* v_hi_2268_, lean_object* v_hhi_2269_, lean_object* v_pivot_2270_, lean_object* v_as_2271_, lean_object* v_i_2272_, lean_object* v_k_2273_, lean_object* v_ilo_2274_, lean_object* v_ik_2275_, lean_object* v_w_2276_){
_start:
{
lean_object* v___x_2277_; 
v___x_2277_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2268_, v_pivot_2270_, v_as_2271_, v_i_2272_, v_k_2273_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2278_, lean_object* v_lo_2279_, lean_object* v_hi_2280_, lean_object* v_hhi_2281_, lean_object* v_pivot_2282_, lean_object* v_as_2283_, lean_object* v_i_2284_, lean_object* v_k_2285_, lean_object* v_ilo_2286_, lean_object* v_ik_2287_, lean_object* v_w_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2278_, v_lo_2279_, v_hi_2280_, v_hhi_2281_, v_pivot_2282_, v_as_2283_, v_i_2284_, v_k_2285_, v_ilo_2286_, v_ik_2287_, v_w_2288_);
lean_dec(v_pivot_2282_);
lean_dec(v_hi_2280_);
lean_dec(v_lo_2279_);
lean_dec(v_n_2278_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_addEntryFn_2290_, lean_object* v_decl_2291_, lean_object* v_s_2292_){
_start:
{
lean_object* v_importedEntries_2293_; lean_object* v_state_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2302_; 
v_importedEntries_2293_ = lean_ctor_get(v_s_2292_, 0);
v_state_2294_ = lean_ctor_get(v_s_2292_, 1);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_s_2292_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2296_ = v_s_2292_;
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_state_2294_);
lean_inc(v_importedEntries_2293_);
lean_dec(v_s_2292_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v_state_2298_; lean_object* v___x_2300_; 
v_state_2298_ = lean_apply_2(v_addEntryFn_2290_, v_state_2294_, v_decl_2291_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 1, v_state_2298_);
v___x_2300_ = v___x_2296_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_importedEntries_2293_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_state_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_attr_2303_, lean_object* v_decl_2304_, lean_object* v_env_2305_){
_start:
{
lean_object* v_ext_2306_; lean_object* v_toEnvExtension_2307_; lean_object* v_addEntryFn_2308_; lean_object* v_asyncMode_2309_; uint8_t v_logWrites_2310_; lean_object* v___f_2311_; uint8_t v___x_2312_; 
v_ext_2306_ = lean_ctor_get(v_attr_2303_, 1);
lean_inc_ref(v_ext_2306_);
lean_dec_ref(v_attr_2303_);
v_toEnvExtension_2307_ = lean_ctor_get(v_ext_2306_, 0);
lean_inc_ref(v_toEnvExtension_2307_);
v_addEntryFn_2308_ = lean_ctor_get(v_ext_2306_, 3);
lean_inc(v_addEntryFn_2308_);
lean_dec_ref(v_ext_2306_);
v_asyncMode_2309_ = lean_ctor_get(v_toEnvExtension_2307_, 2);
lean_inc(v_asyncMode_2309_);
v_logWrites_2310_ = lean_ctor_get_uint8(v_toEnvExtension_2307_, sizeof(void*)*6);
lean_inc(v_decl_2304_);
v___f_2311_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2311_, 0, v_addEntryFn_2308_);
lean_closure_set(v___f_2311_, 1, v_decl_2304_);
v___x_2312_ = 1;
if (v_logWrites_2310_ == 0)
{
lean_object* v___x_2313_; 
v___x_2313_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2307_, v_env_2305_, v___f_2311_, v_asyncMode_2309_, v_decl_2304_, v___x_2312_);
lean_dec(v_asyncMode_2309_);
return v___x_2313_;
}
else
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
lean_inc_ref(v_toEnvExtension_2307_);
v___x_2314_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2307_, v_env_2305_);
lean_dec_ref(v_env_2305_);
v___x_2315_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2307_, v___x_2314_, v___f_2311_, v_asyncMode_2309_, v_decl_2304_, v___x_2312_);
lean_dec(v_asyncMode_2309_);
return v___x_2315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_modifyEnv_2316_, lean_object* v___f_2317_, lean_object* v_____r_2318_){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = lean_apply_1(v_modifyEnv_2316_, v___f_2317_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v_attr_2320_, lean_object* v_env_2321_, lean_object* v_decl_2322_, lean_object* v_inst_2323_, lean_object* v_inst_2324_, lean_object* v_toBind_2325_, lean_object* v___f_2326_, lean_object* v_modifyEnv_2327_, lean_object* v___f_2328_, lean_object* v_____r_2329_){
_start:
{
lean_object* v_ext_2330_; lean_object* v_toEnvExtension_2331_; lean_object* v_attr_2332_; lean_object* v_asyncMode_2333_; uint8_t v___x_2334_; 
v_ext_2330_ = lean_ctor_get(v_attr_2320_, 1);
v_toEnvExtension_2331_ = lean_ctor_get(v_ext_2330_, 0);
lean_inc_ref(v_toEnvExtension_2331_);
v_attr_2332_ = lean_ctor_get(v_attr_2320_, 0);
lean_inc_ref(v_attr_2332_);
lean_dec_ref(v_attr_2320_);
v_asyncMode_2333_ = lean_ctor_get(v_toEnvExtension_2331_, 2);
lean_inc(v_asyncMode_2333_);
lean_dec_ref(v_toEnvExtension_2331_);
lean_inc(v_decl_2322_);
lean_inc_ref(v_env_2321_);
v___x_2334_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2321_, v_decl_2322_, v_asyncMode_2333_);
lean_dec(v_asyncMode_2333_);
if (v___x_2334_ == 0)
{
lean_object* v_toAttributeImplCore_2335_; lean_object* v_name_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
lean_dec_ref(v___f_2328_);
lean_dec(v_modifyEnv_2327_);
v_toAttributeImplCore_2335_ = lean_ctor_get(v_attr_2332_, 0);
lean_inc_ref(v_toAttributeImplCore_2335_);
lean_dec_ref(v_attr_2332_);
v_name_2336_ = lean_ctor_get(v_toAttributeImplCore_2335_, 1);
lean_inc(v_name_2336_);
lean_dec_ref(v_toAttributeImplCore_2335_);
v___x_2337_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2321_);
v___x_2338_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2323_, v_inst_2324_, v_name_2336_, v_decl_2322_, v___x_2337_);
v___x_2339_ = lean_apply_4(v_toBind_2325_, lean_box(0), lean_box(0), v___x_2338_, v___f_2326_);
return v___x_2339_;
}
else
{
lean_object* v___x_2340_; 
lean_dec_ref(v_attr_2332_);
lean_dec(v___f_2326_);
lean_dec(v_toBind_2325_);
lean_dec_ref(v_inst_2324_);
lean_dec_ref(v_inst_2323_);
lean_dec(v_decl_2322_);
lean_dec_ref(v_env_2321_);
v___x_2340_ = lean_apply_1(v_modifyEnv_2327_, v___f_2328_);
return v___x_2340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v___f_2341_, lean_object* v_____r_2342_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = lean_apply_1(v___f_2341_, v_____r_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__5(lean_object* v_attr_2344_, lean_object* v_decl_2345_, lean_object* v_inst_2346_, lean_object* v_inst_2347_, lean_object* v_toBind_2348_, lean_object* v___f_2349_, lean_object* v_modifyEnv_2350_, lean_object* v___f_2351_, lean_object* v_env_2352_){
_start:
{
lean_object* v___f_2353_; lean_object* v___x_2354_; 
lean_inc_ref(v___f_2351_);
lean_inc(v_modifyEnv_2350_);
lean_inc(v___f_2349_);
lean_inc(v_toBind_2348_);
lean_inc_ref(v_inst_2347_);
lean_inc_ref(v_inst_2346_);
lean_inc(v_decl_2345_);
lean_inc_ref(v_env_2352_);
lean_inc_ref(v_attr_2344_);
v___f_2353_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 10, 9);
lean_closure_set(v___f_2353_, 0, v_attr_2344_);
lean_closure_set(v___f_2353_, 1, v_env_2352_);
lean_closure_set(v___f_2353_, 2, v_decl_2345_);
lean_closure_set(v___f_2353_, 3, v_inst_2346_);
lean_closure_set(v___f_2353_, 4, v_inst_2347_);
lean_closure_set(v___f_2353_, 5, v_toBind_2348_);
lean_closure_set(v___f_2353_, 6, v___f_2349_);
lean_closure_set(v___f_2353_, 7, v_modifyEnv_2350_);
lean_closure_set(v___f_2353_, 8, v___f_2351_);
v___x_2354_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2352_, v_decl_2345_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
lean_dec_ref(v___f_2353_);
v___x_2355_ = lean_box(0);
v___x_2356_ = l_Lean_TagAttribute_setTag___redArg___lam__3(v_attr_2344_, v_env_2352_, v_decl_2345_, v_inst_2346_, v_inst_2347_, v_toBind_2348_, v___f_2349_, v_modifyEnv_2350_, v___f_2351_, v___x_2355_);
return v___x_2356_;
}
else
{
lean_object* v_attr_2357_; lean_object* v_toAttributeImplCore_2358_; lean_object* v_name_2359_; lean_object* v___f_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
lean_dec_ref_known(v___x_2354_, 1);
lean_dec_ref(v_env_2352_);
lean_dec_ref(v___f_2351_);
lean_dec(v_modifyEnv_2350_);
lean_dec(v___f_2349_);
v_attr_2357_ = lean_ctor_get(v_attr_2344_, 0);
lean_inc_ref(v_attr_2357_);
lean_dec_ref(v_attr_2344_);
v_toAttributeImplCore_2358_ = lean_ctor_get(v_attr_2357_, 0);
lean_inc_ref(v_toAttributeImplCore_2358_);
lean_dec_ref(v_attr_2357_);
v_name_2359_ = lean_ctor_get(v_toAttributeImplCore_2358_, 1);
lean_inc(v_name_2359_);
lean_dec_ref(v_toAttributeImplCore_2358_);
v___f_2360_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2360_, 0, v___f_2353_);
v___x_2361_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2346_, v_inst_2347_, v_name_2359_, v_decl_2345_);
v___x_2362_ = lean_apply_4(v_toBind_2348_, lean_box(0), lean_box(0), v___x_2361_, v___f_2360_);
return v___x_2362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2363_, lean_object* v_inst_2364_, lean_object* v_inst_2365_, lean_object* v_attr_2366_, lean_object* v_decl_2367_){
_start:
{
lean_object* v_toBind_2368_; lean_object* v_getEnv_2369_; lean_object* v_modifyEnv_2370_; lean_object* v___f_2371_; lean_object* v___f_2372_; lean_object* v___f_2373_; lean_object* v___x_2374_; 
v_toBind_2368_ = lean_ctor_get(v_inst_2363_, 1);
lean_inc_n(v_toBind_2368_, 2);
v_getEnv_2369_ = lean_ctor_get(v_inst_2365_, 0);
lean_inc(v_getEnv_2369_);
v_modifyEnv_2370_ = lean_ctor_get(v_inst_2365_, 1);
lean_inc_n(v_modifyEnv_2370_, 2);
lean_dec_ref(v_inst_2365_);
lean_inc(v_decl_2367_);
lean_inc_ref(v_attr_2366_);
v___f_2371_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2371_, 0, v_attr_2366_);
lean_closure_set(v___f_2371_, 1, v_decl_2367_);
lean_inc_ref(v___f_2371_);
v___f_2372_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2372_, 0, v_modifyEnv_2370_);
lean_closure_set(v___f_2372_, 1, v___f_2371_);
v___f_2373_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__5), 9, 8);
lean_closure_set(v___f_2373_, 0, v_attr_2366_);
lean_closure_set(v___f_2373_, 1, v_decl_2367_);
lean_closure_set(v___f_2373_, 2, v_inst_2363_);
lean_closure_set(v___f_2373_, 3, v_inst_2364_);
lean_closure_set(v___f_2373_, 4, v_toBind_2368_);
lean_closure_set(v___f_2373_, 5, v___f_2372_);
lean_closure_set(v___f_2373_, 6, v_modifyEnv_2370_);
lean_closure_set(v___f_2373_, 7, v___f_2371_);
v___x_2374_ = lean_apply_4(v_toBind_2368_, lean_box(0), lean_box(0), v_getEnv_2369_, v___f_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2375_, lean_object* v_inst_2376_, lean_object* v_inst_2377_, lean_object* v_inst_2378_, lean_object* v_attr_2379_, lean_object* v_decl_2380_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2376_, v_inst_2377_, v_inst_2378_, v_attr_2379_, v_decl_2380_);
return v___x_2381_;
}
}
uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v___y_2382_, lean_object* v_as_2383_, lean_object* v_k_2384_, lean_object* v_x_2385_, lean_object* v_x_2386_){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v_m_2389_; lean_object* v_a_2390_; uint8_t v___x_2391_; 
v___x_2387_ = lean_nat_add(v_x_2385_, v_x_2386_);
v___x_2388_ = lean_unsigned_to_nat(1u);
v_m_2389_ = lean_nat_shiftr(v___x_2387_, v___x_2388_);
lean_dec(v___x_2387_);
v_a_2390_ = lean_array_fget_borrowed(v_as_2383_, v_m_2389_);
v___x_2391_ = l_Lean_Name_quickLt(v_a_2390_, v_k_2384_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; uint8_t v___x_2393_; 
lean_dec(v_x_2386_);
v___x_2392_ = lean_unsigned_to_nat(0u);
v___x_2393_ = l_Lean_Name_quickLt(v_k_2384_, v_a_2390_);
if (v___x_2393_ == 0)
{
uint8_t v___x_2394_; 
lean_dec(v_m_2389_);
lean_dec(v_x_2385_);
v___x_2394_ = lean_nat_dec_le(v___x_2392_, v___y_2382_);
return v___x_2394_;
}
else
{
uint8_t v___x_2395_; 
v___x_2395_ = lean_nat_dec_eq(v_m_2389_, v___x_2392_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; uint8_t v___x_2397_; 
v___x_2396_ = lean_nat_sub(v_m_2389_, v___x_2388_);
lean_dec(v_m_2389_);
v___x_2397_ = lean_nat_dec_lt(v___x_2396_, v_x_2385_);
if (v___x_2397_ == 0)
{
v_x_2386_ = v___x_2396_;
goto _start;
}
else
{
lean_dec(v___x_2396_);
lean_dec(v_x_2385_);
return v___x_2395_;
}
}
else
{
lean_dec(v_m_2389_);
lean_dec(v_x_2385_);
return v___x_2391_;
}
}
}
else
{
lean_object* v___x_2399_; uint8_t v___x_2400_; 
lean_dec(v_x_2385_);
v___x_2399_ = lean_nat_add(v_m_2389_, v___x_2388_);
lean_dec(v_m_2389_);
v___x_2400_ = lean_nat_dec_le(v___x_2399_, v_x_2386_);
if (v___x_2400_ == 0)
{
lean_dec(v___x_2399_);
lean_dec(v_x_2386_);
return v___x_2400_;
}
else
{
v_x_2385_ = v___x_2399_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2382_ = stack[0].m_obj;
lean_object* v_as_2383_ = stack[1].m_obj;
lean_object* v_k_2384_ = stack[2].m_obj;
lean_object* v_x_2385_ = stack[3].m_obj;
lean_object* v_x_2386_ = stack[4].m_obj;
uint8_t v_res_2402_;
v_res_2402_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2382_, v_as_2383_, v_k_2384_, v_x_2385_, v_x_2386_);
stack->m_num = v_res_2402_;
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v___y_2403_, lean_object* v_as_2404_, lean_object* v_k_2405_, lean_object* v_x_2406_, lean_object* v_x_2407_){
_start:
{
uint8_t v_res_2408_; lean_object* v_r_2409_; 
v_res_2408_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2403_, v_as_2404_, v_k_2405_, v_x_2406_, v_x_2407_);
lean_dec(v_k_2405_);
lean_dec_ref(v_as_2404_);
lean_dec(v___y_2403_);
v_r_2409_ = lean_box(v_res_2408_);
return v_r_2409_;
}
}
uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2410_, lean_object* v_env_2411_, lean_object* v_decl_2412_){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = lean_box(1);
v___x_2414_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2411_, v_decl_2412_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_ext_2415_; lean_object* v_toEnvExtension_2416_; lean_object* v_asyncMode_2417_; uint8_t v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
v_ext_2415_ = lean_ctor_get(v_attr_2410_, 1);
v_toEnvExtension_2416_ = lean_ctor_get(v_ext_2415_, 0);
v_asyncMode_2417_ = lean_ctor_get(v_toEnvExtension_2416_, 2);
v___x_2418_ = 0;
lean_inc(v_decl_2412_);
v___x_2419_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2413_, v_ext_2415_, v_env_2411_, v_asyncMode_2417_, v_decl_2412_, v___x_2418_);
v___x_2420_ = l_Lean_NameSet_contains(v___x_2419_, v_decl_2412_);
lean_dec(v_decl_2412_);
lean_dec(v___x_2419_);
return v___x_2420_;
}
else
{
lean_object* v_val_2421_; lean_object* v_ext_2422_; uint8_t v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; 
v_val_2421_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_val_2421_);
lean_dec_ref_known(v___x_2414_, 1);
v_ext_2422_ = lean_ctor_get(v_attr_2410_, 1);
v___x_2423_ = 0;
v___x_2424_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2413_, v_ext_2422_, v_env_2411_, v_val_2421_, v___x_2423_);
lean_dec(v_val_2421_);
lean_dec_ref(v_env_2411_);
v___x_2425_ = lean_unsigned_to_nat(0u);
v___x_2426_ = lean_array_get_size(v___x_2424_);
v___x_2427_ = lean_nat_dec_lt(v___x_2425_, v___x_2426_);
if (v___x_2427_ == 0)
{
lean_dec_ref(v___x_2424_);
lean_dec(v_decl_2412_);
return v___x_2427_;
}
else
{
lean_object* v___x_2428_; lean_object* v___x_2429_; uint8_t v___x_2430_; 
v___x_2428_ = lean_unsigned_to_nat(1u);
v___x_2429_ = lean_nat_sub(v___x_2426_, v___x_2428_);
v___x_2430_ = lean_nat_dec_le(v___x_2425_, v___x_2429_);
if (v___x_2430_ == 0)
{
lean_dec(v___x_2429_);
lean_dec_ref(v___x_2424_);
lean_dec(v_decl_2412_);
return v___x_2430_;
}
else
{
uint8_t v___x_2431_; 
lean_inc(v___x_2429_);
v___x_2431_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2429_, v___x_2424_, v_decl_2412_, v___x_2425_, v___x_2429_);
lean_dec(v_decl_2412_);
lean_dec_ref(v___x_2424_);
lean_dec(v___x_2429_);
return v___x_2431_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_TagAttribute_hasTag_0interp(lean_interpreter_value* stack)
{
lean_object* v_attr_2410_ = stack[0].m_obj;
lean_object* v_env_2411_ = stack[1].m_obj;
lean_object* v_decl_2412_ = stack[2].m_obj;
uint8_t v_res_2432_;
v_res_2432_ = l_Lean_TagAttribute_hasTag(v_attr_2410_, v_env_2411_, v_decl_2412_);
stack->m_num = v_res_2432_;
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2433_, lean_object* v_env_2434_, lean_object* v_decl_2435_){
_start:
{
uint8_t v_res_2436_; lean_object* v_r_2437_; 
v_res_2436_ = l_Lean_TagAttribute_hasTag(v_attr_2433_, v_env_2434_, v_decl_2435_);
lean_dec_ref(v_attr_2433_);
v_r_2437_ = lean_box(v_res_2436_);
return v_r_2437_;
}
}
uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v___y_2438_, lean_object* v_as_2439_, lean_object* v_k_2440_, lean_object* v_x_2441_, lean_object* v_x_2442_, lean_object* v_x_2443_){
_start:
{
uint8_t v___x_2444_; 
v___x_2444_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2438_, v_as_2439_, v_k_2440_, v_x_2441_, v_x_2442_);
return v___x_2444_;
}
}
LEAN_EXPORT void l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2438_ = stack[0].m_obj;
lean_object* v_as_2439_ = stack[1].m_obj;
lean_object* v_k_2440_ = stack[2].m_obj;
lean_object* v_x_2441_ = stack[3].m_obj;
lean_object* v_x_2442_ = stack[4].m_obj;
uint8_t v_res_2445_;
v_res_2445_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v___y_2438_, v_as_2439_, v_k_2440_, v_x_2441_, v_x_2442_, lean_box(0));
stack->m_num = v_res_2445_;
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v___y_2446_, lean_object* v_as_2447_, lean_object* v_k_2448_, lean_object* v_x_2449_, lean_object* v_x_2450_, lean_object* v_x_2451_){
_start:
{
uint8_t v_res_2452_; lean_object* v_r_2453_; 
v_res_2452_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v___y_2446_, v_as_2447_, v_k_2448_, v_x_2449_, v_x_2450_, v_x_2451_);
lean_dec(v_k_2448_);
lean_dec_ref(v_as_2447_);
lean_dec(v___y_2446_);
v_r_2453_ = lean_box(v_res_2452_);
return v_r_2453_;
}
}
lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(lean_object* v_x_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2454_ = stack[0].m_obj;
lean_object* v___y_2455_ = stack[1].m_obj;
lean_object* v_res_2459_;
v_res_2459_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(v_x_2454_, v___y_2455_);
stack->m_obj
 = v_res_2459_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0___boxed(lean_object* v_x_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(v_x_2460_, v___y_2461_);
lean_dec_ref(v___y_2461_);
lean_dec_ref(v_x_2460_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(lean_object* v_s_2464_, lean_object* v_x_2465_){
_start:
{
lean_inc_ref(v_s_2464_);
return v_s_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1___boxed(lean_object* v_s_2466_, lean_object* v_x_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(v_s_2466_, v_x_2467_);
lean_dec_ref(v_x_2467_);
lean_dec_ref(v_s_2466_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(lean_object* v_x_2473_, lean_object* v_x_2474_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___boxed(lean_object* v_x_2476_, lean_object* v_x_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(v_x_2476_, v_x_2477_);
lean_dec_ref(v_x_2477_);
lean_dec_ref(v_x_2476_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(lean_object* v_x_2479_){
_start:
{
lean_object* v___x_2480_; 
v___x_2480_ = lean_box(0);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3___boxed(lean_object* v_x_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(v_x_2481_);
lean_dec_ref(v_x_2481_);
return v_res_2482_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4(void){
_start:
{
lean_object* v___f_2487_; lean_object* v___f_2488_; lean_object* v___f_2489_; lean_object* v___f_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___f_2487_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3));
v___f_2488_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2));
v___f_2489_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1));
v___f_2490_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0));
v___x_2491_ = lean_box(0);
v___x_2492_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
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
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5(void){
_start:
{
uint8_t v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2494_ = 0;
v___x_2495_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4);
v___x_2496_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2497_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
lean_ctor_set(v___x_2497_, 1, v___x_2495_);
lean_ctor_set_uint8(v___x_2497_, sizeof(void*)*2, v___x_2494_);
return v___x_2497_;
}
}
lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg(){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5);
return v___x_2499_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedParametricAttribute_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2500_;
v_res_2500_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
stack->m_obj
 = v_res_2500_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___boxed(lean_object* v___dummy_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v_res_2502_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__0(void){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2504_){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2505_;
}
}
lean_object* l_Lean_instInhabitedParametricAttribute___redArg(){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2507_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedParametricAttribute___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2508_;
v_res_2508_ = l_Lean_instInhabitedParametricAttribute___redArg();
stack->m_obj
 = v_res_2508_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg___boxed(lean_object* v___dummy_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Lean_instInhabitedParametricAttribute___redArg();
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2511_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object* v_x_2513_, lean_object* v_p_2514_){
_start:
{
lean_object* v_fst_2515_; lean_object* v_snd_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2533_; 
v_fst_2515_ = lean_ctor_get(v_x_2513_, 0);
v_snd_2516_ = lean_ctor_get(v_x_2513_, 1);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_x_2513_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2518_ = v_x_2513_;
v_isShared_2519_ = v_isSharedCheck_2533_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_snd_2516_);
lean_inc(v_fst_2515_);
lean_dec(v_x_2513_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2533_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v_fst_2520_; lean_object* v_snd_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2532_; 
v_fst_2520_ = lean_ctor_get(v_p_2514_, 0);
v_snd_2521_ = lean_ctor_get(v_p_2514_, 1);
v_isSharedCheck_2532_ = !lean_is_exclusive(v_p_2514_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2523_ = v_p_2514_;
v_isShared_2524_ = v_isSharedCheck_2532_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_snd_2521_);
lean_inc(v_fst_2520_);
lean_dec(v_p_2514_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2532_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
lean_inc(v_fst_2520_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set_tag(v___x_2518_, 1);
lean_ctor_set(v___x_2518_, 1, v_fst_2515_);
lean_ctor_set(v___x_2518_, 0, v_fst_2520_);
v___x_2526_ = v___x_2518_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_fst_2520_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_fst_2515_);
v___x_2526_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2527_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2520_, v_snd_2521_, v_snd_2516_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 1, v___x_2527_);
lean_ctor_set(v___x_2523_, 0, v___x_2526_);
v___x_2529_ = v___x_2523_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object* v_init_2534_, lean_object* v_x_2535_){
_start:
{
if (lean_obj_tag(v_x_2535_) == 0)
{
lean_object* v_k_2536_; lean_object* v_v_2537_; lean_object* v_l_2538_; lean_object* v_r_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v_k_2536_ = lean_ctor_get(v_x_2535_, 1);
v_v_2537_ = lean_ctor_get(v_x_2535_, 2);
v_l_2538_ = lean_ctor_get(v_x_2535_, 3);
v_r_2539_ = lean_ctor_get(v_x_2535_, 4);
v___x_2540_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2534_, v_l_2538_);
lean_inc(v_v_2537_);
lean_inc(v_k_2536_);
v___x_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2541_, 0, v_k_2536_);
lean_ctor_set(v___x_2541_, 1, v_v_2537_);
v___x_2542_ = lean_array_push(v___x_2540_, v___x_2541_);
v_init_2534_ = v___x_2542_;
v_x_2535_ = v_r_2539_;
goto _start;
}
else
{
return v_init_2534_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object* v_init_2544_, lean_object* v_x_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2544_, v_x_2545_);
lean_dec(v_x_2545_);
return v_res_2546_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object* v_snd_2547_, lean_object* v_as_2548_, size_t v_i_2549_, size_t v_stop_2550_, lean_object* v_b_2551_){
_start:
{
lean_object* v___y_2553_; uint8_t v___x_2557_; 
v___x_2557_ = lean_usize_dec_eq(v_i_2549_, v_stop_2550_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = lean_array_uget_borrowed(v_as_2548_, v_i_2549_);
v___x_2559_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2547_, v___x_2558_);
if (lean_obj_tag(v___x_2559_) == 0)
{
v___y_2553_ = v_b_2551_;
goto v___jp_2552_;
}
else
{
lean_object* v_val_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v_val_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_val_2560_);
lean_dec_ref_known(v___x_2559_, 1);
lean_inc(v___x_2558_);
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2558_);
lean_ctor_set(v___x_2561_, 1, v_val_2560_);
v___x_2562_ = lean_array_push(v_b_2551_, v___x_2561_);
v___y_2553_ = v___x_2562_;
goto v___jp_2552_;
}
}
else
{
return v_b_2551_;
}
v___jp_2552_:
{
size_t v___x_2554_; size_t v___x_2555_; 
v___x_2554_ = ((size_t)1ULL);
v___x_2555_ = lean_usize_add(v_i_2549_, v___x_2554_);
v_i_2549_ = v___x_2555_;
v_b_2551_ = v___y_2553_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_2547_ = stack[0].m_obj;
lean_object* v_as_2548_ = stack[1].m_obj;
size_t v_i_2549_ = stack[2].m_num;
size_t v_stop_2550_ = stack[3].m_num;
lean_object* v_b_2551_ = stack[4].m_obj;
lean_object* v_res_2563_;
v_res_2563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2547_, v_as_2548_, v_i_2549_, v_stop_2550_, v_b_2551_);
stack->m_obj
 = v_res_2563_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2564_, lean_object* v_as_2565_, lean_object* v_i_2566_, lean_object* v_stop_2567_, lean_object* v_b_2568_){
_start:
{
size_t v_i_boxed_2569_; size_t v_stop_boxed_2570_; lean_object* v_res_2571_; 
v_i_boxed_2569_ = lean_unbox_usize(v_i_2566_);
lean_dec(v_i_2566_);
v_stop_boxed_2570_ = lean_unbox_usize(v_stop_2567_);
lean_dec(v_stop_2567_);
v_res_2571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2564_, v_as_2565_, v_i_boxed_2569_, v_stop_boxed_2570_, v_b_2568_);
lean_dec_ref(v_as_2565_);
lean_dec(v_snd_2564_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object* v_snd_2572_, lean_object* v_as_2573_, lean_object* v_start_2574_, lean_object* v_stop_2575_){
_start:
{
lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2576_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2577_ = lean_nat_dec_lt(v_start_2574_, v_stop_2575_);
if (v___x_2577_ == 0)
{
return v___x_2576_;
}
else
{
lean_object* v___x_2578_; uint8_t v___x_2579_; 
v___x_2578_ = lean_array_get_size(v_as_2573_);
v___x_2579_ = lean_nat_dec_le(v_stop_2575_, v___x_2578_);
if (v___x_2579_ == 0)
{
uint8_t v___x_2580_; 
v___x_2580_ = lean_nat_dec_lt(v_start_2574_, v___x_2578_);
if (v___x_2580_ == 0)
{
return v___x_2576_;
}
else
{
size_t v___x_2581_; size_t v___x_2582_; lean_object* v___x_2583_; 
v___x_2581_ = lean_usize_of_nat(v_start_2574_);
v___x_2582_ = lean_usize_of_nat(v___x_2578_);
v___x_2583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2572_, v_as_2573_, v___x_2581_, v___x_2582_, v___x_2576_);
return v___x_2583_;
}
}
else
{
size_t v___x_2584_; size_t v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = lean_usize_of_nat(v_start_2574_);
v___x_2585_ = lean_usize_of_nat(v_stop_2575_);
v___x_2586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2572_, v_as_2573_, v___x_2584_, v___x_2585_, v___x_2576_);
return v___x_2586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object* v_snd_2587_, lean_object* v_as_2588_, lean_object* v_start_2589_, lean_object* v_stop_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2587_, v_as_2588_, v_start_2589_, v_stop_2590_);
lean_dec(v_stop_2590_);
lean_dec(v_start_2589_);
lean_dec_ref(v_as_2588_);
lean_dec(v_snd_2587_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object* v_hi_2592_, lean_object* v_pivot_2593_, lean_object* v_as_2594_, lean_object* v_i_2595_, lean_object* v_k_2596_){
_start:
{
uint8_t v___x_2597_; 
v___x_2597_ = lean_nat_dec_lt(v_k_2596_, v_hi_2592_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
lean_dec(v_k_2596_);
v___x_2598_ = lean_array_fswap(v_as_2594_, v_i_2595_, v_hi_2592_);
v___x_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2599_, 0, v_i_2595_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
return v___x_2599_;
}
else
{
lean_object* v___x_2600_; lean_object* v_fst_2601_; lean_object* v_fst_2602_; uint8_t v___x_2603_; 
v___x_2600_ = lean_array_fget_borrowed(v_as_2594_, v_k_2596_);
v_fst_2601_ = lean_ctor_get(v___x_2600_, 0);
v_fst_2602_ = lean_ctor_get(v_pivot_2593_, 0);
v___x_2603_ = l_Lean_Name_quickLt(v_fst_2601_, v_fst_2602_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = lean_unsigned_to_nat(1u);
v___x_2605_ = lean_nat_add(v_k_2596_, v___x_2604_);
lean_dec(v_k_2596_);
v_k_2596_ = v___x_2605_;
goto _start;
}
else
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2607_ = lean_array_fswap(v_as_2594_, v_i_2595_, v_k_2596_);
v___x_2608_ = lean_unsigned_to_nat(1u);
v___x_2609_ = lean_nat_add(v_i_2595_, v___x_2608_);
lean_dec(v_i_2595_);
v___x_2610_ = lean_nat_add(v_k_2596_, v___x_2608_);
lean_dec(v_k_2596_);
v_as_2594_ = v___x_2607_;
v_i_2595_ = v___x_2609_;
v_k_2596_ = v___x_2610_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2612_, lean_object* v_pivot_2613_, lean_object* v_as_2614_, lean_object* v_i_2615_, lean_object* v_k_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2612_, v_pivot_2613_, v_as_2614_, v_i_2615_, v_k_2616_);
lean_dec_ref(v_pivot_2613_);
lean_dec(v_hi_2612_);
return v_res_2617_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object* v_a_2618_, lean_object* v_b_2619_){
_start:
{
lean_object* v_fst_2620_; lean_object* v_fst_2621_; uint8_t v___x_2622_; 
v_fst_2620_ = lean_ctor_get(v_a_2618_, 0);
v_fst_2621_ = lean_ctor_get(v_b_2619_, 0);
v___x_2622_ = l_Lean_Name_quickLt(v_fst_2620_, v_fst_2621_);
return v___x_2622_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2618_ = stack[0].m_obj;
lean_object* v_b_2619_ = stack[1].m_obj;
uint8_t v_res_2623_;
v_res_2623_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2618_, v_b_2619_);
stack->m_num = v_res_2623_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object* v_a_2624_, lean_object* v_b_2625_){
_start:
{
uint8_t v_res_2626_; lean_object* v_r_2627_; 
v_res_2626_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2624_, v_b_2625_);
lean_dec_ref(v_b_2625_);
lean_dec_ref(v_a_2624_);
v_r_2627_ = lean_box(v_res_2626_);
return v_r_2627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object* v_n_2628_, lean_object* v_as_2629_, lean_object* v_lo_2630_, lean_object* v_hi_2631_){
_start:
{
lean_object* v___y_2633_; uint8_t v___x_2643_; 
v___x_2643_ = lean_nat_dec_lt(v_lo_2630_, v_hi_2631_);
if (v___x_2643_ == 0)
{
lean_dec(v_lo_2630_);
return v_as_2629_;
}
else
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v_mid_2646_; lean_object* v___y_2648_; lean_object* v___y_2654_; lean_object* v___x_2659_; lean_object* v___x_2660_; uint8_t v___x_2661_; 
v___x_2644_ = lean_nat_add(v_lo_2630_, v_hi_2631_);
v___x_2645_ = lean_unsigned_to_nat(1u);
v_mid_2646_ = lean_nat_shiftr(v___x_2644_, v___x_2645_);
lean_dec(v___x_2644_);
v___x_2659_ = lean_array_fget_borrowed(v_as_2629_, v_mid_2646_);
v___x_2660_ = lean_array_fget_borrowed(v_as_2629_, v_lo_2630_);
v___x_2661_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2659_, v___x_2660_);
if (v___x_2661_ == 0)
{
v___y_2654_ = v_as_2629_;
goto v___jp_2653_;
}
else
{
lean_object* v___x_2662_; 
v___x_2662_ = lean_array_fswap(v_as_2629_, v_lo_2630_, v_mid_2646_);
v___y_2654_ = v___x_2662_;
goto v___jp_2653_;
}
v___jp_2647_:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; 
v___x_2649_ = lean_array_fget_borrowed(v___y_2648_, v_mid_2646_);
v___x_2650_ = lean_array_fget_borrowed(v___y_2648_, v_hi_2631_);
v___x_2651_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2649_, v___x_2650_);
if (v___x_2651_ == 0)
{
lean_dec(v_mid_2646_);
v___y_2633_ = v___y_2648_;
goto v___jp_2632_;
}
else
{
lean_object* v___x_2652_; 
v___x_2652_ = lean_array_fswap(v___y_2648_, v_mid_2646_, v_hi_2631_);
lean_dec(v_mid_2646_);
v___y_2633_ = v___x_2652_;
goto v___jp_2632_;
}
}
v___jp_2653_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; 
v___x_2655_ = lean_array_fget_borrowed(v___y_2654_, v_hi_2631_);
v___x_2656_ = lean_array_fget_borrowed(v___y_2654_, v_lo_2630_);
v___x_2657_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2655_, v___x_2656_);
if (v___x_2657_ == 0)
{
v___y_2648_ = v___y_2654_;
goto v___jp_2647_;
}
else
{
lean_object* v___x_2658_; 
v___x_2658_ = lean_array_fswap(v___y_2654_, v_lo_2630_, v_hi_2631_);
v___y_2648_ = v___x_2658_;
goto v___jp_2647_;
}
}
}
v___jp_2632_:
{
lean_object* v_pivot_2634_; lean_object* v___x_2635_; lean_object* v_fst_2636_; lean_object* v_snd_2637_; uint8_t v___x_2638_; 
v_pivot_2634_ = lean_array_fget(v___y_2633_, v_hi_2631_);
lean_inc_n(v_lo_2630_, 2);
v___x_2635_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2631_, v_pivot_2634_, v___y_2633_, v_lo_2630_, v_lo_2630_);
lean_dec(v_pivot_2634_);
v_fst_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_fst_2636_);
v_snd_2637_ = lean_ctor_get(v___x_2635_, 1);
lean_inc(v_snd_2637_);
lean_dec_ref(v___x_2635_);
v___x_2638_ = lean_nat_dec_le(v_hi_2631_, v_fst_2636_);
if (v___x_2638_ == 0)
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2639_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2628_, v_snd_2637_, v_lo_2630_, v_fst_2636_);
v___x_2640_ = lean_unsigned_to_nat(1u);
v___x_2641_ = lean_nat_add(v_fst_2636_, v___x_2640_);
lean_dec(v_fst_2636_);
v_as_2629_ = v___x_2639_;
v_lo_2630_ = v___x_2641_;
goto _start;
}
else
{
lean_dec(v_fst_2636_);
lean_dec(v_lo_2630_);
return v_snd_2637_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object* v_n_2663_, lean_object* v_as_2664_, lean_object* v_lo_2665_, lean_object* v_hi_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2663_, v_as_2664_, v_lo_2665_, v_hi_2666_);
lean_dec(v_hi_2666_);
lean_dec(v_n_2663_);
return v_res_2667_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object* v_filterExport_2668_, lean_object* v_env_2669_, lean_object* v_as_2670_, size_t v_i_2671_, size_t v_stop_2672_, lean_object* v_b_2673_){
_start:
{
lean_object* v___y_2675_; uint8_t v___x_2679_; 
v___x_2679_ = lean_usize_dec_eq(v_i_2671_, v_stop_2672_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2680_; lean_object* v_fst_2681_; lean_object* v_snd_2682_; lean_object* v___x_2683_; uint8_t v___x_2684_; 
v___x_2680_ = lean_array_uget_borrowed(v_as_2670_, v_i_2671_);
v_fst_2681_ = lean_ctor_get(v___x_2680_, 0);
v_snd_2682_ = lean_ctor_get(v___x_2680_, 1);
lean_inc_ref(v_filterExport_2668_);
lean_inc(v_snd_2682_);
lean_inc(v_fst_2681_);
lean_inc_ref(v_env_2669_);
v___x_2683_ = lean_apply_3(v_filterExport_2668_, v_env_2669_, v_fst_2681_, v_snd_2682_);
v___x_2684_ = lean_unbox(v___x_2683_);
if (v___x_2684_ == 0)
{
v___y_2675_ = v_b_2673_;
goto v___jp_2674_;
}
else
{
lean_object* v___x_2685_; 
lean_inc(v___x_2680_);
v___x_2685_ = lean_array_push(v_b_2673_, v___x_2680_);
v___y_2675_ = v___x_2685_;
goto v___jp_2674_;
}
}
else
{
lean_dec_ref(v_env_2669_);
lean_dec_ref(v_filterExport_2668_);
return v_b_2673_;
}
v___jp_2674_:
{
size_t v___x_2676_; size_t v___x_2677_; 
v___x_2676_ = ((size_t)1ULL);
v___x_2677_ = lean_usize_add(v_i_2671_, v___x_2676_);
v_i_2671_ = v___x_2677_;
v_b_2673_ = v___y_2675_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_filterExport_2668_ = stack[0].m_obj;
lean_object* v_env_2669_ = stack[1].m_obj;
lean_object* v_as_2670_ = stack[2].m_obj;
size_t v_i_2671_ = stack[3].m_num;
size_t v_stop_2672_ = stack[4].m_num;
lean_object* v_b_2673_ = stack[5].m_obj;
lean_object* v_res_2686_;
v_res_2686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2668_, v_env_2669_, v_as_2670_, v_i_2671_, v_stop_2672_, v_b_2673_);
stack->m_obj
 = v_res_2686_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object* v_filterExport_2687_, lean_object* v_env_2688_, lean_object* v_as_2689_, lean_object* v_i_2690_, lean_object* v_stop_2691_, lean_object* v_b_2692_){
_start:
{
size_t v_i_boxed_2693_; size_t v_stop_boxed_2694_; lean_object* v_res_2695_; 
v_i_boxed_2693_ = lean_unbox_usize(v_i_2690_);
lean_dec(v_i_2690_);
v_stop_boxed_2694_ = lean_unbox_usize(v_stop_2691_);
lean_dec(v_stop_2691_);
v_res_2695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2687_, v_env_2688_, v_as_2689_, v_i_boxed_2693_, v_stop_boxed_2694_, v_b_2692_);
lean_dec_ref(v_as_2689_);
return v_res_2695_;
}
}
lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object* v_filterExport_2696_, uint8_t v_preserveOrder_2697_, lean_object* v_env_2698_, lean_object* v_x_2699_){
_start:
{
lean_object* v___y_2701_; 
if (v_preserveOrder_2697_ == 0)
{
lean_object* v_snd_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v_r_2720_; lean_object* v___x_2721_; lean_object* v___y_2723_; lean_object* v___y_2724_; uint8_t v___x_2726_; 
v_snd_2717_ = lean_ctor_get(v_x_2699_, 1);
lean_inc(v_snd_2717_);
lean_dec_ref(v_x_2699_);
v___x_2718_ = lean_unsigned_to_nat(0u);
v___x_2719_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v_r_2720_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_2719_, v_snd_2717_);
lean_dec(v_snd_2717_);
v___x_2721_ = lean_array_get_size(v_r_2720_);
v___x_2726_ = lean_nat_dec_eq(v___x_2721_, v___x_2718_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___y_2730_; uint8_t v___x_2732_; 
v___x_2727_ = lean_unsigned_to_nat(1u);
v___x_2728_ = lean_nat_sub(v___x_2721_, v___x_2727_);
v___x_2732_ = lean_nat_dec_le(v___x_2718_, v___x_2728_);
if (v___x_2732_ == 0)
{
lean_inc(v___x_2728_);
v___y_2730_ = v___x_2728_;
goto v___jp_2729_;
}
else
{
v___y_2730_ = v___x_2718_;
goto v___jp_2729_;
}
v___jp_2729_:
{
uint8_t v___x_2731_; 
v___x_2731_ = lean_nat_dec_le(v___y_2730_, v___x_2728_);
if (v___x_2731_ == 0)
{
lean_dec(v___x_2728_);
lean_inc(v___y_2730_);
v___y_2723_ = v___y_2730_;
v___y_2724_ = v___y_2730_;
goto v___jp_2722_;
}
else
{
v___y_2723_ = v___y_2730_;
v___y_2724_ = v___x_2728_;
goto v___jp_2722_;
}
}
}
else
{
v___y_2701_ = v_r_2720_;
goto v___jp_2700_;
}
v___jp_2722_:
{
lean_object* v___x_2725_; 
v___x_2725_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_2721_, v_r_2720_, v___y_2723_, v___y_2724_);
lean_dec(v___y_2724_);
v___y_2701_ = v___x_2725_;
goto v___jp_2700_;
}
}
else
{
lean_object* v_fst_2733_; lean_object* v_snd_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v_fst_2733_ = lean_ctor_get(v_x_2699_, 0);
lean_inc(v_fst_2733_);
v_snd_2734_ = lean_ctor_get(v_x_2699_, 1);
lean_inc(v_snd_2734_);
lean_dec_ref(v_x_2699_);
v___x_2735_ = lean_array_mk(v_fst_2733_);
v___x_2736_ = l_Array_reverse___redArg(v___x_2735_);
v___x_2737_ = lean_unsigned_to_nat(0u);
v___x_2738_ = lean_array_get_size(v___x_2736_);
v___x_2739_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2734_, v___x_2736_, v___x_2737_, v___x_2738_);
lean_dec_ref(v___x_2736_);
lean_dec(v_snd_2734_);
v___y_2701_ = v___x_2739_;
goto v___jp_2700_;
}
v___jp_2700_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; uint8_t v___x_2705_; 
v___x_2702_ = lean_unsigned_to_nat(0u);
v___x_2703_ = lean_array_get_size(v___y_2701_);
v___x_2704_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2705_ = lean_nat_dec_lt(v___x_2702_, v___x_2703_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; 
lean_dec_ref(v_env_2698_);
lean_dec_ref(v_filterExport_2696_);
v___x_2706_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2704_);
lean_ctor_set(v___x_2706_, 1, v___x_2704_);
lean_ctor_set(v___x_2706_, 2, v___y_2701_);
return v___x_2706_;
}
else
{
uint8_t v___x_2707_; 
v___x_2707_ = lean_nat_dec_le(v___x_2703_, v___x_2703_);
if (v___x_2707_ == 0)
{
if (v___x_2705_ == 0)
{
lean_object* v___x_2708_; 
lean_dec_ref(v_env_2698_);
lean_dec_ref(v_filterExport_2696_);
v___x_2708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2704_);
lean_ctor_set(v___x_2708_, 1, v___x_2704_);
lean_ctor_set(v___x_2708_, 2, v___y_2701_);
return v___x_2708_;
}
else
{
size_t v___x_2709_; size_t v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2709_ = ((size_t)0ULL);
v___x_2710_ = lean_usize_of_nat(v___x_2703_);
v___x_2711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2696_, v_env_2698_, v___y_2701_, v___x_2709_, v___x_2710_, v___x_2704_);
lean_inc_ref(v___x_2711_);
v___x_2712_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
lean_ctor_set(v___x_2712_, 2, v___y_2701_);
return v___x_2712_;
}
}
else
{
size_t v___x_2713_; size_t v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2713_ = ((size_t)0ULL);
v___x_2714_ = lean_usize_of_nat(v___x_2703_);
v___x_2715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2696_, v_env_2698_, v___y_2701_, v___x_2713_, v___x_2714_, v___x_2704_);
lean_inc_ref(v___x_2715_);
v___x_2716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
lean_ctor_set(v___x_2716_, 2, v___y_2701_);
return v___x_2716_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_registerParametricAttributeExt___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_filterExport_2696_ = stack[0].m_obj;
uint8_t v_preserveOrder_2697_ = stack[1].m_num;
lean_object* v_env_2698_ = stack[2].m_obj;
lean_object* v_x_2699_ = stack[3].m_obj;
lean_object* v_res_2740_;
v_res_2740_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2696_, v_preserveOrder_2697_, v_env_2698_, v_x_2699_);
stack->m_obj
 = v_res_2740_;
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object* v_filterExport_2741_, lean_object* v_preserveOrder_2742_, lean_object* v_env_2743_, lean_object* v_x_2744_){
_start:
{
uint8_t v_preserveOrder_boxed_2745_; lean_object* v_res_2746_; 
v_preserveOrder_boxed_2745_ = lean_unbox(v_preserveOrder_2742_);
v_res_2746_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2741_, v_preserveOrder_boxed_2745_, v_env_2743_, v_x_2744_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object* v_x_2756_){
_start:
{
lean_object* v_snd_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2771_; 
v_snd_2757_ = lean_ctor_get(v_x_2756_, 1);
v_isSharedCheck_2771_ = !lean_is_exclusive(v_x_2756_);
if (v_isSharedCheck_2771_ == 0)
{
lean_object* v_unused_2772_; 
v_unused_2772_ = lean_ctor_get(v_x_2756_, 0);
lean_dec(v_unused_2772_);
v___x_2759_ = v_x_2756_;
v_isShared_2760_ = v_isSharedCheck_2771_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_snd_2757_);
lean_dec(v_x_2756_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2771_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; lean_object* v___y_2763_; 
v___x_2761_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2757_) == 0)
{
lean_object* v_size_2769_; 
v_size_2769_ = lean_ctor_get(v_snd_2757_, 0);
lean_inc(v_size_2769_);
lean_dec_ref_known(v_snd_2757_, 5);
v___y_2763_ = v_size_2769_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_unsigned_to_nat(0u);
v___y_2763_ = v___x_2770_;
goto v___jp_2762_;
}
v___jp_2762_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
v___x_2764_ = l_Nat_reprFast(v___y_2763_);
v___x_2765_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2764_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set_tag(v___x_2759_, 5);
lean_ctor_set(v___x_2759_, 1, v___x_2765_);
lean_ctor_set(v___x_2759_, 0, v___x_2761_);
v___x_2767_ = v___x_2759_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2761_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v___x_2765_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object* v_x_2773_){
_start:
{
lean_object* v___x_2774_; 
v___x_2774_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object* v_x_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Lean_registerParametricAttributeExt___redArg___lam__3(v_x_2775_);
lean_dec_ref(v_x_2775_);
return v_res_2776_;
}
}
lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object* v___x_2777_){
_start:
{
lean_object* v___x_2779_; 
v___x_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2777_);
return v___x_2779_;
}
}
LEAN_EXPORT void l_Lean_registerParametricAttributeExt___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2777_ = stack[0].m_obj;
lean_object* v_res_2780_;
v_res_2780_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2777_);
stack->m_obj
 = v_res_2780_;
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object* v___x_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2781_);
return v_res_2783_;
}
}
lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object* v___x_2784_, lean_object* v_x_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2784_);
return v___x_2788_;
}
}
LEAN_EXPORT void l_Lean_registerParametricAttributeExt___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2784_ = stack[0].m_obj;
lean_object* v_x_2785_ = stack[1].m_obj;
lean_object* v___y_2786_ = stack[2].m_obj;
lean_object* v_res_2789_;
v_res_2789_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2784_, v_x_2785_, v___y_2786_);
stack->m_obj
 = v_res_2789_;
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object* v___x_2790_, lean_object* v_x_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2790_, v_x_2791_, v___y_2792_);
lean_dec_ref(v___y_2792_);
lean_dec_ref(v_x_2791_);
return v_res_2794_;
}
}
lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object* v_ref_2805_, uint8_t v_preserveOrder_2806_, lean_object* v_filterExport_2807_, uint8_t v_logWrites_2808_){
_start:
{
lean_object* v___f_2810_; lean_object* v___x_2811_; lean_object* v___f_2812_; lean_object* v___f_2813_; lean_object* v___f_2814_; lean_object* v___f_2815_; lean_object* v___f_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___f_2810_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__0));
v___x_2811_ = lean_box(v_preserveOrder_2806_);
v___f_2812_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2812_, 0, v_filterExport_2807_);
lean_closure_set(v___f_2812_, 1, v___x_2811_);
v___f_2813_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__1));
v___f_2814_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__2));
v___f_2815_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__4));
v___f_2816_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__5));
v___x_2817_ = lean_box(2);
v___x_2818_ = lean_box(0);
v___x_2819_ = 0;
v___x_2820_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2820_, 0, v_ref_2805_);
lean_ctor_set(v___x_2820_, 1, v___f_2815_);
lean_ctor_set(v___x_2820_, 2, v___f_2816_);
lean_ctor_set(v___x_2820_, 3, v___f_2810_);
lean_ctor_set(v___x_2820_, 4, v___f_2812_);
lean_ctor_set(v___x_2820_, 5, v___f_2813_);
lean_ctor_set(v___x_2820_, 6, v___x_2817_);
lean_ctor_set(v___x_2820_, 7, v___x_2818_);
lean_ctor_set_uint8(v___x_2820_, sizeof(void*)*8, v___x_2819_);
lean_ctor_set_uint8(v___x_2820_, sizeof(void*)*8 + 1, v_logWrites_2808_);
v___x_2821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2820_);
lean_ctor_set(v___x_2821_, 1, v___f_2814_);
v___x_2822_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT void l_Lean_registerParametricAttributeExt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2805_ = stack[0].m_obj;
uint8_t v_preserveOrder_2806_ = stack[1].m_num;
lean_object* v_filterExport_2807_ = stack[2].m_obj;
uint8_t v_logWrites_2808_ = stack[3].m_num;
lean_object* v_res_2823_;
v_res_2823_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2805_, v_preserveOrder_2806_, v_filterExport_2807_, v_logWrites_2808_);
stack->m_obj
 = v_res_2823_;
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object* v_ref_2824_, lean_object* v_preserveOrder_2825_, lean_object* v_filterExport_2826_, lean_object* v_logWrites_2827_, lean_object* v_a_2828_){
_start:
{
uint8_t v_preserveOrder_boxed_2829_; uint8_t v_logWrites_boxed_2830_; lean_object* v_res_2831_; 
v_preserveOrder_boxed_2829_ = lean_unbox(v_preserveOrder_2825_);
v_logWrites_boxed_2830_ = lean_unbox(v_logWrites_2827_);
v_res_2831_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2824_, v_preserveOrder_boxed_2829_, v_filterExport_2826_, v_logWrites_boxed_2830_);
return v_res_2831_;
}
}
lean_object* l_Lean_registerParametricAttributeExt(lean_object* v_00_u03b1_2832_, lean_object* v_ref_2833_, uint8_t v_preserveOrder_2834_, lean_object* v_filterExport_2835_, uint8_t v_logWrites_2836_){
_start:
{
lean_object* v___x_2838_; 
v___x_2838_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2833_, v_preserveOrder_2834_, v_filterExport_2835_, v_logWrites_2836_);
return v___x_2838_;
}
}
LEAN_EXPORT void l_Lean_registerParametricAttributeExt_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2833_ = stack[1].m_obj;
uint8_t v_preserveOrder_2834_ = stack[2].m_num;
lean_object* v_filterExport_2835_ = stack[3].m_obj;
uint8_t v_logWrites_2836_ = stack[4].m_num;
lean_object* v_res_2839_;
v_res_2839_ = l_Lean_registerParametricAttributeExt(lean_box(0), v_ref_2833_, v_preserveOrder_2834_, v_filterExport_2835_, v_logWrites_2836_);
stack->m_obj
 = v_res_2839_;
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object* v_00_u03b1_2840_, lean_object* v_ref_2841_, lean_object* v_preserveOrder_2842_, lean_object* v_filterExport_2843_, lean_object* v_logWrites_2844_, lean_object* v_a_2845_){
_start:
{
uint8_t v_preserveOrder_boxed_2846_; uint8_t v_logWrites_boxed_2847_; lean_object* v_res_2848_; 
v_preserveOrder_boxed_2846_ = lean_unbox(v_preserveOrder_2842_);
v_logWrites_boxed_2847_ = lean_unbox(v_logWrites_2844_);
v_res_2848_ = l_Lean_registerParametricAttributeExt(v_00_u03b1_2840_, v_ref_2841_, v_preserveOrder_boxed_2846_, v_filterExport_2843_, v_logWrites_boxed_2847_);
return v_res_2848_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object* v_00_u03b1_2849_, lean_object* v_filterExport_2850_, lean_object* v_env_2851_, lean_object* v_as_2852_, size_t v_i_2853_, size_t v_stop_2854_, lean_object* v_b_2855_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2850_, v_env_2851_, v_as_2852_, v_i_2853_, v_stop_2854_, v_b_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_filterExport_2850_ = stack[1].m_obj;
lean_object* v_env_2851_ = stack[2].m_obj;
lean_object* v_as_2852_ = stack[3].m_obj;
size_t v_i_2853_ = stack[4].m_num;
size_t v_stop_2854_ = stack[5].m_num;
lean_object* v_b_2855_ = stack[6].m_obj;
lean_object* v_res_2857_;
v_res_2857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_box(0), v_filterExport_2850_, v_env_2851_, v_as_2852_, v_i_2853_, v_stop_2854_, v_b_2855_);
stack->m_obj
 = v_res_2857_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object* v_00_u03b1_2858_, lean_object* v_filterExport_2859_, lean_object* v_env_2860_, lean_object* v_as_2861_, lean_object* v_i_2862_, lean_object* v_stop_2863_, lean_object* v_b_2864_){
_start:
{
size_t v_i_boxed_2865_; size_t v_stop_boxed_2866_; lean_object* v_res_2867_; 
v_i_boxed_2865_ = lean_unbox_usize(v_i_2862_);
lean_dec(v_i_2862_);
v_stop_boxed_2866_ = lean_unbox_usize(v_stop_2863_);
lean_dec(v_stop_2863_);
v_res_2867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(v_00_u03b1_2858_, v_filterExport_2859_, v_env_2860_, v_as_2861_, v_i_boxed_2865_, v_stop_boxed_2866_, v_b_2864_);
lean_dec_ref(v_as_2861_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object* v_init_2868_, lean_object* v_t_2869_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2868_, v_t_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object* v_init_2871_, lean_object* v_t_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(v_init_2871_, v_t_2872_);
lean_dec(v_t_2872_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object* v_00_u03b1_2874_, lean_object* v_init_2875_, lean_object* v_t_2876_){
_start:
{
lean_object* v___x_2877_; 
v___x_2877_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2875_, v_t_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object* v_00_u03b1_2878_, lean_object* v_init_2879_, lean_object* v_t_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(v_00_u03b1_2878_, v_init_2879_, v_t_2880_);
lean_dec(v_t_2880_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object* v_00_u03b1_2882_, lean_object* v_n_2883_, lean_object* v_as_2884_, lean_object* v_lo_2885_, lean_object* v_hi_2886_, lean_object* v_w_2887_, lean_object* v_hlo_2888_, lean_object* v_hhi_2889_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2883_, v_as_2884_, v_lo_2885_, v_hi_2886_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object* v_00_u03b1_2891_, lean_object* v_n_2892_, lean_object* v_as_2893_, lean_object* v_lo_2894_, lean_object* v_hi_2895_, lean_object* v_w_2896_, lean_object* v_hlo_2897_, lean_object* v_hhi_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(v_00_u03b1_2891_, v_n_2892_, v_as_2893_, v_lo_2894_, v_hi_2895_, v_w_2896_, v_hlo_2897_, v_hhi_2898_);
lean_dec(v_hi_2895_);
lean_dec(v_n_2892_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object* v_00_u03b1_2900_, lean_object* v_snd_2901_, lean_object* v_as_2902_, lean_object* v_start_2903_, lean_object* v_stop_2904_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2901_, v_as_2902_, v_start_2903_, v_stop_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object* v_00_u03b1_2906_, lean_object* v_snd_2907_, lean_object* v_as_2908_, lean_object* v_start_2909_, lean_object* v_stop_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(v_00_u03b1_2906_, v_snd_2907_, v_as_2908_, v_start_2909_, v_stop_2910_);
lean_dec(v_stop_2910_);
lean_dec(v_start_2909_);
lean_dec_ref(v_as_2908_);
lean_dec(v_snd_2907_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object* v_00_u03b1_2912_, lean_object* v_init_2913_, lean_object* v_x_2914_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2913_, v_x_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2916_, lean_object* v_init_2917_, lean_object* v_x_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(v_00_u03b1_2916_, v_init_2917_, v_x_2918_);
lean_dec(v_x_2918_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object* v_00_u03b1_2920_, lean_object* v_n_2921_, lean_object* v_lo_2922_, lean_object* v_hi_2923_, lean_object* v_hhi_2924_, lean_object* v_pivot_2925_, lean_object* v_as_2926_, lean_object* v_i_2927_, lean_object* v_k_2928_, lean_object* v_ilo_2929_, lean_object* v_ik_2930_, lean_object* v_w_2931_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2923_, v_pivot_2925_, v_as_2926_, v_i_2927_, v_k_2928_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2933_, lean_object* v_n_2934_, lean_object* v_lo_2935_, lean_object* v_hi_2936_, lean_object* v_hhi_2937_, lean_object* v_pivot_2938_, lean_object* v_as_2939_, lean_object* v_i_2940_, lean_object* v_k_2941_, lean_object* v_ilo_2942_, lean_object* v_ik_2943_, lean_object* v_w_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(v_00_u03b1_2933_, v_n_2934_, v_lo_2935_, v_hi_2936_, v_hhi_2937_, v_pivot_2938_, v_as_2939_, v_i_2940_, v_k_2941_, v_ilo_2942_, v_ik_2943_, v_w_2944_);
lean_dec_ref(v_pivot_2938_);
lean_dec(v_hi_2936_);
lean_dec(v_lo_2935_);
lean_dec(v_n_2934_);
return v_res_2945_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object* v_00_u03b1_2946_, lean_object* v_snd_2947_, lean_object* v_as_2948_, size_t v_i_2949_, size_t v_stop_2950_, lean_object* v_b_2951_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2947_, v_as_2948_, v_i_2949_, v_stop_2950_, v_b_2951_);
return v___x_2952_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_2947_ = stack[1].m_obj;
lean_object* v_as_2948_ = stack[2].m_obj;
size_t v_i_2949_ = stack[3].m_num;
size_t v_stop_2950_ = stack[4].m_num;
lean_object* v_b_2951_ = stack[5].m_obj;
lean_object* v_res_2953_;
v_res_2953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_box(0), v_snd_2947_, v_as_2948_, v_i_2949_, v_stop_2950_, v_b_2951_);
stack->m_obj
 = v_res_2953_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2954_, lean_object* v_snd_2955_, lean_object* v_as_2956_, lean_object* v_i_2957_, lean_object* v_stop_2958_, lean_object* v_b_2959_){
_start:
{
size_t v_i_boxed_2960_; size_t v_stop_boxed_2961_; lean_object* v_res_2962_; 
v_i_boxed_2960_ = lean_unbox_usize(v_i_2957_);
lean_dec(v_i_2957_);
v_stop_boxed_2961_ = lean_unbox_usize(v_stop_2958_);
lean_dec(v_stop_2958_);
v_res_2962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(v_00_u03b1_2954_, v_snd_2955_, v_as_2956_, v_i_boxed_2960_, v_stop_boxed_2961_, v_b_2959_);
lean_dec_ref(v_as_2956_);
lean_dec(v_snd_2955_);
return v_res_2962_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object* v_env_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v___x_2966_; lean_object* v_nextMacroScope_2967_; lean_object* v_ngen_2968_; lean_object* v_auxDeclNGen_2969_; lean_object* v_traceState_2970_; lean_object* v_recordedDeps_2971_; lean_object* v_messages_2972_; lean_object* v_infoState_2973_; lean_object* v_snapshotTasks_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2985_; 
v___x_2966_ = lean_st_ref_take(v___y_2964_);
v_nextMacroScope_2967_ = lean_ctor_get(v___x_2966_, 1);
v_ngen_2968_ = lean_ctor_get(v___x_2966_, 2);
v_auxDeclNGen_2969_ = lean_ctor_get(v___x_2966_, 3);
v_traceState_2970_ = lean_ctor_get(v___x_2966_, 4);
v_recordedDeps_2971_ = lean_ctor_get(v___x_2966_, 6);
v_messages_2972_ = lean_ctor_get(v___x_2966_, 7);
v_infoState_2973_ = lean_ctor_get(v___x_2966_, 8);
v_snapshotTasks_2974_ = lean_ctor_get(v___x_2966_, 9);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2985_ == 0)
{
lean_object* v_unused_2986_; lean_object* v_unused_2987_; 
v_unused_2986_ = lean_ctor_get(v___x_2966_, 5);
lean_dec(v_unused_2986_);
v_unused_2987_ = lean_ctor_get(v___x_2966_, 0);
lean_dec(v_unused_2987_);
v___x_2976_ = v___x_2966_;
v_isShared_2977_ = v_isSharedCheck_2985_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_snapshotTasks_2974_);
lean_inc(v_infoState_2973_);
lean_inc(v_messages_2972_);
lean_inc(v_recordedDeps_2971_);
lean_inc(v_traceState_2970_);
lean_inc(v_auxDeclNGen_2969_);
lean_inc(v_ngen_2968_);
lean_inc(v_nextMacroScope_2967_);
lean_dec(v___x_2966_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2985_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2981_; 
v___x_2978_ = lean_box(0);
v___x_2979_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 5, v___x_2979_);
lean_ctor_set(v___x_2976_, 0, v_env_2963_);
v___x_2981_ = v___x_2976_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_env_2963_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_nextMacroScope_2967_);
lean_ctor_set(v_reuseFailAlloc_2984_, 2, v_ngen_2968_);
lean_ctor_set(v_reuseFailAlloc_2984_, 3, v_auxDeclNGen_2969_);
lean_ctor_set(v_reuseFailAlloc_2984_, 4, v_traceState_2970_);
lean_ctor_set(v_reuseFailAlloc_2984_, 5, v___x_2979_);
lean_ctor_set(v_reuseFailAlloc_2984_, 6, v_recordedDeps_2971_);
lean_ctor_set(v_reuseFailAlloc_2984_, 7, v_messages_2972_);
lean_ctor_set(v_reuseFailAlloc_2984_, 8, v_infoState_2973_);
lean_ctor_set(v_reuseFailAlloc_2984_, 9, v_snapshotTasks_2974_);
v___x_2981_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = lean_st_ref_put(v___y_2964_, v___x_2981_);
v___x_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2978_);
return v___x_2983_;
}
}
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2963_ = stack[0].m_obj;
lean_object* v___y_2964_ = stack[1].m_obj;
lean_object* v_res_2988_;
v_res_2988_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2963_, v___y_2964_);
stack->m_obj
 = v_res_2988_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object* v_env_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2989_, v___y_2990_);
lean_dec(v___y_2990_);
return v_res_2992_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object* v_env_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2993_, v___y_2995_);
return v___x_2997_;
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2993_ = stack[0].m_obj;
lean_object* v___y_2994_ = stack[1].m_obj;
lean_object* v___y_2995_ = stack[2].m_obj;
lean_object* v_res_2998_;
v_res_2998_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(v_env_2993_, v___y_2994_, v___y_2995_);
stack->m_obj
 = v_res_2998_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object* v_env_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(v_env_2999_, v___y_3000_, v___y_3001_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object* v_addEntryFn_3004_, lean_object* v___x_3005_, lean_object* v_s_3006_){
_start:
{
lean_object* v_importedEntries_3007_; lean_object* v_state_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3016_; 
v_importedEntries_3007_ = lean_ctor_get(v_s_3006_, 0);
v_state_3008_ = lean_ctor_get(v_s_3006_, 1);
v_isSharedCheck_3016_ = !lean_is_exclusive(v_s_3006_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3010_ = v_s_3006_;
v_isShared_3011_ = v_isSharedCheck_3016_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_state_3008_);
lean_inc(v_importedEntries_3007_);
lean_dec(v_s_3006_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3016_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v_state_3012_; lean_object* v___x_3014_; 
v_state_3012_ = lean_apply_2(v_addEntryFn_3004_, v_state_3008_, v___x_3005_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 1, v_state_3012_);
v___x_3014_ = v___x_3010_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_importedEntries_3007_);
lean_ctor_set(v_reuseFailAlloc_3015_, 1, v_state_3012_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object* v_afterSet_3017_, lean_object* v_getParam_3018_, lean_object* v_ext_3019_, lean_object* v_toAttributeImplCore_3020_, lean_object* v_decl_3021_, lean_object* v_stx_3022_, uint8_t v_kind_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; uint8_t v___y_3031_; lean_object* v_nextMacroScope_3034_; lean_object* v_ngen_3035_; lean_object* v_auxDeclNGen_3036_; lean_object* v_traceState_3037_; lean_object* v_recordedDeps_3038_; lean_object* v_messages_3039_; lean_object* v_infoState_3040_; lean_object* v_snapshotTasks_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; uint8_t v___x_3094_; uint8_t v___x_3095_; 
v___x_3094_ = 0;
v___x_3095_ = l_Lean_instBEqAttributeKind_beq(v_kind_3023_, v___x_3094_);
if (v___x_3095_ == 0)
{
lean_object* v_name_3096_; lean_object* v___x_3097_; 
lean_dec(v_stx_3022_);
lean_dec(v_decl_3021_);
lean_dec_ref(v_ext_3019_);
lean_dec_ref(v_getParam_3018_);
lean_dec_ref(v_afterSet_3017_);
v_name_3096_ = lean_ctor_get(v_toAttributeImplCore_3020_, 1);
lean_inc(v_name_3096_);
lean_dec_ref(v_toAttributeImplCore_3020_);
v___x_3097_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_3096_, v_kind_3023_, v___y_3024_, v___y_3025_);
return v___x_3097_;
}
else
{
goto v___jp_3088_;
}
v___jp_3027_:
{
if (v___y_3031_ == 0)
{
lean_object* v___x_3032_; 
lean_dec_ref(v___y_3028_);
v___x_3032_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v___y_3030_, v___y_3029_);
return v___x_3032_;
}
else
{
lean_dec_ref(v___y_3030_);
return v___y_3028_;
}
}
v___jp_3033_:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3047_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_3048_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3048_, 0, v___y_3046_);
lean_ctor_set(v___x_3048_, 1, v_nextMacroScope_3034_);
lean_ctor_set(v___x_3048_, 2, v_ngen_3035_);
lean_ctor_set(v___x_3048_, 3, v_auxDeclNGen_3036_);
lean_ctor_set(v___x_3048_, 4, v_traceState_3037_);
lean_ctor_set(v___x_3048_, 5, v___x_3047_);
lean_ctor_set(v___x_3048_, 6, v_recordedDeps_3038_);
lean_ctor_set(v___x_3048_, 7, v_messages_3039_);
lean_ctor_set(v___x_3048_, 8, v_infoState_3040_);
lean_ctor_set(v___x_3048_, 9, v_snapshotTasks_3041_);
v___x_3049_ = lean_st_ref_put(v___y_3045_, v___x_3048_);
lean_inc(v___y_3045_);
lean_inc_ref(v___y_3042_);
v___x_3050_ = lean_apply_5(v_afterSet_3017_, v_decl_3021_, v___y_3043_, v___y_3042_, v___y_3045_, lean_box(0));
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_dec_ref(v___y_3044_);
return v___x_3050_;
}
else
{
lean_object* v_a_3051_; uint8_t v___x_3052_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
v___x_3052_ = l_Lean_Exception_isInterrupt(v_a_3051_);
if (v___x_3052_ == 0)
{
uint8_t v___x_3053_; 
v___x_3053_ = l_Lean_Exception_isRuntime(v_a_3051_);
v___y_3028_ = v___x_3050_;
v___y_3029_ = v___y_3045_;
v___y_3030_ = v___y_3044_;
v___y_3031_ = v___x_3053_;
goto v___jp_3027_;
}
else
{
lean_dec(v_a_3051_);
v___y_3028_ = v___x_3050_;
v___y_3029_ = v___y_3045_;
v___y_3030_ = v___y_3044_;
v___y_3031_ = v___x_3052_;
goto v___jp_3027_;
}
}
}
v___jp_3054_:
{
lean_object* v___x_3058_; 
lean_inc(v___y_3057_);
lean_inc_ref(v___y_3056_);
lean_inc(v_decl_3021_);
v___x_3058_ = lean_apply_5(v_getParam_3018_, v_decl_3021_, v_stx_3022_, v___y_3056_, v___y_3057_, lean_box(0));
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3060_; lean_object* v_toEnvExtension_3061_; lean_object* v_env_3062_; lean_object* v_nextMacroScope_3063_; lean_object* v_ngen_3064_; lean_object* v_auxDeclNGen_3065_; lean_object* v_traceState_3066_; lean_object* v_recordedDeps_3067_; lean_object* v_messages_3068_; lean_object* v_infoState_3069_; lean_object* v_snapshotTasks_3070_; lean_object* v_addEntryFn_3071_; lean_object* v_asyncMode_3072_; uint8_t v_logWrites_3073_; lean_object* v___x_3074_; lean_object* v___f_3075_; uint8_t v___x_3076_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc_n(v_a_3059_, 2);
lean_dec_ref_known(v___x_3058_, 1);
v___x_3060_ = lean_st_ref_take(v___y_3057_);
v_toEnvExtension_3061_ = lean_ctor_get(v_ext_3019_, 0);
lean_inc_ref(v_toEnvExtension_3061_);
v_env_3062_ = lean_ctor_get(v___x_3060_, 0);
lean_inc_ref(v_env_3062_);
v_nextMacroScope_3063_ = lean_ctor_get(v___x_3060_, 1);
lean_inc(v_nextMacroScope_3063_);
v_ngen_3064_ = lean_ctor_get(v___x_3060_, 2);
lean_inc_ref(v_ngen_3064_);
v_auxDeclNGen_3065_ = lean_ctor_get(v___x_3060_, 3);
lean_inc_ref(v_auxDeclNGen_3065_);
v_traceState_3066_ = lean_ctor_get(v___x_3060_, 4);
lean_inc_ref(v_traceState_3066_);
v_recordedDeps_3067_ = lean_ctor_get(v___x_3060_, 6);
lean_inc_ref(v_recordedDeps_3067_);
v_messages_3068_ = lean_ctor_get(v___x_3060_, 7);
lean_inc_ref(v_messages_3068_);
v_infoState_3069_ = lean_ctor_get(v___x_3060_, 8);
lean_inc_ref(v_infoState_3069_);
v_snapshotTasks_3070_ = lean_ctor_get(v___x_3060_, 9);
lean_inc_ref(v_snapshotTasks_3070_);
lean_dec(v___x_3060_);
v_addEntryFn_3071_ = lean_ctor_get(v_ext_3019_, 3);
lean_inc(v_addEntryFn_3071_);
lean_dec_ref(v_ext_3019_);
v_asyncMode_3072_ = lean_ctor_get(v_toEnvExtension_3061_, 2);
lean_inc(v_asyncMode_3072_);
v_logWrites_3073_ = lean_ctor_get_uint8(v_toEnvExtension_3061_, sizeof(void*)*6);
lean_inc(v_decl_3021_);
v___x_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3074_, 0, v_decl_3021_);
lean_ctor_set(v___x_3074_, 1, v_a_3059_);
v___f_3075_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3075_, 0, v_addEntryFn_3071_);
lean_closure_set(v___f_3075_, 1, v___x_3074_);
v___x_3076_ = 1;
if (v_logWrites_3073_ == 0)
{
lean_object* v___x_3077_; 
lean_inc(v_decl_3021_);
v___x_3077_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3061_, v_env_3062_, v___f_3075_, v_asyncMode_3072_, v_decl_3021_, v___x_3076_);
lean_dec(v_asyncMode_3072_);
v_nextMacroScope_3034_ = v_nextMacroScope_3063_;
v_ngen_3035_ = v_ngen_3064_;
v_auxDeclNGen_3036_ = v_auxDeclNGen_3065_;
v_traceState_3037_ = v_traceState_3066_;
v_recordedDeps_3038_ = v_recordedDeps_3067_;
v_messages_3039_ = v_messages_3068_;
v_infoState_3040_ = v_infoState_3069_;
v_snapshotTasks_3041_ = v_snapshotTasks_3070_;
v___y_3042_ = v___y_3056_;
v___y_3043_ = v_a_3059_;
v___y_3044_ = v___y_3055_;
v___y_3045_ = v___y_3057_;
v___y_3046_ = v___x_3077_;
goto v___jp_3033_;
}
else
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
lean_inc_n(v_decl_3021_, 2);
v___x_3078_ = l_Lean_Environment_logDeclChange(v_env_3062_, v_decl_3021_);
v___x_3079_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3061_, v___x_3078_, v___f_3075_, v_asyncMode_3072_, v_decl_3021_, v___x_3076_);
lean_dec(v_asyncMode_3072_);
v_nextMacroScope_3034_ = v_nextMacroScope_3063_;
v_ngen_3035_ = v_ngen_3064_;
v_auxDeclNGen_3036_ = v_auxDeclNGen_3065_;
v_traceState_3037_ = v_traceState_3066_;
v_recordedDeps_3038_ = v_recordedDeps_3067_;
v_messages_3039_ = v_messages_3068_;
v_infoState_3040_ = v_infoState_3069_;
v_snapshotTasks_3041_ = v_snapshotTasks_3070_;
v___y_3042_ = v___y_3056_;
v___y_3043_ = v_a_3059_;
v___y_3044_ = v___y_3055_;
v___y_3045_ = v___y_3057_;
v___y_3046_ = v___x_3079_;
goto v___jp_3033_;
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec_ref(v___y_3055_);
lean_dec(v_decl_3021_);
lean_dec_ref(v_ext_3019_);
lean_dec_ref(v_afterSet_3017_);
v_a_3080_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3058_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3058_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
v___jp_3088_:
{
lean_object* v___x_3089_; lean_object* v_env_3090_; lean_object* v___x_3091_; 
v___x_3089_ = lean_st_ref_get(v___y_3025_);
v_env_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc_ref(v_env_3090_);
lean_dec(v___x_3089_);
v___x_3091_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3090_, v_decl_3021_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_dec_ref(v_toAttributeImplCore_3020_);
v___y_3055_ = v_env_3090_;
v___y_3056_ = v___y_3024_;
v___y_3057_ = v___y_3025_;
goto v___jp_3054_;
}
else
{
lean_object* v_name_3092_; lean_object* v___x_3093_; 
lean_dec_ref_known(v___x_3091_, 1);
lean_dec_ref(v_env_3090_);
lean_dec(v_stx_3022_);
lean_dec_ref(v_ext_3019_);
lean_dec_ref(v_getParam_3018_);
lean_dec_ref(v_afterSet_3017_);
v_name_3092_ = lean_ctor_get(v_toAttributeImplCore_3020_, 1);
lean_inc(v_name_3092_);
lean_dec_ref(v_toAttributeImplCore_3020_);
v___x_3093_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_3092_, v_decl_3021_, v___y_3024_, v___y_3025_);
return v___x_3093_;
}
}
}
}
LEAN_EXPORT void l_Lean_registerParametricAttributeForExt___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_afterSet_3017_ = stack[0].m_obj;
lean_object* v_getParam_3018_ = stack[1].m_obj;
lean_object* v_ext_3019_ = stack[2].m_obj;
lean_object* v_toAttributeImplCore_3020_ = stack[3].m_obj;
lean_object* v_decl_3021_ = stack[4].m_obj;
lean_object* v_stx_3022_ = stack[5].m_obj;
uint8_t v_kind_3023_ = stack[6].m_num;
lean_object* v___y_3024_ = stack[7].m_obj;
lean_object* v___y_3025_ = stack[8].m_obj;
lean_object* v_res_3098_;
v_res_3098_ = l_Lean_registerParametricAttributeForExt___redArg___lam__1(v_afterSet_3017_, v_getParam_3018_, v_ext_3019_, v_toAttributeImplCore_3020_, v_decl_3021_, v_stx_3022_, v_kind_3023_, v___y_3024_, v___y_3025_);
stack->m_obj
 = v_res_3098_;
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object* v_afterSet_3099_, lean_object* v_getParam_3100_, lean_object* v_ext_3101_, lean_object* v_toAttributeImplCore_3102_, lean_object* v_decl_3103_, lean_object* v_stx_3104_, lean_object* v_kind_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
uint8_t v_kind_boxed_3109_; lean_object* v_res_3110_; 
v_kind_boxed_3109_ = lean_unbox(v_kind_3105_);
v_res_3110_ = l_Lean_registerParametricAttributeForExt___redArg___lam__1(v_afterSet_3099_, v_getParam_3100_, v_ext_3101_, v_toAttributeImplCore_3102_, v_decl_3103_, v_stx_3104_, v_kind_boxed_3109_, v___y_3106_, v___y_3107_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
return v_res_3110_;
}
}
lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__2(lean_object* v_toAttributeImplCore_3111_, lean_object* v_decl_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v_name_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v_name_3116_ = lean_ctor_get(v_toAttributeImplCore_3111_, 1);
lean_inc(v_name_3116_);
lean_dec_ref(v_toAttributeImplCore_3111_);
v___x_3117_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3118_ = l_Lean_MessageData_ofName(v_name_3116_);
v___x_3119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3117_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v___x_3120_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3119_);
lean_ctor_set(v___x_3121_, 1, v___x_3120_);
v___x_3122_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3121_, v___y_3113_, v___y_3114_);
return v___x_3122_;
}
}
LEAN_EXPORT void l_Lean_registerParametricAttributeForExt___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_toAttributeImplCore_3111_ = stack[0].m_obj;
lean_object* v_decl_3112_ = stack[1].m_obj;
lean_object* v___y_3113_ = stack[2].m_obj;
lean_object* v___y_3114_ = stack[3].m_obj;
lean_object* v_res_3123_;
v_res_3123_ = l_Lean_registerParametricAttributeForExt___redArg___lam__2(v_toAttributeImplCore_3111_, v_decl_3112_, v___y_3113_, v___y_3114_);
stack->m_obj
 = v_res_3123_;
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__2___boxed(lean_object* v_toAttributeImplCore_3124_, lean_object* v_decl_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Lean_registerParametricAttributeForExt___redArg___lam__2(v_toAttributeImplCore_3124_, v_decl_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v_decl_3125_);
return v_res_3129_;
}
}
lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object* v_impl_3130_, lean_object* v_ext_3131_){
_start:
{
lean_object* v_toAttributeImplCore_3133_; lean_object* v_getParam_3134_; lean_object* v_afterSet_3135_; uint8_t v_preserveOrder_3136_; lean_object* v___f_3137_; lean_object* v___f_3138_; lean_object* v_attrImpl_3139_; lean_object* v___x_3140_; 
v_toAttributeImplCore_3133_ = lean_ctor_get(v_impl_3130_, 0);
lean_inc_ref_n(v_toAttributeImplCore_3133_, 3);
v_getParam_3134_ = lean_ctor_get(v_impl_3130_, 1);
lean_inc_ref(v_getParam_3134_);
v_afterSet_3135_ = lean_ctor_get(v_impl_3130_, 2);
lean_inc_ref(v_afterSet_3135_);
v_preserveOrder_3136_ = lean_ctor_get_uint8(v_impl_3130_, sizeof(void*)*4);
lean_dec_ref(v_impl_3130_);
lean_inc_ref(v_ext_3131_);
v___f_3137_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3137_, 0, v_afterSet_3135_);
lean_closure_set(v___f_3137_, 1, v_getParam_3134_);
lean_closure_set(v___f_3137_, 2, v_ext_3131_);
lean_closure_set(v___f_3137_, 3, v_toAttributeImplCore_3133_);
v___f_3138_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__2___boxed), 5, 1);
lean_closure_set(v___f_3138_, 0, v_toAttributeImplCore_3133_);
v_attrImpl_3139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_attrImpl_3139_, 0, v_toAttributeImplCore_3133_);
lean_ctor_set(v_attrImpl_3139_, 1, v___f_3137_);
lean_ctor_set(v_attrImpl_3139_, 2, v___f_3138_);
lean_inc_ref(v_attrImpl_3139_);
v___x_3140_ = l_Lean_registerBuiltinAttribute(v_attrImpl_3139_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3148_; 
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3148_ == 0)
{
lean_object* v_unused_3149_; 
v_unused_3149_ = lean_ctor_get(v___x_3140_, 0);
lean_dec(v_unused_3149_);
v___x_3142_ = v___x_3140_;
v_isShared_3143_ = v_isSharedCheck_3148_;
goto v_resetjp_3141_;
}
else
{
lean_dec(v___x_3140_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3148_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3144_; lean_object* v___x_3146_; 
v___x_3144_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3144_, 0, v_attrImpl_3139_);
lean_ctor_set(v___x_3144_, 1, v_ext_3131_);
lean_ctor_set_uint8(v___x_3144_, sizeof(void*)*2, v_preserveOrder_3136_);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v___x_3144_);
v___x_3146_ = v___x_3142_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3144_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec_ref_known(v_attrImpl_3139_, 3);
lean_dec_ref(v_ext_3131_);
v_a_3150_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3140_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3140_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_registerParametricAttributeForExt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_impl_3130_ = stack[0].m_obj;
lean_object* v_ext_3131_ = stack[1].m_obj;
lean_object* v_res_3158_;
v_res_3158_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3130_, v_ext_3131_);
stack->m_obj
 = v_res_3158_;
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object* v_impl_3159_, lean_object* v_ext_3160_, lean_object* v_a_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3159_, v_ext_3160_);
return v_res_3162_;
}
}
lean_object* l_Lean_registerParametricAttributeForExt(lean_object* v_00_u03b1_3163_, lean_object* v_impl_3164_, lean_object* v_ext_3165_){
_start:
{
lean_object* v___x_3167_; 
v___x_3167_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3164_, v_ext_3165_);
return v___x_3167_;
}
}
LEAN_EXPORT void l_Lean_registerParametricAttributeForExt_0interp(lean_interpreter_value* stack)
{
lean_object* v_impl_3164_ = stack[1].m_obj;
lean_object* v_ext_3165_ = stack[2].m_obj;
lean_object* v_res_3168_;
v_res_3168_ = l_Lean_registerParametricAttributeForExt(lean_box(0), v_impl_3164_, v_ext_3165_);
stack->m_obj
 = v_res_3168_;
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object* v_00_u03b1_3169_, lean_object* v_impl_3170_, lean_object* v_ext_3171_, lean_object* v_a_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l_Lean_registerParametricAttributeForExt(v_00_u03b1_3169_, v_impl_3170_, v_ext_3171_);
return v_res_3173_;
}
}
lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_3174_){
_start:
{
lean_object* v_toAttributeImplCore_3176_; uint8_t v_preserveOrder_3177_; lean_object* v_filterExport_3178_; lean_object* v_ref_3179_; uint8_t v___x_3180_; lean_object* v___x_3181_; 
v_toAttributeImplCore_3176_ = lean_ctor_get(v_impl_3174_, 0);
v_preserveOrder_3177_ = lean_ctor_get_uint8(v_impl_3174_, sizeof(void*)*4);
v_filterExport_3178_ = lean_ctor_get(v_impl_3174_, 3);
v_ref_3179_ = lean_ctor_get(v_toAttributeImplCore_3176_, 0);
v___x_3180_ = 0;
lean_inc_ref(v_filterExport_3178_);
lean_inc(v_ref_3179_);
v___x_3181_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_3179_, v_preserveOrder_3177_, v_filterExport_3178_, v___x_3180_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3182_; lean_object* v___x_3183_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3182_);
lean_dec_ref_known(v___x_3181_, 1);
v___x_3183_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3174_, v_a_3182_);
return v___x_3183_;
}
else
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
lean_dec_ref(v_impl_3174_);
v_a_3184_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_3181_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3181_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3184_);
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
LEAN_EXPORT void l_Lean_registerParametricAttribute___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_impl_3174_ = stack[0].m_obj;
lean_object* v_res_3192_;
v_res_3192_ = l_Lean_registerParametricAttribute___redArg(v_impl_3174_);
stack->m_obj
 = v_res_3192_;
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_3193_, lean_object* v_a_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_Lean_registerParametricAttribute___redArg(v_impl_3193_);
return v_res_3195_;
}
}
lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_3196_, lean_object* v_impl_3197_){
_start:
{
lean_object* v___x_3199_; 
v___x_3199_ = l_Lean_registerParametricAttribute___redArg(v_impl_3197_);
return v___x_3199_;
}
}
LEAN_EXPORT void l_Lean_registerParametricAttribute_0interp(lean_interpreter_value* stack)
{
lean_object* v_impl_3197_ = stack[1].m_obj;
lean_object* v_res_3200_;
v_res_3200_ = l_Lean_registerParametricAttribute(lean_box(0), v_impl_3197_);
stack->m_obj
 = v_res_3200_;
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_3201_, lean_object* v_impl_3202_, lean_object* v_a_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l_Lean_registerParametricAttribute(v_00_u03b1_3201_, v_impl_3202_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(lean_object* v_decl_3205_, lean_object* v___x_3206_, lean_object* v___x_3207_, lean_object* v_a_3208_, lean_object* v_x_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v_fst_3211_; uint8_t v___x_3212_; 
v_fst_3211_ = lean_ctor_get(v_a_3208_, 0);
v___x_3212_ = lean_name_eq(v_fst_3211_, v_decl_3205_);
if (v___x_3212_ == 0)
{
lean_object* v___x_3213_; 
lean_dec_ref(v_a_3208_);
v___x_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3206_);
return v___x_3213_;
}
else
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
lean_dec_ref(v___x_3206_);
v___x_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3214_, 0, v_a_3208_);
v___x_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
v___x_3216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
lean_ctor_set(v___x_3216_, 1, v___x_3207_);
v___x_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
return v___x_3217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed(lean_object* v_decl_3218_, lean_object* v___x_3219_, lean_object* v___x_3220_, lean_object* v_a_3221_, lean_object* v_x_3222_, lean_object* v___y_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(v_decl_3218_, v___x_3219_, v___x_3220_, v_a_3221_, v_x_3222_, v___y_3223_);
lean_dec_ref(v___y_3223_);
lean_dec(v_decl_3218_);
return v_res_3224_;
}
}
lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object* v_inst_3252_, lean_object* v_ext_3253_, uint8_t v_preserveOrder_3254_, lean_object* v_env_3255_, lean_object* v_decl_3256_){
_start:
{
lean_object* v___y_3258_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3269_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3270_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3255_, v_decl_3256_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_toEnvExtension_3271_; lean_object* v_asyncMode_3272_; lean_object* v___x_3273_; uint8_t v___x_3274_; lean_object* v___x_3275_; lean_object* v_snd_3276_; lean_object* v___x_3277_; 
lean_dec(v_inst_3252_);
v_toEnvExtension_3271_ = lean_ctor_get(v_ext_3253_, 0);
v_asyncMode_3272_ = lean_ctor_get(v_toEnvExtension_3271_, 2);
v___x_3273_ = lean_box(0);
v___x_3274_ = 0;
v___x_3275_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3269_, v_ext_3253_, v_env_3255_, v_asyncMode_3272_, v___x_3273_, v___x_3274_);
v_snd_3276_ = lean_ctor_get(v___x_3275_, 1);
lean_inc(v_snd_3276_);
lean_dec(v___x_3275_);
v___x_3277_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3276_, v_decl_3256_);
lean_dec(v_decl_3256_);
lean_dec(v_snd_3276_);
return v___x_3277_;
}
else
{
if (v_preserveOrder_3254_ == 0)
{
lean_object* v_val_3278_; uint8_t v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; uint8_t v___x_3283_; 
v_val_3278_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_val_3278_);
lean_dec_ref_known(v___x_3270_, 1);
v___x_3279_ = 0;
v___x_3280_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3269_, v_ext_3253_, v_env_3255_, v_val_3278_, v___x_3279_);
lean_dec(v_val_3278_);
lean_dec_ref(v_env_3255_);
v___x_3281_ = lean_unsigned_to_nat(0u);
v___x_3282_ = lean_array_get_size(v___x_3280_);
v___x_3283_ = lean_nat_dec_lt(v___x_3281_, v___x_3282_);
if (v___x_3283_ == 0)
{
lean_object* v___x_3284_; 
lean_dec_ref(v___x_3280_);
lean_dec(v_decl_3256_);
lean_dec(v_inst_3252_);
v___x_3284_ = lean_box(0);
return v___x_3284_;
}
else
{
lean_object* v___x_3285_; lean_object* v___x_3286_; uint8_t v___x_3287_; 
v___x_3285_ = lean_unsigned_to_nat(1u);
v___x_3286_ = lean_nat_sub(v___x_3282_, v___x_3285_);
v___x_3287_ = lean_nat_dec_le(v___x_3281_, v___x_3286_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; 
lean_dec(v___x_3286_);
lean_dec_ref(v___x_3280_);
lean_dec(v_decl_3256_);
lean_dec(v_inst_3252_);
v___x_3288_ = lean_box(0);
return v___x_3288_;
}
else
{
lean_object* v___f_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___f_3289_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
v___x_3290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3290_, 0, v_decl_3256_);
lean_ctor_set(v___x_3290_, 1, v_inst_3252_);
v___x_3291_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3292_ = l_Array_binSearchAux___redArg(v___f_3289_, v___x_3291_, v___x_3280_, v___x_3290_, v___x_3281_, v___x_3286_);
lean_dec_ref(v___x_3280_);
v___y_3258_ = v___x_3292_;
goto v___jp_3257_;
}
}
}
else
{
lean_object* v_val_3293_; uint8_t v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___f_3300_; size_t v_sz_3301_; size_t v___x_3302_; lean_object* v___x_3303_; lean_object* v_fst_3304_; 
lean_dec(v_inst_3252_);
v_val_3293_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_val_3293_);
lean_dec_ref_known(v___x_3270_, 1);
v___x_3294_ = 0;
v___x_3295_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3269_, v_ext_3253_, v_env_3255_, v_val_3293_, v___x_3294_);
lean_dec(v_val_3293_);
lean_dec_ref(v_env_3255_);
v___x_3296_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12));
v___x_3297_ = lean_box(0);
v___x_3298_ = lean_box(0);
v___x_3299_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13));
v___f_3300_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3300_, 0, v_decl_3256_);
lean_closure_set(v___f_3300_, 1, v___x_3299_);
lean_closure_set(v___f_3300_, 2, v___x_3298_);
v_sz_3301_ = lean_array_size(v___x_3295_);
v___x_3302_ = ((size_t)0ULL);
v___x_3303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3296_, v___x_3295_, v___f_3300_, v_sz_3301_, v___x_3302_, v___x_3299_);
v_fst_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_fst_3304_);
lean_dec(v___x_3303_);
if (lean_obj_tag(v_fst_3304_) == 0)
{
return v___x_3297_;
}
else
{
lean_object* v_val_3305_; 
v_val_3305_ = lean_ctor_get(v_fst_3304_, 0);
lean_inc(v_val_3305_);
lean_dec_ref_known(v_fst_3304_, 1);
v___y_3258_ = v_val_3305_;
goto v___jp_3257_;
}
}
}
v___jp_3257_:
{
if (lean_obj_tag(v___y_3258_) == 0)
{
lean_object* v___x_3259_; 
v___x_3259_ = lean_box(0);
return v___x_3259_;
}
else
{
lean_object* v_val_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3268_; 
v_val_3260_ = lean_ctor_get(v___y_3258_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___y_3258_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3262_ = v___y_3258_;
v_isShared_3263_ = v_isSharedCheck_3268_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_val_3260_);
lean_dec(v___y_3258_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3268_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v_snd_3264_; lean_object* v___x_3266_; 
v_snd_3264_ = lean_ctor_get(v_val_3260_, 1);
lean_inc(v_snd_3264_);
lean_dec(v_val_3260_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 0, v_snd_3264_);
v___x_3266_ = v___x_3262_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_snd_3264_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3252_ = stack[0].m_obj;
lean_object* v_ext_3253_ = stack[1].m_obj;
uint8_t v_preserveOrder_3254_ = stack[2].m_num;
lean_object* v_env_3255_ = stack[3].m_obj;
lean_object* v_decl_3256_ = stack[4].m_obj;
lean_object* v_res_3306_;
v_res_3306_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3252_, v_ext_3253_, v_preserveOrder_3254_, v_env_3255_, v_decl_3256_);
stack->m_obj
 = v_res_3306_;
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object* v_inst_3307_, lean_object* v_ext_3308_, lean_object* v_preserveOrder_3309_, lean_object* v_env_3310_, lean_object* v_decl_3311_){
_start:
{
uint8_t v_preserveOrder_boxed_3312_; lean_object* v_res_3313_; 
v_preserveOrder_boxed_3312_ = lean_unbox(v_preserveOrder_3309_);
v_res_3313_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3307_, v_ext_3308_, v_preserveOrder_boxed_3312_, v_env_3310_, v_decl_3311_);
lean_dec_ref(v_ext_3308_);
return v_res_3313_;
}
}
lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object* v_00_u03b1_3314_, lean_object* v_inst_3315_, lean_object* v_ext_3316_, uint8_t v_preserveOrder_3317_, lean_object* v_env_3318_, lean_object* v_decl_3319_){
_start:
{
lean_object* v___x_3320_; 
v___x_3320_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3315_, v_ext_3316_, v_preserveOrder_3317_, v_env_3318_, v_decl_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT void l_Lean_ParametricAttribute_getParamFromExt_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3315_ = stack[1].m_obj;
lean_object* v_ext_3316_ = stack[2].m_obj;
uint8_t v_preserveOrder_3317_ = stack[3].m_num;
lean_object* v_env_3318_ = stack[4].m_obj;
lean_object* v_decl_3319_ = stack[5].m_obj;
lean_object* v_res_3321_;
v_res_3321_ = l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_box(0), v_inst_3315_, v_ext_3316_, v_preserveOrder_3317_, v_env_3318_, v_decl_3319_);
stack->m_obj
 = v_res_3321_;
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object* v_00_u03b1_3322_, lean_object* v_inst_3323_, lean_object* v_ext_3324_, lean_object* v_preserveOrder_3325_, lean_object* v_env_3326_, lean_object* v_decl_3327_){
_start:
{
uint8_t v_preserveOrder_boxed_3328_; lean_object* v_res_3329_; 
v_preserveOrder_boxed_3328_ = lean_unbox(v_preserveOrder_3325_);
v_res_3329_ = l_Lean_ParametricAttribute_getParamFromExt_x3f(v_00_u03b1_3322_, v_inst_3323_, v_ext_3324_, v_preserveOrder_boxed_3328_, v_env_3326_, v_decl_3327_);
lean_dec_ref(v_ext_3324_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3330_, lean_object* v_attr_3331_, lean_object* v_env_3332_, lean_object* v_decl_3333_){
_start:
{
lean_object* v_ext_3334_; uint8_t v_preserveOrder_3335_; lean_object* v___x_3336_; 
v_ext_3334_ = lean_ctor_get(v_attr_3331_, 1);
v_preserveOrder_3335_ = lean_ctor_get_uint8(v_attr_3331_, sizeof(void*)*2);
v___x_3336_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3330_, v_ext_3334_, v_preserveOrder_3335_, v_env_3332_, v_decl_3333_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3337_, lean_object* v_attr_3338_, lean_object* v_env_3339_, lean_object* v_decl_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3337_, v_attr_3338_, v_env_3339_, v_decl_3340_);
lean_dec_ref(v_attr_3338_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3342_, lean_object* v_inst_3343_, lean_object* v_attr_3344_, lean_object* v_env_3345_, lean_object* v_decl_3346_){
_start:
{
lean_object* v___x_3347_; 
v___x_3347_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3343_, v_attr_3344_, v_env_3345_, v_decl_3346_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3348_, lean_object* v_inst_3349_, lean_object* v_attr_3350_, lean_object* v_env_3351_, lean_object* v_decl_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3348_, v_inst_3349_, v_attr_3350_, v_env_3351_, v_decl_3352_);
lean_dec_ref(v_attr_3350_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object* v_ext_3358_, lean_object* v_attr_3359_, lean_object* v_env_3360_, lean_object* v_decl_3361_, lean_object* v_param_3362_){
_start:
{
lean_object* v___x_3363_; 
v___x_3363_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3360_, v_decl_3361_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_toEnvExtension_3364_; lean_object* v_addEntryFn_3365_; lean_object* v_asyncMode_3366_; uint8_t v_logWrites_3367_; uint8_t v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v_snd_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3407_; 
v_toEnvExtension_3364_ = lean_ctor_get(v_ext_3358_, 0);
lean_inc_ref(v_toEnvExtension_3364_);
v_addEntryFn_3365_ = lean_ctor_get(v_ext_3358_, 3);
lean_inc(v_addEntryFn_3365_);
v_asyncMode_3366_ = lean_ctor_get(v_toEnvExtension_3364_, 2);
lean_inc(v_asyncMode_3366_);
v_logWrites_3367_ = lean_ctor_get_uint8(v_toEnvExtension_3364_, sizeof(void*)*6);
v___x_3368_ = 0;
v___x_3369_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3370_ = lean_box(0);
lean_inc_ref(v_env_3360_);
v___x_3371_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3369_, v_ext_3358_, v_env_3360_, v_asyncMode_3366_, v___x_3370_, v___x_3368_);
lean_dec_ref(v_ext_3358_);
v_snd_3372_ = lean_ctor_get(v___x_3371_, 1);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3407_ == 0)
{
lean_object* v_unused_3408_; 
v_unused_3408_ = lean_ctor_get(v___x_3371_, 0);
lean_dec(v_unused_3408_);
v___x_3374_ = v___x_3371_;
v_isShared_3375_ = v_isSharedCheck_3407_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_snd_3372_);
lean_dec(v___x_3371_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3407_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; 
v___x_3376_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3372_, v_decl_3361_);
lean_dec(v_snd_3372_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v___x_3378_; 
lean_dec_ref(v_attr_3359_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 1, v_param_3362_);
lean_ctor_set(v___x_3374_, 0, v_decl_3361_);
v___x_3378_ = v___x_3374_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_decl_3361_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v_param_3362_);
v___x_3378_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
lean_object* v___f_3379_; uint8_t v___x_3380_; 
v___f_3379_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3379_, 0, v_addEntryFn_3365_);
lean_closure_set(v___f_3379_, 1, v___x_3378_);
v___x_3380_ = 1;
if (v_logWrites_3367_ == 0)
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3364_, v_env_3360_, v___f_3379_, v_asyncMode_3366_, v___x_3370_, v___x_3380_);
lean_dec(v_asyncMode_3366_);
v___x_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3381_);
return v___x_3382_;
}
else
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
lean_inc_ref(v_toEnvExtension_3364_);
v___x_3383_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3364_, v_env_3360_);
lean_dec_ref(v_env_3360_);
v___x_3384_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3364_, v___x_3383_, v___f_3379_, v_asyncMode_3366_, v___x_3370_, v___x_3380_);
lean_dec(v_asyncMode_3366_);
v___x_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
return v___x_3385_;
}
}
}
else
{
lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3405_; 
lean_del_object(v___x_3374_);
lean_dec(v_asyncMode_3366_);
lean_dec(v_addEntryFn_3365_);
lean_dec_ref(v_toEnvExtension_3364_);
lean_dec(v_param_3362_);
lean_dec_ref(v_env_3360_);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3405_ == 0)
{
lean_object* v_unused_3406_; 
v_unused_3406_ = lean_ctor_get(v___x_3376_, 0);
lean_dec(v_unused_3406_);
v___x_3388_ = v___x_3376_;
v_isShared_3389_ = v_isSharedCheck_3405_;
goto v_resetjp_3387_;
}
else
{
lean_dec(v___x_3376_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3405_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v_toAttributeImplCore_3390_; lean_object* v_name_3391_; uint8_t v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3403_; 
v_toAttributeImplCore_3390_ = lean_ctor_get(v_attr_3359_, 0);
lean_inc_ref(v_toAttributeImplCore_3390_);
lean_dec_ref(v_attr_3359_);
v_name_3391_ = lean_ctor_get(v_toAttributeImplCore_3390_, 1);
lean_inc(v_name_3391_);
lean_dec_ref(v_toAttributeImplCore_3390_);
v___x_3392_ = 1;
v___x_3393_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3394_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3391_, v___x_3392_);
v___x_3395_ = lean_string_append(v___x_3393_, v___x_3394_);
lean_dec_ref(v___x_3394_);
v___x_3396_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3397_ = lean_string_append(v___x_3395_, v___x_3396_);
v___x_3398_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3361_, v___x_3392_);
v___x_3399_ = lean_string_append(v___x_3397_, v___x_3398_);
lean_dec_ref(v___x_3398_);
v___x_3400_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2));
v___x_3401_ = lean_string_append(v___x_3399_, v___x_3400_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set_tag(v___x_3388_, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3401_);
v___x_3403_ = v___x_3388_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3401_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
}
else
{
lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3427_; 
lean_dec(v_param_3362_);
lean_dec_ref(v_env_3360_);
lean_dec_ref(v_ext_3358_);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3427_ == 0)
{
lean_object* v_unused_3428_; 
v_unused_3428_ = lean_ctor_get(v___x_3363_, 0);
lean_dec(v_unused_3428_);
v___x_3410_ = v___x_3363_;
v_isShared_3411_ = v_isSharedCheck_3427_;
goto v_resetjp_3409_;
}
else
{
lean_dec(v___x_3363_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3427_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v_toAttributeImplCore_3412_; lean_object* v_name_3413_; uint8_t v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3425_; 
v_toAttributeImplCore_3412_ = lean_ctor_get(v_attr_3359_, 0);
lean_inc_ref(v_toAttributeImplCore_3412_);
lean_dec_ref(v_attr_3359_);
v_name_3413_ = lean_ctor_get(v_toAttributeImplCore_3412_, 1);
lean_inc(v_name_3413_);
lean_dec_ref(v_toAttributeImplCore_3412_);
v___x_3414_ = 1;
v___x_3415_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3416_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3413_, v___x_3414_);
v___x_3417_ = lean_string_append(v___x_3415_, v___x_3416_);
lean_dec_ref(v___x_3416_);
v___x_3418_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3419_ = lean_string_append(v___x_3417_, v___x_3418_);
v___x_3420_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3361_, v___x_3414_);
v___x_3421_ = lean_string_append(v___x_3419_, v___x_3420_);
lean_dec_ref(v___x_3420_);
v___x_3422_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3));
v___x_3423_ = lean_string_append(v___x_3421_, v___x_3422_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set_tag(v___x_3410_, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3423_);
v___x_3425_ = v___x_3410_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3423_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object* v_00_u03b1_3429_, lean_object* v_ext_3430_, lean_object* v_attr_3431_, lean_object* v_env_3432_, lean_object* v_decl_3433_, lean_object* v_param_3434_){
_start:
{
lean_object* v___x_3435_; 
v___x_3435_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3430_, v_attr_3431_, v_env_3432_, v_decl_3433_, v_param_3434_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3436_, lean_object* v_env_3437_, lean_object* v_decl_3438_, lean_object* v_param_3439_){
_start:
{
lean_object* v_attr_3440_; lean_object* v_ext_3441_; lean_object* v___x_3442_; 
v_attr_3440_ = lean_ctor_get(v_attr_3436_, 0);
lean_inc_ref(v_attr_3440_);
v_ext_3441_ = lean_ctor_get(v_attr_3436_, 1);
lean_inc_ref(v_ext_3441_);
lean_dec_ref(v_attr_3436_);
v___x_3442_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3441_, v_attr_3440_, v_env_3437_, v_decl_3438_, v_param_3439_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3443_, lean_object* v_attr_3444_, lean_object* v_env_3445_, lean_object* v_decl_3446_, lean_object* v_param_3447_){
_start:
{
lean_object* v___x_3448_; 
v___x_3448_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3444_, v_env_3445_, v_decl_3446_, v_param_3447_);
return v___x_3448_;
}
}
lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(lean_object* v_x_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3452_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
return v___x_3453_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3449_ = stack[0].m_obj;
lean_object* v___y_3450_ = stack[1].m_obj;
lean_object* v_res_3454_;
v_res_3454_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(v_x_3449_, v___y_3450_);
stack->m_obj
 = v_res_3454_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0___boxed(lean_object* v_x_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(v_x_3455_, v___y_3456_);
lean_dec_ref(v___y_3456_);
lean_dec_ref(v_x_3455_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(lean_object* v_s_3459_, lean_object* v_x_3460_){
_start:
{
lean_inc(v_s_3459_);
return v_s_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1___boxed(lean_object* v_s_3461_, lean_object* v_x_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(v_s_3461_, v_x_3462_);
lean_dec_ref(v_x_3462_);
lean_dec(v_s_3461_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(lean_object* v_x_3464_, lean_object* v_x_3465_){
_start:
{
lean_object* v___x_3466_; 
v___x_3466_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_3466_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2___boxed(lean_object* v_x_3467_, lean_object* v_x_3468_){
_start:
{
lean_object* v_res_3469_; 
v_res_3469_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(v_x_3467_, v_x_3468_);
lean_dec(v_x_3468_);
lean_dec_ref(v_x_3467_);
return v_res_3469_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3(void){
_start:
{
lean_object* v___f_3473_; lean_object* v___f_3474_; lean_object* v___f_3475_; lean_object* v___f_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___f_3473_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3474_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2));
v___f_3475_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1));
v___f_3476_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0));
v___x_3477_ = lean_box(0);
v___x_3478_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_3479_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3478_);
lean_ctor_set(v___x_3479_, 1, v___x_3477_);
lean_ctor_set(v___x_3479_, 2, v___f_3476_);
lean_ctor_set(v___x_3479_, 3, v___f_3475_);
lean_ctor_set(v___x_3479_, 4, v___f_3474_);
lean_ctor_set(v___x_3479_, 5, v___f_3473_);
return v___x_3479_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3480_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3);
v___x_3481_ = lean_box(0);
v___x_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
lean_ctor_set(v___x_3482_, 1, v___x_3480_);
return v___x_3482_;
}
}
lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg(){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4);
return v___x_3484_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedEnumAttributes_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3485_;
v_res_3485_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
stack->m_obj
 = v_res_3485_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___boxed(lean_object* v___dummy_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v_res_3487_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__0(void){
_start:
{
lean_object* v___x_3488_; 
v___x_3488_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3489_){
_start:
{
lean_object* v___x_3490_; 
v___x_3490_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3490_;
}
}
lean_object* l_Lean_instInhabitedEnumAttributes___redArg(){
_start:
{
lean_object* v___x_3492_; 
v___x_3492_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3492_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedEnumAttributes___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3493_;
v_res_3493_ = l_Lean_instInhabitedEnumAttributes___redArg();
stack->m_obj
 = v_res_3493_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg___boxed(lean_object* v___dummy_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Lean_instInhabitedEnumAttributes___redArg();
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3496_){
_start:
{
lean_object* v___x_3497_; 
v___x_3497_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3497_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3499_){
_start:
{
lean_object* v___x_3500_; 
v___x_3500_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3501_){
_start:
{
lean_object* v_res_3502_; 
v_res_3502_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3501_);
lean_dec(v_x_3501_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3503_, lean_object* v_x_3504_, lean_object* v_x_3505_){
_start:
{
if (lean_obj_tag(v_x_3505_) == 0)
{
return v_x_3504_;
}
else
{
lean_object* v_head_3506_; lean_object* v_tail_3507_; lean_object* v___x_3508_; 
v_head_3506_ = lean_ctor_get(v_x_3505_, 0);
lean_inc(v_head_3506_);
v_tail_3507_ = lean_ctor_get(v_x_3505_, 1);
lean_inc(v_tail_3507_);
lean_dec_ref_known(v_x_3505_, 2);
v___x_3508_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3503_, v_head_3506_);
if (lean_obj_tag(v___x_3508_) == 1)
{
lean_object* v_val_3509_; lean_object* v___x_3510_; 
v_val_3509_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_val_3509_);
lean_dec_ref_known(v___x_3508_, 1);
v___x_3510_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3506_, v_val_3509_, v_x_3504_);
v_x_3504_ = v___x_3510_;
v_x_3505_ = v_tail_3507_;
goto _start;
}
else
{
lean_dec(v___x_3508_);
lean_dec(v_head_3506_);
v_x_3505_ = v_tail_3507_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3513_, lean_object* v_x_3514_, lean_object* v_x_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3513_, v_x_3514_, v_x_3515_);
lean_dec(v_newState_3513_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3517_, lean_object* v_newState_3518_, lean_object* v_consts_3519_, lean_object* v_st_3520_){
_start:
{
lean_object* v___x_3521_; 
v___x_3521_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3518_, v_st_3520_, v_consts_3519_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3522_, lean_object* v_newState_3523_, lean_object* v_consts_3524_, lean_object* v_st_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3522_, v_newState_3523_, v_consts_3524_, v_st_3525_);
lean_dec(v_newState_3523_);
lean_dec(v_x_3522_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3536_){
_start:
{
lean_object* v___x_3537_; lean_object* v___y_3539_; 
v___x_3537_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3536_) == 0)
{
lean_object* v_size_3543_; 
v_size_3543_ = lean_ctor_get(v_s_3536_, 0);
lean_inc(v_size_3543_);
lean_dec_ref_known(v_s_3536_, 5);
v___y_3539_ = v_size_3543_;
goto v___jp_3538_;
}
else
{
lean_object* v___x_3544_; 
v___x_3544_ = lean_unsigned_to_nat(0u);
v___y_3539_ = v___x_3544_;
goto v___jp_3538_;
}
v___jp_3538_:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3540_ = l_Nat_reprFast(v___y_3539_);
v___x_3541_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
v___x_3542_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3537_);
lean_ctor_set(v___x_3542_, 1, v___x_3541_);
return v___x_3542_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3545_, lean_object* v_as_3546_, size_t v_i_3547_, size_t v_stop_3548_, lean_object* v_b_3549_){
_start:
{
lean_object* v___y_3551_; uint8_t v___x_3555_; 
v___x_3555_ = lean_usize_dec_eq(v_i_3547_, v_stop_3548_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; lean_object* v_fst_3557_; uint8_t v___x_3558_; lean_object* v___x_3559_; uint8_t v___x_3560_; 
v___x_3556_ = lean_array_uget_borrowed(v_as_3546_, v_i_3547_);
v_fst_3557_ = lean_ctor_get(v___x_3556_, 0);
v___x_3558_ = 1;
lean_inc_ref(v_env_3545_);
v___x_3559_ = l_Lean_Environment_setExporting(v_env_3545_, v___x_3558_);
lean_inc(v_fst_3557_);
v___x_3560_ = l_Lean_Environment_contains(v___x_3559_, v_fst_3557_, v___x_3558_);
if (v___x_3560_ == 0)
{
v___y_3551_ = v_b_3549_;
goto v___jp_3550_;
}
else
{
lean_object* v___x_3561_; 
lean_inc(v___x_3556_);
v___x_3561_ = lean_array_push(v_b_3549_, v___x_3556_);
v___y_3551_ = v___x_3561_;
goto v___jp_3550_;
}
}
else
{
lean_dec_ref(v_env_3545_);
return v_b_3549_;
}
v___jp_3550_:
{
size_t v___x_3552_; size_t v___x_3553_; 
v___x_3552_ = ((size_t)1ULL);
v___x_3553_ = lean_usize_add(v_i_3547_, v___x_3552_);
v_i_3547_ = v___x_3553_;
v_b_3549_ = v___y_3551_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_3545_ = stack[0].m_obj;
lean_object* v_as_3546_ = stack[1].m_obj;
size_t v_i_3547_ = stack[2].m_num;
size_t v_stop_3548_ = stack[3].m_num;
lean_object* v_b_3549_ = stack[4].m_obj;
lean_object* v_res_3562_;
v_res_3562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3545_, v_as_3546_, v_i_3547_, v_stop_3548_, v_b_3549_);
stack->m_obj
 = v_res_3562_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3563_, lean_object* v_as_3564_, lean_object* v_i_3565_, lean_object* v_stop_3566_, lean_object* v_b_3567_){
_start:
{
size_t v_i_boxed_3568_; size_t v_stop_boxed_3569_; lean_object* v_res_3570_; 
v_i_boxed_3568_ = lean_unbox_usize(v_i_3565_);
lean_dec(v_i_3565_);
v_stop_boxed_3569_ = lean_unbox_usize(v_stop_3566_);
lean_dec(v_stop_3566_);
v_res_3570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3563_, v_as_3564_, v_i_boxed_3568_, v_stop_boxed_3569_, v_b_3567_);
lean_dec_ref(v_as_3564_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3571_, lean_object* v_m_3572_){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___y_3576_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___y_3593_; lean_object* v___y_3594_; uint8_t v___x_3596_; 
v___x_3573_ = lean_unsigned_to_nat(0u);
v___x_3574_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_3590_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_3574_, v_m_3572_);
v___x_3591_ = lean_array_get_size(v___x_3590_);
v___x_3596_ = lean_nat_dec_eq(v___x_3591_, v___x_3573_);
if (v___x_3596_ == 0)
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___y_3600_; uint8_t v___x_3602_; 
v___x_3597_ = lean_unsigned_to_nat(1u);
v___x_3598_ = lean_nat_sub(v___x_3591_, v___x_3597_);
v___x_3602_ = lean_nat_dec_le(v___x_3573_, v___x_3598_);
if (v___x_3602_ == 0)
{
lean_inc(v___x_3598_);
v___y_3600_ = v___x_3598_;
goto v___jp_3599_;
}
else
{
v___y_3600_ = v___x_3573_;
goto v___jp_3599_;
}
v___jp_3599_:
{
uint8_t v___x_3601_; 
v___x_3601_ = lean_nat_dec_le(v___y_3600_, v___x_3598_);
if (v___x_3601_ == 0)
{
lean_dec(v___x_3598_);
lean_inc(v___y_3600_);
v___y_3593_ = v___y_3600_;
v___y_3594_ = v___y_3600_;
goto v___jp_3592_;
}
else
{
v___y_3593_ = v___y_3600_;
v___y_3594_ = v___x_3598_;
goto v___jp_3592_;
}
}
}
else
{
v___y_3576_ = v___x_3590_;
goto v___jp_3575_;
}
v___jp_3575_:
{
lean_object* v___x_3577_; uint8_t v___x_3578_; 
v___x_3577_ = lean_array_get_size(v___y_3576_);
v___x_3578_ = lean_nat_dec_lt(v___x_3573_, v___x_3577_);
if (v___x_3578_ == 0)
{
lean_object* v___x_3579_; 
lean_dec_ref(v_env_3571_);
v___x_3579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3574_);
lean_ctor_set(v___x_3579_, 1, v___x_3574_);
lean_ctor_set(v___x_3579_, 2, v___y_3576_);
return v___x_3579_;
}
else
{
uint8_t v___x_3580_; 
v___x_3580_ = lean_nat_dec_le(v___x_3577_, v___x_3577_);
if (v___x_3580_ == 0)
{
if (v___x_3578_ == 0)
{
lean_object* v___x_3581_; 
lean_dec_ref(v_env_3571_);
v___x_3581_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3574_);
lean_ctor_set(v___x_3581_, 1, v___x_3574_);
lean_ctor_set(v___x_3581_, 2, v___y_3576_);
return v___x_3581_;
}
else
{
size_t v___x_3582_; size_t v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3582_ = ((size_t)0ULL);
v___x_3583_ = lean_usize_of_nat(v___x_3577_);
v___x_3584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3571_, v___y_3576_, v___x_3582_, v___x_3583_, v___x_3574_);
lean_inc_ref(v___x_3584_);
v___x_3585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3584_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
lean_ctor_set(v___x_3585_, 2, v___y_3576_);
return v___x_3585_;
}
}
else
{
size_t v___x_3586_; size_t v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3586_ = ((size_t)0ULL);
v___x_3587_ = lean_usize_of_nat(v___x_3577_);
v___x_3588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3571_, v___y_3576_, v___x_3586_, v___x_3587_, v___x_3574_);
lean_inc_ref(v___x_3588_);
v___x_3589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
lean_ctor_set(v___x_3589_, 1, v___x_3588_);
lean_ctor_set(v___x_3589_, 2, v___y_3576_);
return v___x_3589_;
}
}
}
v___jp_3592_:
{
lean_object* v___x_3595_; 
v___x_3595_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_3591_, v___x_3590_, v___y_3593_, v___y_3594_);
lean_dec(v___y_3594_);
v___y_3576_ = v___x_3595_;
goto v___jp_3575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3603_, lean_object* v_m_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3603_, v_m_3604_);
lean_dec(v_m_3604_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3606_, lean_object* v_p_3607_){
_start:
{
lean_object* v_fst_3608_; lean_object* v_snd_3609_; lean_object* v___x_3610_; 
v_fst_3608_ = lean_ctor_get(v_p_3607_, 0);
lean_inc(v_fst_3608_);
v_snd_3609_ = lean_ctor_get(v_p_3607_, 1);
lean_inc(v_snd_3609_);
lean_dec_ref(v_p_3607_);
v___x_3610_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3608_, v_snd_3609_, v_s_3606_);
return v___x_3610_;
}
}
lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3611_, lean_object* v_x_3612_, lean_object* v_x_3613_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3611_);
return v___x_3615_;
}
}
LEAN_EXPORT void l_Lean_registerEnumAttributes___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3611_ = stack[0].m_obj;
lean_object* v_x_3612_ = stack[1].m_obj;
lean_object* v_x_3613_ = stack[2].m_obj;
lean_object* v_res_3616_;
v_res_3616_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3611_, v_x_3612_, v_x_3613_);
stack->m_obj
 = v_res_3616_;
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3617_, lean_object* v_x_3618_, lean_object* v_x_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v_res_3621_; 
v_res_3621_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3617_, v_x_3618_, v_x_3619_);
lean_dec_ref(v_x_3619_);
lean_dec_ref(v_x_3618_);
return v_res_3621_;
}
}
lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3622_){
_start:
{
if (lean_obj_tag(v_as_3622_) == 0)
{
lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3624_ = lean_box(0);
v___x_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3624_);
return v___x_3625_;
}
else
{
lean_object* v_head_3626_; lean_object* v_tail_3627_; lean_object* v___x_3628_; 
v_head_3626_ = lean_ctor_get(v_as_3622_, 0);
lean_inc(v_head_3626_);
v_tail_3627_ = lean_ctor_get(v_as_3622_, 1);
lean_inc(v_tail_3627_);
lean_dec_ref_known(v_as_3622_, 2);
v___x_3628_ = l_Lean_registerBuiltinAttribute(v_head_3626_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_dec_ref_known(v___x_3628_, 1);
v_as_3622_ = v_tail_3627_;
goto _start;
}
else
{
lean_dec(v_tail_3627_);
return v___x_3628_;
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00Lean_registerEnumAttributes_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3622_ = stack[0].m_obj;
lean_object* v_res_3630_;
v_res_3630_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3622_);
stack->m_obj
 = v_res_3630_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3631_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_addEntryFn_3634_, lean_object* v___x_3635_, lean_object* v_s_3636_){
_start:
{
lean_object* v_importedEntries_3637_; lean_object* v_state_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3646_; 
v_importedEntries_3637_ = lean_ctor_get(v_s_3636_, 0);
v_state_3638_ = lean_ctor_get(v_s_3636_, 1);
v_isSharedCheck_3646_ = !lean_is_exclusive(v_s_3636_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3640_ = v_s_3636_;
v_isShared_3641_ = v_isSharedCheck_3646_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_state_3638_);
lean_inc(v_importedEntries_3637_);
lean_dec(v_s_3636_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3646_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v_state_3642_; lean_object* v___x_3644_; 
v_state_3642_ = lean_apply_2(v_addEntryFn_3634_, v_state_3638_, v___x_3635_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 1, v_state_3642_);
v___x_3644_ = v___x_3640_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_importedEntries_3637_);
lean_ctor_set(v_reuseFailAlloc_3645_, 1, v_state_3642_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2(lean_object* v_validate_3647_, lean_object* v_snd_3648_, lean_object* v_a_3649_, lean_object* v_fst_3650_, lean_object* v_decl_3651_, lean_object* v_stx_3652_, uint8_t v_kind_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v_nextMacroScope_3660_; lean_object* v_ngen_3661_; lean_object* v_auxDeclNGen_3662_; lean_object* v_traceState_3663_; lean_object* v_recordedDeps_3664_; lean_object* v_messages_3665_; lean_object* v_infoState_3666_; lean_object* v_snapshotTasks_3667_; lean_object* v___y_3668_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___x_3703_; 
v___x_3703_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3652_, v___y_3654_, v___y_3655_);
if (lean_obj_tag(v___x_3703_) == 0)
{
uint8_t v___x_3704_; uint8_t v___x_3705_; 
lean_dec_ref_known(v___x_3703_, 1);
v___x_3704_ = 0;
v___x_3705_ = l_Lean_instBEqAttributeKind_beq(v_kind_3653_, v___x_3704_);
if (v___x_3705_ == 0)
{
lean_object* v___x_3706_; 
lean_dec(v_decl_3651_);
lean_dec_ref(v_a_3649_);
lean_dec(v_snd_3648_);
lean_dec_ref(v_validate_3647_);
v___x_3706_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3650_, v_kind_3653_, v___y_3654_, v___y_3655_);
return v___x_3706_;
}
else
{
goto v___jp_3698_;
}
}
else
{
lean_dec(v_decl_3651_);
lean_dec(v_fst_3650_);
lean_dec_ref(v_a_3649_);
lean_dec(v_snd_3648_);
lean_dec_ref(v_validate_3647_);
return v___x_3703_;
}
v___jp_3657_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3669_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_3670_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3670_, 0, v___y_3668_);
lean_ctor_set(v___x_3670_, 1, v_nextMacroScope_3660_);
lean_ctor_set(v___x_3670_, 2, v_ngen_3661_);
lean_ctor_set(v___x_3670_, 3, v_auxDeclNGen_3662_);
lean_ctor_set(v___x_3670_, 4, v_traceState_3663_);
lean_ctor_set(v___x_3670_, 5, v___x_3669_);
lean_ctor_set(v___x_3670_, 6, v_recordedDeps_3664_);
lean_ctor_set(v___x_3670_, 7, v_messages_3665_);
lean_ctor_set(v___x_3670_, 8, v_infoState_3666_);
lean_ctor_set(v___x_3670_, 9, v_snapshotTasks_3667_);
v___x_3671_ = lean_st_ref_put(v___y_3658_, v___x_3670_);
v___x_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3672_, 0, v___y_3659_);
return v___x_3672_;
}
v___jp_3673_:
{
lean_object* v___x_3676_; 
lean_inc(v___y_3675_);
lean_inc_ref(v___y_3674_);
lean_inc(v_snd_3648_);
lean_inc(v_decl_3651_);
v___x_3676_ = lean_apply_5(v_validate_3647_, v_decl_3651_, v_snd_3648_, v___y_3674_, v___y_3675_, lean_box(0));
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v___x_3677_; lean_object* v_toEnvExtension_3678_; lean_object* v_env_3679_; lean_object* v_nextMacroScope_3680_; lean_object* v_ngen_3681_; lean_object* v_auxDeclNGen_3682_; lean_object* v_traceState_3683_; lean_object* v_recordedDeps_3684_; lean_object* v_messages_3685_; lean_object* v_infoState_3686_; lean_object* v_snapshotTasks_3687_; lean_object* v_addEntryFn_3688_; lean_object* v_asyncMode_3689_; uint8_t v_logWrites_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___f_3693_; uint8_t v___x_3694_; 
lean_dec_ref_known(v___x_3676_, 1);
v___x_3677_ = lean_st_ref_take(v___y_3675_);
v_toEnvExtension_3678_ = lean_ctor_get(v_a_3649_, 0);
lean_inc_ref(v_toEnvExtension_3678_);
v_env_3679_ = lean_ctor_get(v___x_3677_, 0);
lean_inc_ref(v_env_3679_);
v_nextMacroScope_3680_ = lean_ctor_get(v___x_3677_, 1);
lean_inc(v_nextMacroScope_3680_);
v_ngen_3681_ = lean_ctor_get(v___x_3677_, 2);
lean_inc_ref(v_ngen_3681_);
v_auxDeclNGen_3682_ = lean_ctor_get(v___x_3677_, 3);
lean_inc_ref(v_auxDeclNGen_3682_);
v_traceState_3683_ = lean_ctor_get(v___x_3677_, 4);
lean_inc_ref(v_traceState_3683_);
v_recordedDeps_3684_ = lean_ctor_get(v___x_3677_, 6);
lean_inc_ref(v_recordedDeps_3684_);
v_messages_3685_ = lean_ctor_get(v___x_3677_, 7);
lean_inc_ref(v_messages_3685_);
v_infoState_3686_ = lean_ctor_get(v___x_3677_, 8);
lean_inc_ref(v_infoState_3686_);
v_snapshotTasks_3687_ = lean_ctor_get(v___x_3677_, 9);
lean_inc_ref(v_snapshotTasks_3687_);
lean_dec(v___x_3677_);
v_addEntryFn_3688_ = lean_ctor_get(v_a_3649_, 3);
lean_inc(v_addEntryFn_3688_);
lean_dec_ref(v_a_3649_);
v_asyncMode_3689_ = lean_ctor_get(v_toEnvExtension_3678_, 2);
lean_inc(v_asyncMode_3689_);
v_logWrites_3690_ = lean_ctor_get_uint8(v_toEnvExtension_3678_, sizeof(void*)*6);
v___x_3691_ = lean_box(0);
lean_inc(v_decl_3651_);
v___x_3692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3692_, 0, v_decl_3651_);
lean_ctor_set(v___x_3692_, 1, v_snd_3648_);
v___f_3693_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3693_, 0, v_addEntryFn_3688_);
lean_closure_set(v___f_3693_, 1, v___x_3692_);
v___x_3694_ = 1;
if (v_logWrites_3690_ == 0)
{
lean_object* v___x_3695_; 
v___x_3695_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3678_, v_env_3679_, v___f_3693_, v_asyncMode_3689_, v_decl_3651_, v___x_3694_);
lean_dec(v_asyncMode_3689_);
v___y_3658_ = v___y_3675_;
v___y_3659_ = v___x_3691_;
v_nextMacroScope_3660_ = v_nextMacroScope_3680_;
v_ngen_3661_ = v_ngen_3681_;
v_auxDeclNGen_3662_ = v_auxDeclNGen_3682_;
v_traceState_3663_ = v_traceState_3683_;
v_recordedDeps_3664_ = v_recordedDeps_3684_;
v_messages_3665_ = v_messages_3685_;
v_infoState_3666_ = v_infoState_3686_;
v_snapshotTasks_3667_ = v_snapshotTasks_3687_;
v___y_3668_ = v___x_3695_;
goto v___jp_3657_;
}
else
{
lean_object* v___x_3696_; lean_object* v___x_3697_; 
lean_inc_ref(v_toEnvExtension_3678_);
v___x_3696_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3678_, v_env_3679_);
lean_dec_ref(v_env_3679_);
v___x_3697_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3678_, v___x_3696_, v___f_3693_, v_asyncMode_3689_, v_decl_3651_, v___x_3694_);
lean_dec(v_asyncMode_3689_);
v___y_3658_ = v___y_3675_;
v___y_3659_ = v___x_3691_;
v_nextMacroScope_3660_ = v_nextMacroScope_3680_;
v_ngen_3661_ = v_ngen_3681_;
v_auxDeclNGen_3662_ = v_auxDeclNGen_3682_;
v_traceState_3663_ = v_traceState_3683_;
v_recordedDeps_3664_ = v_recordedDeps_3684_;
v_messages_3665_ = v_messages_3685_;
v_infoState_3666_ = v_infoState_3686_;
v_snapshotTasks_3667_ = v_snapshotTasks_3687_;
v___y_3668_ = v___x_3697_;
goto v___jp_3657_;
}
}
else
{
lean_dec(v_decl_3651_);
lean_dec_ref(v_a_3649_);
lean_dec(v_snd_3648_);
return v___x_3676_;
}
}
v___jp_3698_:
{
lean_object* v___x_3699_; lean_object* v_env_3700_; lean_object* v___x_3701_; 
v___x_3699_ = lean_st_ref_get(v___y_3655_);
v_env_3700_ = lean_ctor_get(v___x_3699_, 0);
lean_inc_ref(v_env_3700_);
lean_dec(v___x_3699_);
v___x_3701_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3700_, v_decl_3651_);
lean_dec_ref(v_env_3700_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_dec(v_fst_3650_);
v___y_3674_ = v___y_3654_;
v___y_3675_ = v___y_3655_;
goto v___jp_3673_;
}
else
{
lean_object* v___x_3702_; 
lean_dec_ref_known(v___x_3701_, 1);
lean_dec_ref(v_a_3649_);
lean_dec(v_snd_3648_);
lean_dec_ref(v_validate_3647_);
v___x_3702_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3650_, v_decl_3651_, v___y_3654_, v___y_3655_);
return v___x_3702_;
}
}
}
}
LEAN_EXPORT void l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_validate_3647_ = stack[0].m_obj;
lean_object* v_snd_3648_ = stack[1].m_obj;
lean_object* v_a_3649_ = stack[2].m_obj;
lean_object* v_fst_3650_ = stack[3].m_obj;
lean_object* v_decl_3651_ = stack[4].m_obj;
lean_object* v_stx_3652_ = stack[5].m_obj;
uint8_t v_kind_3653_ = stack[6].m_num;
lean_object* v___y_3654_ = stack[7].m_obj;
lean_object* v___y_3655_ = stack[8].m_obj;
lean_object* v_res_3707_;
v_res_3707_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2(v_validate_3647_, v_snd_3648_, v_a_3649_, v_fst_3650_, v_decl_3651_, v_stx_3652_, v_kind_3653_, v___y_3654_, v___y_3655_);
stack->m_obj
 = v_res_3707_;
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2___boxed(lean_object* v_validate_3708_, lean_object* v_snd_3709_, lean_object* v_a_3710_, lean_object* v_fst_3711_, lean_object* v_decl_3712_, lean_object* v_stx_3713_, lean_object* v_kind_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
uint8_t v_kind_boxed_3718_; lean_object* v_res_3719_; 
v_kind_boxed_3718_ = lean_unbox(v_kind_3714_);
v_res_3719_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2(v_validate_3708_, v_snd_3709_, v_a_3710_, v_fst_3711_, v_decl_3712_, v_stx_3713_, v_kind_boxed_3718_, v___y_3715_, v___y_3716_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
return v_res_3719_;
}
}
lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3720_, lean_object* v_decl_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3725_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3726_ = l_Lean_MessageData_ofName(v_fst_3720_);
v___x_3727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3725_);
lean_ctor_set(v___x_3727_, 1, v___x_3726_);
v___x_3728_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3729_, v___y_3722_, v___y_3723_);
return v___x_3730_;
}
}
LEAN_EXPORT void l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_3720_ = stack[0].m_obj;
lean_object* v_decl_3721_ = stack[1].m_obj;
lean_object* v___y_3722_ = stack[2].m_obj;
lean_object* v___y_3723_ = stack[3].m_obj;
lean_object* v_res_3731_;
v_res_3731_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3720_, v_decl_3721_, v___y_3722_, v___y_3723_);
stack->m_obj
 = v_res_3731_;
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3732_, lean_object* v_decl_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3732_, v_decl_3733_, v___y_3734_, v___y_3735_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v_decl_3733_);
return v_res_3737_;
}
}
lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3738_, lean_object* v_a_3739_, lean_object* v_ref_3740_, uint8_t v_applicationTime_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_){
_start:
{
if (lean_obj_tag(v_a_3742_) == 0)
{
lean_object* v___x_3744_; 
lean_dec(v_ref_3740_);
lean_dec_ref(v_a_3739_);
lean_dec_ref(v_validate_3738_);
v___x_3744_ = l_List_reverse___redArg(v_a_3743_);
return v___x_3744_;
}
else
{
lean_object* v_head_3745_; lean_object* v_snd_3746_; lean_object* v_tail_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3762_; 
v_head_3745_ = lean_ctor_get(v_a_3742_, 0);
lean_inc(v_head_3745_);
v_snd_3746_ = lean_ctor_get(v_head_3745_, 1);
lean_inc(v_snd_3746_);
v_tail_3747_ = lean_ctor_get(v_a_3742_, 1);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_a_3742_);
if (v_isSharedCheck_3762_ == 0)
{
lean_object* v_unused_3763_; 
v_unused_3763_ = lean_ctor_get(v_a_3742_, 0);
lean_dec(v_unused_3763_);
v___x_3749_ = v_a_3742_;
v_isShared_3750_ = v_isSharedCheck_3762_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_tail_3747_);
lean_dec(v_a_3742_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3762_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v_fst_3751_; lean_object* v_fst_3752_; lean_object* v_snd_3753_; lean_object* v___f_3754_; lean_object* v___f_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3759_; 
v_fst_3751_ = lean_ctor_get(v_head_3745_, 0);
lean_inc_n(v_fst_3751_, 3);
lean_dec(v_head_3745_);
v_fst_3752_ = lean_ctor_get(v_snd_3746_, 0);
lean_inc(v_fst_3752_);
v_snd_3753_ = lean_ctor_get(v_snd_3746_, 1);
lean_inc(v_snd_3753_);
lean_dec(v_snd_3746_);
v___f_3754_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3754_, 0, v_fst_3751_);
lean_inc_ref(v_a_3739_);
lean_inc_ref(v_validate_3738_);
v___f_3755_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2___boxed), 10, 4);
lean_closure_set(v___f_3755_, 0, v_validate_3738_);
lean_closure_set(v___f_3755_, 1, v_snd_3753_);
lean_closure_set(v___f_3755_, 2, v_a_3739_);
lean_closure_set(v___f_3755_, 3, v_fst_3751_);
lean_inc(v_ref_3740_);
v___x_3756_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3756_, 0, v_ref_3740_);
lean_ctor_set(v___x_3756_, 1, v_fst_3751_);
lean_ctor_set(v___x_3756_, 2, v_fst_3752_);
lean_ctor_set_uint8(v___x_3756_, sizeof(void*)*3, v_applicationTime_3741_);
v___x_3757_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3756_);
lean_ctor_set(v___x_3757_, 1, v___f_3755_);
lean_ctor_set(v___x_3757_, 2, v___f_3754_);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 1, v_a_3743_);
lean_ctor_set(v___x_3749_, 0, v___x_3757_);
v___x_3759_ = v___x_3749_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3757_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_a_3743_);
v___x_3759_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
v_a_3742_ = v_tail_3747_;
v_a_3743_ = v___x_3759_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_validate_3738_ = stack[0].m_obj;
lean_object* v_a_3739_ = stack[1].m_obj;
lean_object* v_ref_3740_ = stack[2].m_obj;
uint8_t v_applicationTime_3741_ = stack[3].m_num;
lean_object* v_a_3742_ = stack[4].m_obj;
lean_object* v_a_3743_ = stack[5].m_obj;
lean_object* v_res_3764_;
v_res_3764_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3738_, v_a_3739_, v_ref_3740_, v_applicationTime_3741_, v_a_3742_, v_a_3743_);
stack->m_obj
 = v_res_3764_;
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3765_, lean_object* v_a_3766_, lean_object* v_ref_3767_, lean_object* v_applicationTime_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_){
_start:
{
uint8_t v_applicationTime_boxed_3771_; lean_object* v_res_3772_; 
v_applicationTime_boxed_3771_ = lean_unbox(v_applicationTime_3768_);
v_res_3772_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3765_, v_a_3766_, v_ref_3767_, v_applicationTime_boxed_3771_, v_a_3769_, v_a_3770_);
return v_res_3772_;
}
}
lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3786_, lean_object* v_validate_3787_, uint8_t v_applicationTime_3788_, lean_object* v_ref_3789_){
_start:
{
lean_object* v___f_3791_; lean_object* v___f_3792_; lean_object* v___f_3793_; lean_object* v___f_3794_; lean_object* v___f_3795_; lean_object* v___f_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; uint8_t v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___f_3791_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3792_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3793_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3794_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3795_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3796_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3797_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3798_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
v___x_3799_ = 0;
lean_inc(v_ref_3789_);
v___x_3800_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_3800_, 0, v_ref_3789_);
lean_ctor_set(v___x_3800_, 1, v___f_3795_);
lean_ctor_set(v___x_3800_, 2, v___f_3796_);
lean_ctor_set(v___x_3800_, 3, v___f_3794_);
lean_ctor_set(v___x_3800_, 4, v___f_3793_);
lean_ctor_set(v___x_3800_, 5, v___f_3792_);
lean_ctor_set(v___x_3800_, 6, v___x_3797_);
lean_ctor_set(v___x_3800_, 7, v___x_3798_);
lean_ctor_set_uint8(v___x_3800_, sizeof(void*)*8, v___x_3799_);
lean_ctor_set_uint8(v___x_3800_, sizeof(void*)*8 + 1, v___x_3799_);
v___x_3801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3800_);
lean_ctor_set(v___x_3801_, 1, v___f_3791_);
v___x_3802_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3801_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
lean_inc_n(v_a_3803_, 2);
lean_dec_ref_known(v___x_3802_, 1);
v___x_3804_ = lean_box(0);
v___x_3805_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3787_, v_a_3803_, v_ref_3789_, v_applicationTime_3788_, v_attrDescrs_3786_, v___x_3804_);
lean_inc(v___x_3805_);
v___x_3806_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3805_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3814_; 
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3814_ == 0)
{
lean_object* v_unused_3815_; 
v_unused_3815_ = lean_ctor_get(v___x_3806_, 0);
lean_dec(v_unused_3815_);
v___x_3808_ = v___x_3806_;
v_isShared_3809_ = v_isSharedCheck_3814_;
goto v_resetjp_3807_;
}
else
{
lean_dec(v___x_3806_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3814_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3810_; lean_object* v___x_3812_; 
v___x_3810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3805_);
lean_ctor_set(v___x_3810_, 1, v_a_3803_);
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 0, v___x_3810_);
v___x_3812_ = v___x_3808_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3810_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
lean_dec(v___x_3805_);
lean_dec(v_a_3803_);
v_a_3816_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3806_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3806_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_dec(v_ref_3789_);
lean_dec_ref(v_validate_3787_);
lean_dec(v_attrDescrs_3786_);
v_a_3824_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3802_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3802_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_registerEnumAttributes___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrDescrs_3786_ = stack[0].m_obj;
lean_object* v_validate_3787_ = stack[1].m_obj;
uint8_t v_applicationTime_3788_ = stack[2].m_num;
lean_object* v_ref_3789_ = stack[3].m_obj;
lean_object* v_res_3832_;
v_res_3832_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3786_, v_validate_3787_, v_applicationTime_3788_, v_ref_3789_);
stack->m_obj
 = v_res_3832_;
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3833_, lean_object* v_validate_3834_, lean_object* v_applicationTime_3835_, lean_object* v_ref_3836_, lean_object* v_a_3837_){
_start:
{
uint8_t v_applicationTime_boxed_3838_; lean_object* v_res_3839_; 
v_applicationTime_boxed_3838_ = lean_unbox(v_applicationTime_3835_);
v_res_3839_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3833_, v_validate_3834_, v_applicationTime_boxed_3838_, v_ref_3836_);
return v_res_3839_;
}
}
lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3840_, lean_object* v_attrDescrs_3841_, lean_object* v_validate_3842_, uint8_t v_applicationTime_3843_, lean_object* v_ref_3844_){
_start:
{
lean_object* v___x_3846_; 
v___x_3846_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3841_, v_validate_3842_, v_applicationTime_3843_, v_ref_3844_);
return v___x_3846_;
}
}
LEAN_EXPORT void l_Lean_registerEnumAttributes_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrDescrs_3841_ = stack[1].m_obj;
lean_object* v_validate_3842_ = stack[2].m_obj;
uint8_t v_applicationTime_3843_ = stack[3].m_num;
lean_object* v_ref_3844_ = stack[4].m_obj;
lean_object* v_res_3847_;
v_res_3847_ = l_Lean_registerEnumAttributes(lean_box(0), v_attrDescrs_3841_, v_validate_3842_, v_applicationTime_3843_, v_ref_3844_);
stack->m_obj
 = v_res_3847_;
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3848_, lean_object* v_attrDescrs_3849_, lean_object* v_validate_3850_, lean_object* v_applicationTime_3851_, lean_object* v_ref_3852_, lean_object* v_a_3853_){
_start:
{
uint8_t v_applicationTime_boxed_3854_; lean_object* v_res_3855_; 
v_applicationTime_boxed_3854_ = lean_unbox(v_applicationTime_3851_);
v_res_3855_ = l_Lean_registerEnumAttributes(v_00_u03b1_3848_, v_attrDescrs_3849_, v_validate_3850_, v_applicationTime_boxed_3854_, v_ref_3852_);
return v_res_3855_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3856_, lean_object* v_env_3857_, lean_object* v_as_3858_, size_t v_i_3859_, size_t v_stop_3860_, lean_object* v_b_3861_){
_start:
{
lean_object* v___x_3862_; 
v___x_3862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3857_, v_as_3858_, v_i_3859_, v_stop_3860_, v_b_3861_);
return v___x_3862_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_3857_ = stack[1].m_obj;
lean_object* v_as_3858_ = stack[2].m_obj;
size_t v_i_3859_ = stack[3].m_num;
size_t v_stop_3860_ = stack[4].m_num;
lean_object* v_b_3861_ = stack[5].m_obj;
lean_object* v_res_3863_;
v_res_3863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_box(0), v_env_3857_, v_as_3858_, v_i_3859_, v_stop_3860_, v_b_3861_);
stack->m_obj
 = v_res_3863_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3864_, lean_object* v_env_3865_, lean_object* v_as_3866_, lean_object* v_i_3867_, lean_object* v_stop_3868_, lean_object* v_b_3869_){
_start:
{
size_t v_i_boxed_3870_; size_t v_stop_boxed_3871_; lean_object* v_res_3872_; 
v_i_boxed_3870_ = lean_unbox_usize(v_i_3867_);
lean_dec(v_i_3867_);
v_stop_boxed_3871_ = lean_unbox_usize(v_stop_3868_);
lean_dec(v_stop_3868_);
v_res_3872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3864_, v_env_3865_, v_as_3866_, v_i_boxed_3870_, v_stop_boxed_3871_, v_b_3869_);
lean_dec_ref(v_as_3866_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3873_, lean_object* v_newState_3874_, lean_object* v_x_3875_, lean_object* v_x_3876_){
_start:
{
lean_object* v___x_3877_; 
v___x_3877_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3874_, v_x_3875_, v_x_3876_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3878_, lean_object* v_newState_3879_, lean_object* v_x_3880_, lean_object* v_x_3881_){
_start:
{
lean_object* v_res_3882_; 
v_res_3882_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3878_, v_newState_3879_, v_x_3880_, v_x_3881_);
lean_dec(v_newState_3879_);
return v_res_3882_;
}
}
lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3883_, lean_object* v_validate_3884_, lean_object* v_a_3885_, lean_object* v_ref_3886_, uint8_t v_applicationTime_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v___x_3890_; 
v___x_3890_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3884_, v_a_3885_, v_ref_3886_, v_applicationTime_3887_, v_a_3888_, v_a_3889_);
return v___x_3890_;
}
}
LEAN_EXPORT void l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_validate_3884_ = stack[1].m_obj;
lean_object* v_a_3885_ = stack[2].m_obj;
lean_object* v_ref_3886_ = stack[3].m_obj;
uint8_t v_applicationTime_3887_ = stack[4].m_num;
lean_object* v_a_3888_ = stack[5].m_obj;
lean_object* v_a_3889_ = stack[6].m_obj;
lean_object* v_res_3891_;
v_res_3891_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_box(0), v_validate_3884_, v_a_3885_, v_ref_3886_, v_applicationTime_3887_, v_a_3888_, v_a_3889_);
stack->m_obj
 = v_res_3891_;
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3892_, lean_object* v_validate_3893_, lean_object* v_a_3894_, lean_object* v_ref_3895_, lean_object* v_applicationTime_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_){
_start:
{
uint8_t v_applicationTime_boxed_3899_; lean_object* v_res_3900_; 
v_applicationTime_boxed_3899_ = lean_unbox(v_applicationTime_3896_);
v_res_3900_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3892_, v_validate_3893_, v_a_3894_, v_ref_3895_, v_applicationTime_boxed_3899_, v_a_3897_, v_a_3898_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3901_, lean_object* v_attr_3902_, lean_object* v_env_3903_, lean_object* v_decl_3904_){
_start:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3905_ = lean_box(1);
v___x_3906_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3903_, v_decl_3904_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v_ext_3907_; lean_object* v_toEnvExtension_3908_; lean_object* v_asyncMode_3909_; uint8_t v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
lean_dec(v_inst_3901_);
v_ext_3907_ = lean_ctor_get(v_attr_3902_, 1);
lean_inc_ref(v_ext_3907_);
lean_dec_ref(v_attr_3902_);
v_toEnvExtension_3908_ = lean_ctor_get(v_ext_3907_, 0);
v_asyncMode_3909_ = lean_ctor_get(v_toEnvExtension_3908_, 2);
lean_inc(v_asyncMode_3909_);
v___x_3910_ = 0;
lean_inc(v_decl_3904_);
v___x_3911_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3905_, v_ext_3907_, v_env_3903_, v_asyncMode_3909_, v_decl_3904_, v___x_3910_);
lean_dec(v_asyncMode_3909_);
lean_dec_ref(v_ext_3907_);
v___x_3912_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3911_, v_decl_3904_);
lean_dec(v_decl_3904_);
lean_dec(v___x_3911_);
return v___x_3912_;
}
else
{
lean_object* v_val_3913_; lean_object* v_ext_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3944_; 
v_val_3913_ = lean_ctor_get(v___x_3906_, 0);
lean_inc(v_val_3913_);
lean_dec_ref_known(v___x_3906_, 1);
v_ext_3914_ = lean_ctor_get(v_attr_3902_, 1);
v_isSharedCheck_3944_ = !lean_is_exclusive(v_attr_3902_);
if (v_isSharedCheck_3944_ == 0)
{
lean_object* v_unused_3945_; 
v_unused_3945_ = lean_ctor_get(v_attr_3902_, 0);
lean_dec(v_unused_3945_);
v___x_3916_ = v_attr_3902_;
v_isShared_3917_ = v_isSharedCheck_3944_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_ext_3914_);
lean_dec(v_attr_3902_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3944_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
uint8_t v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; uint8_t v___x_3922_; 
v___x_3918_ = 0;
v___x_3919_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3905_, v_ext_3914_, v_env_3903_, v_val_3913_, v___x_3918_);
lean_dec(v_val_3913_);
lean_dec_ref(v_env_3903_);
lean_dec_ref(v_ext_3914_);
v___x_3920_ = lean_unsigned_to_nat(0u);
v___x_3921_ = lean_array_get_size(v___x_3919_);
v___x_3922_ = lean_nat_dec_lt(v___x_3920_, v___x_3921_);
if (v___x_3922_ == 0)
{
lean_object* v___x_3923_; 
lean_dec_ref(v___x_3919_);
lean_del_object(v___x_3916_);
lean_dec(v_decl_3904_);
lean_dec(v_inst_3901_);
v___x_3923_ = lean_box(0);
return v___x_3923_;
}
else
{
lean_object* v___x_3924_; lean_object* v___x_3925_; uint8_t v___x_3926_; 
v___x_3924_ = lean_unsigned_to_nat(1u);
v___x_3925_ = lean_nat_sub(v___x_3921_, v___x_3924_);
v___x_3926_ = lean_nat_dec_le(v___x_3920_, v___x_3925_);
if (v___x_3926_ == 0)
{
lean_object* v___x_3927_; 
lean_dec(v___x_3925_);
lean_dec_ref(v___x_3919_);
lean_del_object(v___x_3916_);
lean_dec(v_decl_3904_);
lean_dec(v_inst_3901_);
v___x_3927_ = lean_box(0);
return v___x_3927_;
}
else
{
lean_object* v___f_3928_; lean_object* v___x_3930_; 
v___f_3928_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 1, v_inst_3901_);
lean_ctor_set(v___x_3916_, 0, v_decl_3904_);
v___x_3930_ = v___x_3916_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_decl_3904_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v_inst_3901_);
v___x_3930_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; 
v___x_3931_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3932_ = l_Array_binSearchAux___redArg(v___f_3928_, v___x_3931_, v___x_3919_, v___x_3930_, v___x_3920_, v___x_3925_);
lean_dec_ref(v___x_3919_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_object* v___x_3933_; 
v___x_3933_ = lean_box(0);
return v___x_3933_;
}
else
{
lean_object* v_val_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3942_; 
v_val_3934_ = lean_ctor_get(v___x_3932_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3936_ = v___x_3932_;
v_isShared_3937_ = v_isSharedCheck_3942_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_val_3934_);
lean_dec(v___x_3932_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3942_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v_snd_3938_; lean_object* v___x_3940_; 
v_snd_3938_ = lean_ctor_get(v_val_3934_, 1);
lean_inc(v_snd_3938_);
lean_dec(v_val_3934_);
if (v_isShared_3937_ == 0)
{
lean_ctor_set(v___x_3936_, 0, v_snd_3938_);
v___x_3940_ = v___x_3936_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_snd_3938_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3946_, lean_object* v_inst_3947_, lean_object* v_attr_3948_, lean_object* v_env_3949_, lean_object* v_decl_3950_){
_start:
{
lean_object* v___x_3951_; 
v___x_3951_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3947_, v_attr_3948_, v_env_3949_, v_decl_3950_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3960_, lean_object* v_env_3961_, lean_object* v_decl_3962_, lean_object* v_val_3963_){
_start:
{
lean_object* v_ext_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_4034_; 
v_ext_3964_ = lean_ctor_get(v_attrs_3960_, 1);
v_isSharedCheck_4034_ = !lean_is_exclusive(v_attrs_3960_);
if (v_isSharedCheck_4034_ == 0)
{
lean_object* v_unused_4035_; 
v_unused_4035_ = lean_ctor_get(v_attrs_3960_, 0);
lean_dec(v_unused_4035_);
v___x_3966_ = v_attrs_3960_;
v_isShared_3967_ = v_isSharedCheck_4034_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_ext_3964_);
lean_dec(v_attrs_3960_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_4034_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v_toEnvExtension_3968_; lean_object* v_name_3969_; lean_object* v_addEntryFn_3970_; lean_object* v___x_3971_; uint8_t v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v_pfx_3980_; lean_object* v___x_3981_; 
v_toEnvExtension_3968_ = lean_ctor_get(v_ext_3964_, 0);
lean_inc_ref(v_toEnvExtension_3968_);
v_name_3969_ = lean_ctor_get(v_ext_3964_, 1);
v_addEntryFn_3970_ = lean_ctor_get(v_ext_3964_, 3);
lean_inc(v_addEntryFn_3970_);
v___x_3971_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3972_ = 1;
lean_inc(v_name_3969_);
v___x_3973_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3969_, v___x_3972_);
v___x_3974_ = lean_string_append(v___x_3971_, v___x_3973_);
lean_dec_ref(v___x_3973_);
v___x_3975_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3976_ = lean_string_append(v___x_3974_, v___x_3975_);
lean_inc(v_decl_3962_);
v___x_3977_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3962_, v___x_3972_);
v___x_3978_ = lean_string_append(v___x_3976_, v___x_3977_);
lean_dec_ref(v___x_3977_);
v___x_3979_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3980_ = lean_string_append(v___x_3978_, v___x_3979_);
v___x_3981_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3961_, v_decl_3962_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_asyncMode_3982_; uint8_t v_logWrites_3983_; uint8_t v___x_3984_; 
v_asyncMode_3982_ = lean_ctor_get(v_toEnvExtension_3968_, 2);
lean_inc(v_asyncMode_3982_);
v_logWrites_3983_ = lean_ctor_get_uint8(v_toEnvExtension_3968_, sizeof(void*)*6);
lean_inc(v_decl_3962_);
lean_inc_ref(v_env_3961_);
v___x_3984_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3961_, v_decl_3962_, v_asyncMode_3982_);
if (v___x_3984_ == 0)
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___y_3988_; lean_object* v___x_3992_; 
lean_dec(v_asyncMode_3982_);
lean_dec(v_addEntryFn_3970_);
lean_dec_ref(v_toEnvExtension_3968_);
lean_del_object(v___x_3966_);
lean_dec_ref(v_ext_3964_);
lean_dec(v_val_3963_);
lean_dec(v_decl_3962_);
v___x_3985_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3986_ = lean_string_append(v_pfx_3980_, v___x_3985_);
v___x_3992_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3961_);
if (lean_obj_tag(v___x_3992_) == 0)
{
lean_object* v___x_3993_; 
v___x_3993_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3988_ = v___x_3993_;
goto v___jp_3987_;
}
else
{
lean_object* v_val_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v_val_3994_ = lean_ctor_get(v___x_3992_, 0);
lean_inc(v_val_3994_);
lean_dec_ref_known(v___x_3992_, 1);
v___x_3995_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3996_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3994_, v___x_3972_);
v___x_3997_ = l_addParenHeuristic(v___x_3996_);
v___x_3998_ = lean_string_append(v___x_3995_, v___x_3997_);
lean_dec_ref(v___x_3997_);
v___x_3999_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_4000_ = lean_string_append(v___x_3998_, v___x_3999_);
v___y_3988_ = v___x_4000_;
goto v___jp_3987_;
}
v___jp_3987_:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3989_ = lean_string_append(v___x_3986_, v___y_3988_);
lean_dec_ref(v___y_3988_);
v___x_3990_ = lean_string_append(v___x_3989_, v___x_3979_);
v___x_3991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
return v___x_3991_;
}
}
else
{
lean_object* v___x_4001_; uint8_t v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4001_ = lean_box(1);
v___x_4002_ = 0;
lean_inc(v_decl_3962_);
lean_inc_ref(v_env_3961_);
v___x_4003_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4001_, v_ext_3964_, v_env_3961_, v_asyncMode_3982_, v_decl_3962_, v___x_4002_);
lean_dec_ref(v_ext_3964_);
v___x_4004_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4003_, v_decl_3962_);
lean_dec(v___x_4003_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v___x_4006_; 
lean_dec_ref(v_pfx_3980_);
lean_inc(v_decl_3962_);
if (v_isShared_3967_ == 0)
{
lean_ctor_set(v___x_3966_, 1, v_val_3963_);
lean_ctor_set(v___x_3966_, 0, v_decl_3962_);
v___x_4006_ = v___x_3966_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_decl_3962_);
lean_ctor_set(v_reuseFailAlloc_4013_, 1, v_val_3963_);
v___x_4006_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
lean_object* v___f_4007_; 
v___f_4007_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4007_, 0, v_addEntryFn_3970_);
lean_closure_set(v___f_4007_, 1, v___x_4006_);
if (v_logWrites_3983_ == 0)
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3968_, v_env_3961_, v___f_4007_, v_asyncMode_3982_, v_decl_3962_, v___x_3984_);
lean_dec(v_asyncMode_3982_);
v___x_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4008_);
return v___x_4009_;
}
else
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
lean_inc_ref(v_toEnvExtension_3968_);
v___x_4010_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3968_, v_env_3961_);
lean_dec_ref(v_env_3961_);
v___x_4011_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3968_, v___x_4010_, v___f_4007_, v_asyncMode_3982_, v_decl_3962_, v___x_3984_);
lean_dec(v_asyncMode_3982_);
v___x_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4011_);
return v___x_4012_;
}
}
}
else
{
lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4022_; 
lean_dec(v_asyncMode_3982_);
lean_dec(v_addEntryFn_3970_);
lean_dec_ref(v_toEnvExtension_3968_);
lean_del_object(v___x_3966_);
lean_dec(v_val_3963_);
lean_dec(v_decl_3962_);
lean_dec_ref(v_env_3961_);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4022_ == 0)
{
lean_object* v_unused_4023_; 
v_unused_4023_ = lean_ctor_get(v___x_4004_, 0);
lean_dec(v_unused_4023_);
v___x_4015_ = v___x_4004_;
v_isShared_4016_ = v_isSharedCheck_4022_;
goto v_resetjp_4014_;
}
else
{
lean_dec(v___x_4004_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4022_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4020_; 
v___x_4017_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_4018_ = lean_string_append(v_pfx_3980_, v___x_4017_);
if (v_isShared_4016_ == 0)
{
lean_ctor_set_tag(v___x_4015_, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4018_);
v___x_4020_ = v___x_4015_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v___x_4018_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
}
else
{
lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4032_; 
lean_dec(v_addEntryFn_3970_);
lean_dec_ref(v_toEnvExtension_3968_);
lean_del_object(v___x_3966_);
lean_dec_ref(v_ext_3964_);
lean_dec(v_val_3963_);
lean_dec(v_decl_3962_);
lean_dec_ref(v_env_3961_);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_4032_ == 0)
{
lean_object* v_unused_4033_; 
v_unused_4033_ = lean_ctor_get(v___x_3981_, 0);
lean_dec(v_unused_4033_);
v___x_4025_ = v___x_3981_;
v_isShared_4026_ = v_isSharedCheck_4032_;
goto v_resetjp_4024_;
}
else
{
lean_dec(v___x_3981_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4032_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4030_; 
v___x_4027_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_4028_ = lean_string_append(v_pfx_3980_, v___x_4027_);
if (v_isShared_4026_ == 0)
{
lean_ctor_set_tag(v___x_4025_, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4028_);
v___x_4030_ = v___x_4025_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4028_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_4036_, lean_object* v_attrs_4037_, lean_object* v_env_4038_, lean_object* v_decl_4039_, lean_object* v_val_4040_){
_start:
{
lean_object* v___x_4041_; 
v___x_4041_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_4037_, v_env_4038_, v_decl_4039_, v_val_4040_);
return v___x_4041_;
}
}
lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4043_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_4044_ = lean_st_mk_ref(v___x_4043_);
v___x_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT void l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4046_;
v_res_4046_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4046_;
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_4047_){
_start:
{
lean_object* v_res_4048_; 
v_res_4048_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_4048_;
}
}
lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_4051_, lean_object* v_builder_4052_){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; uint8_t v___x_4056_; 
v___x_4054_ = l_Lean_attributeImplBuilderTableRef;
v___x_4055_ = lean_st_ref_get(v___x_4054_);
v___x_4056_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4055_, v_builderId_4051_);
lean_dec(v___x_4055_);
if (v___x_4056_ == 0)
{
lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4057_ = lean_st_ref_take(v___x_4054_);
v___x_4058_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_4057_, v_builderId_4051_, v_builder_4052_);
v___x_4059_ = lean_st_ref_put(v___x_4054_, v___x_4058_);
v___x_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4059_);
return v___x_4060_;
}
else
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
lean_dec_ref(v_builder_4052_);
v___x_4061_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_4062_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_4051_, v___x_4056_);
v___x_4063_ = lean_string_append(v___x_4061_, v___x_4062_);
lean_dec_ref(v___x_4062_);
v___x_4064_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_4065_ = lean_string_append(v___x_4063_, v___x_4064_);
v___x_4066_ = lean_mk_io_user_error(v___x_4065_);
v___x_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4066_);
return v___x_4067_;
}
}
}
LEAN_EXPORT void l_Lean_registerAttributeImplBuilder_0interp(lean_interpreter_value* stack)
{
lean_object* v_builderId_4051_ = stack[0].m_obj;
lean_object* v_builder_4052_ = stack[1].m_obj;
lean_object* v_res_4068_;
v_res_4068_ = l_Lean_registerAttributeImplBuilder(v_builderId_4051_, v_builder_4052_);
stack->m_obj
 = v_res_4068_;
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_4069_, lean_object* v_builder_4070_, lean_object* v_a_4071_){
_start:
{
lean_object* v_res_4072_; 
v_res_4072_ = l_Lean_registerAttributeImplBuilder(v_builderId_4069_, v_builder_4070_);
return v_res_4072_;
}
}
lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_4073_){
_start:
{
if (lean_obj_tag(v_e_4073_) == 0)
{
lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4083_; 
v_a_4075_ = lean_ctor_get(v_e_4073_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v_e_4073_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4077_ = v_e_4073_;
v_isShared_4078_ = v_isSharedCheck_4083_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_dec(v_e_4073_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4083_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4079_; lean_object* v___x_4081_; 
v___x_4079_ = lean_mk_io_user_error(v_a_4075_);
if (v_isShared_4078_ == 0)
{
lean_ctor_set_tag(v___x_4077_, 1);
lean_ctor_set(v___x_4077_, 0, v___x_4079_);
v___x_4081_ = v___x_4077_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v___x_4079_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
v_a_4084_ = lean_ctor_get(v_e_4073_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v_e_4073_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v_e_4073_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v_e_4073_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
lean_ctor_set_tag(v___x_4086_, 0);
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4073_ = stack[0].m_obj;
lean_object* v_res_4092_;
v_res_4092_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_4073_);
stack->m_obj
 = v_res_4092_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_4093_, lean_object* v_a_4094_){
_start:
{
lean_object* v_res_4095_; 
v_res_4095_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_4093_);
return v_res_4095_;
}
}
lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_4096_, lean_object* v_e_4097_){
_start:
{
lean_object* v___x_4099_; 
v___x_4099_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_4097_);
return v___x_4099_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4097_ = stack[1].m_obj;
lean_object* v_res_4100_;
v_res_4100_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_box(0), v_e_4097_);
stack->m_obj
 = v_res_4100_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_4101_, lean_object* v_e_4102_, lean_object* v_a_4103_){
_start:
{
lean_object* v_res_4104_; 
v_res_4104_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_4101_, v_e_4102_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_4105_, lean_object* v_x_4106_){
_start:
{
if (lean_obj_tag(v_x_4106_) == 0)
{
lean_object* v___x_4107_; 
v___x_4107_ = lean_box(0);
return v___x_4107_;
}
else
{
lean_object* v_key_4108_; lean_object* v_value_4109_; lean_object* v_tail_4110_; uint8_t v___x_4111_; 
v_key_4108_ = lean_ctor_get(v_x_4106_, 0);
v_value_4109_ = lean_ctor_get(v_x_4106_, 1);
v_tail_4110_ = lean_ctor_get(v_x_4106_, 2);
v___x_4111_ = lean_name_eq(v_key_4108_, v_a_4105_);
if (v___x_4111_ == 0)
{
v_x_4106_ = v_tail_4110_;
goto _start;
}
else
{
lean_object* v___x_4113_; 
lean_inc(v_value_4109_);
v___x_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4113_, 0, v_value_4109_);
return v___x_4113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_4114_, lean_object* v_x_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_4114_, v_x_4115_);
lean_dec(v_x_4115_);
lean_dec(v_a_4114_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_4117_, lean_object* v_a_4118_){
_start:
{
lean_object* v_buckets_4119_; lean_object* v___x_4120_; uint64_t v___y_4122_; 
v_buckets_4119_ = lean_ctor_get(v_m_4117_, 1);
v___x_4120_ = lean_array_get_size(v_buckets_4119_);
if (lean_obj_tag(v_a_4118_) == 0)
{
uint64_t v___x_4136_; 
v___x_4136_ = 1723ULL;
v___y_4122_ = v___x_4136_;
goto v___jp_4121_;
}
else
{
uint64_t v_hash_4137_; 
v_hash_4137_ = lean_ctor_get_uint64(v_a_4118_, sizeof(void*)*2);
v___y_4122_ = v_hash_4137_;
goto v___jp_4121_;
}
v___jp_4121_:
{
uint64_t v___x_4123_; uint64_t v___x_4124_; uint64_t v_fold_4125_; uint64_t v___x_4126_; uint64_t v___x_4127_; uint64_t v___x_4128_; size_t v___x_4129_; size_t v___x_4130_; size_t v___x_4131_; size_t v___x_4132_; size_t v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4123_ = 32ULL;
v___x_4124_ = lean_uint64_shift_right(v___y_4122_, v___x_4123_);
v_fold_4125_ = lean_uint64_xor(v___y_4122_, v___x_4124_);
v___x_4126_ = 16ULL;
v___x_4127_ = lean_uint64_shift_right(v_fold_4125_, v___x_4126_);
v___x_4128_ = lean_uint64_xor(v_fold_4125_, v___x_4127_);
v___x_4129_ = lean_uint64_to_usize(v___x_4128_);
v___x_4130_ = lean_usize_of_nat(v___x_4120_);
v___x_4131_ = ((size_t)1ULL);
v___x_4132_ = lean_usize_sub(v___x_4130_, v___x_4131_);
v___x_4133_ = lean_usize_land(v___x_4129_, v___x_4132_);
v___x_4134_ = lean_array_uget_borrowed(v_buckets_4119_, v___x_4133_);
v___x_4135_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_4118_, v___x_4134_);
return v___x_4135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_4138_, lean_object* v_a_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_4138_, v_a_4139_);
lean_dec(v_a_4139_);
lean_dec_ref(v_m_4138_);
return v_res_4140_;
}
}
lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_4142_){
_start:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v_builderId_4146_; lean_object* v_ref_4147_; lean_object* v_args_4148_; lean_object* v___x_4149_; 
v___x_4144_ = l_Lean_attributeImplBuilderTableRef;
v___x_4145_ = lean_st_ref_get(v___x_4144_);
v_builderId_4146_ = lean_ctor_get(v_e_4142_, 0);
lean_inc(v_builderId_4146_);
v_ref_4147_ = lean_ctor_get(v_e_4142_, 1);
lean_inc(v_ref_4147_);
v_args_4148_ = lean_ctor_get(v_e_4142_, 2);
lean_inc(v_args_4148_);
lean_dec_ref(v_e_4142_);
v___x_4149_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4145_, v_builderId_4146_);
lean_dec(v___x_4145_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v___x_4150_; uint8_t v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
lean_dec(v_args_4148_);
lean_dec(v_ref_4147_);
v___x_4150_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_4151_ = 1;
v___x_4152_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_4146_, v___x_4151_);
v___x_4153_ = lean_string_append(v___x_4150_, v___x_4152_);
lean_dec_ref(v___x_4152_);
v___x_4154_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4155_ = lean_string_append(v___x_4153_, v___x_4154_);
v___x_4156_ = lean_mk_io_user_error(v___x_4155_);
v___x_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4156_);
return v___x_4157_;
}
else
{
lean_object* v_val_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
lean_dec(v_builderId_4146_);
v_val_4158_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_val_4158_);
lean_dec_ref_known(v___x_4149_, 1);
v___x_4159_ = lean_apply_2(v_val_4158_, v_ref_4147_, v_args_4148_);
v___x_4160_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_4159_);
return v___x_4160_;
}
}
}
LEAN_EXPORT void l_Lean_mkAttributeImplOfEntry_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4142_ = stack[0].m_obj;
lean_object* v_res_4161_;
v_res_4161_ = l_Lean_mkAttributeImplOfEntry(v_e_4142_);
stack->m_obj
 = v_res_4161_;
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_4162_, lean_object* v_a_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Lean_mkAttributeImplOfEntry(v_e_4162_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_4165_, lean_object* v_m_4166_, lean_object* v_a_4167_){
_start:
{
lean_object* v___x_4168_; 
v___x_4168_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_4166_, v_a_4167_);
return v___x_4168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_4169_, lean_object* v_m_4170_, lean_object* v_a_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_4169_, v_m_4170_, v_a_4171_);
lean_dec(v_a_4171_);
lean_dec_ref(v_m_4170_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_4173_, lean_object* v_a_4174_, lean_object* v_x_4175_){
_start:
{
lean_object* v___x_4176_; 
v___x_4176_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_4174_, v_x_4175_);
return v___x_4176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4177_, lean_object* v_a_4178_, lean_object* v_x_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_4177_, v_a_4178_, v_x_4179_);
lean_dec(v_x_4179_);
lean_dec(v_a_4178_);
return v_res_4180_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4181_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_4182_ = lean_box(0);
v___x_4183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4182_);
lean_ctor_set(v___x_4183_, 1, v___x_4181_);
return v___x_4183_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_4184_; 
v___x_4184_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_4184_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_4185_; 
v___x_4185_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_4185_;
}
}
lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4187_ = l_Lean_attributeMapRef;
v___x_4188_ = lean_st_ref_get(v___x_4187_);
v___x_4189_ = lean_box(0);
v___x_4190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
lean_ctor_set(v___x_4190_, 1, v___x_4188_);
v___x_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4190_);
return v___x_4191_;
}
}
LEAN_EXPORT void l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4192_;
v_res_4192_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
stack->m_obj
 = v_res_4192_;
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_4200_, lean_object* v_opts_4201_, lean_object* v_declName_4202_){
_start:
{
uint8_t v___x_4205_; lean_object* v___x_4206_; 
v___x_4205_ = 0;
lean_inc(v_declName_4202_);
lean_inc_ref(v_env_4200_);
v___x_4206_ = l_Lean_Environment_find_x3f(v_env_4200_, v_declName_4202_, v___x_4205_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v___x_4207_; uint8_t v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; 
lean_dec_ref(v_env_4200_);
v___x_4207_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_4208_ = 1;
v___x_4209_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_4202_, v___x_4208_);
v___x_4210_ = lean_string_append(v___x_4207_, v___x_4209_);
lean_dec_ref(v___x_4209_);
v___x_4211_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4212_ = lean_string_append(v___x_4210_, v___x_4211_);
v___x_4213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4212_);
return v___x_4213_;
}
else
{
lean_object* v_val_4214_; lean_object* v___x_4215_; 
v_val_4214_ = lean_ctor_get(v___x_4206_, 0);
lean_inc(v_val_4214_);
lean_dec_ref_known(v___x_4206_, 1);
v___x_4215_ = l_Lean_ConstantInfo_type(v_val_4214_);
lean_dec(v_val_4214_);
if (lean_obj_tag(v___x_4215_) == 4)
{
lean_object* v_declName_4216_; 
v_declName_4216_ = lean_ctor_get(v___x_4215_, 0);
lean_inc(v_declName_4216_);
lean_dec_ref_known(v___x_4215_, 2);
if (lean_obj_tag(v_declName_4216_) == 1)
{
lean_object* v_pre_4217_; 
v_pre_4217_ = lean_ctor_get(v_declName_4216_, 0);
lean_inc(v_pre_4217_);
if (lean_obj_tag(v_pre_4217_) == 1)
{
lean_object* v_pre_4218_; 
v_pre_4218_ = lean_ctor_get(v_pre_4217_, 0);
if (lean_obj_tag(v_pre_4218_) == 0)
{
lean_object* v_str_4219_; lean_object* v_str_4220_; lean_object* v___x_4221_; uint8_t v___x_4222_; 
v_str_4219_ = lean_ctor_get(v_declName_4216_, 1);
lean_inc_ref(v_str_4219_);
lean_dec_ref_known(v_declName_4216_, 2);
v_str_4220_ = lean_ctor_get(v_pre_4217_, 1);
lean_inc_ref(v_str_4220_);
lean_dec_ref_known(v_pre_4217_, 2);
v___x_4221_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_4222_ = lean_string_dec_eq(v_str_4220_, v___x_4221_);
lean_dec_ref(v_str_4220_);
if (v___x_4222_ == 0)
{
lean_dec_ref(v_str_4219_);
lean_dec(v_declName_4202_);
lean_dec_ref(v_env_4200_);
goto v___jp_4203_;
}
else
{
lean_object* v___x_4223_; uint8_t v___x_4224_; 
v___x_4223_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_4224_ = lean_string_dec_eq(v_str_4219_, v___x_4223_);
lean_dec_ref(v_str_4219_);
if (v___x_4224_ == 0)
{
lean_dec(v_declName_4202_);
lean_dec_ref(v_env_4200_);
goto v___jp_4203_;
}
else
{
lean_object* v___x_4225_; 
v___x_4225_ = l_Lean_Environment_evalConst___redArg(v_env_4200_, v_opts_4201_, v_declName_4202_, v___x_4224_);
lean_dec(v_declName_4202_);
lean_dec_ref(v_env_4200_);
return v___x_4225_;
}
}
}
else
{
lean_dec_ref_known(v_pre_4217_, 2);
lean_dec_ref_known(v_declName_4216_, 2);
lean_dec(v_declName_4202_);
lean_dec_ref(v_env_4200_);
goto v___jp_4203_;
}
}
else
{
lean_dec(v_pre_4217_);
lean_dec_ref_known(v_declName_4216_, 2);
lean_dec(v_declName_4202_);
lean_dec_ref(v_env_4200_);
goto v___jp_4203_;
}
}
else
{
lean_dec(v_declName_4216_);
lean_dec(v_declName_4202_);
lean_dec_ref(v_env_4200_);
goto v___jp_4203_;
}
}
else
{
lean_dec_ref(v___x_4215_);
lean_dec(v_declName_4202_);
lean_dec_ref(v_env_4200_);
goto v___jp_4203_;
}
}
v___jp_4203_:
{
lean_object* v___x_4204_; 
v___x_4204_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_4204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_4226_, lean_object* v_opts_4227_, lean_object* v_declName_4228_){
_start:
{
lean_object* v_res_4229_; 
v_res_4229_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_4226_, v_opts_4227_, v_declName_4228_);
lean_dec_ref(v_opts_4227_);
return v_res_4229_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_4230_, size_t v_i_4231_, size_t v_stop_4232_, lean_object* v_b_4233_){
_start:
{
uint8_t v___x_4235_; 
v___x_4235_ = lean_usize_dec_eq(v_i_4231_, v_stop_4232_);
if (v___x_4235_ == 0)
{
lean_object* v___x_4236_; lean_object* v___x_4237_; 
v___x_4236_ = lean_array_uget_borrowed(v_as_4230_, v_i_4231_);
lean_inc(v___x_4236_);
v___x_4237_ = l_Lean_mkAttributeImplOfEntry(v___x_4236_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v_a_4238_; lean_object* v_toAttributeImplCore_4239_; lean_object* v_name_4240_; lean_object* v___x_4241_; size_t v___x_4242_; size_t v___x_4243_; 
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
lean_inc(v_a_4238_);
lean_dec_ref_known(v___x_4237_, 1);
v_toAttributeImplCore_4239_ = lean_ctor_get(v_a_4238_, 0);
v_name_4240_ = lean_ctor_get(v_toAttributeImplCore_4239_, 1);
lean_inc(v_name_4240_);
v___x_4241_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_4233_, v_name_4240_, v_a_4238_);
v___x_4242_ = ((size_t)1ULL);
v___x_4243_ = lean_usize_add(v_i_4231_, v___x_4242_);
v_i_4231_ = v___x_4243_;
v_b_4233_ = v___x_4241_;
goto _start;
}
else
{
lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4252_; 
lean_dec_ref(v_b_4233_);
v_a_4245_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4247_ = v___x_4237_;
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4237_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___x_4250_; 
if (v_isShared_4248_ == 0)
{
v___x_4250_ = v___x_4247_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_a_4245_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
else
{
lean_object* v___x_4253_; 
v___x_4253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4253_, 0, v_b_4233_);
return v___x_4253_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4230_ = stack[0].m_obj;
size_t v_i_4231_ = stack[1].m_num;
size_t v_stop_4232_ = stack[2].m_num;
lean_object* v_b_4233_ = stack[3].m_obj;
lean_object* v_res_4254_;
v_res_4254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4230_, v_i_4231_, v_stop_4232_, v_b_4233_);
stack->m_obj
 = v_res_4254_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_4255_, lean_object* v_i_4256_, lean_object* v_stop_4257_, lean_object* v_b_4258_, lean_object* v___y_4259_){
_start:
{
size_t v_i_boxed_4260_; size_t v_stop_boxed_4261_; lean_object* v_res_4262_; 
v_i_boxed_4260_ = lean_unbox_usize(v_i_4256_);
lean_dec(v_i_4256_);
v_stop_boxed_4261_ = lean_unbox_usize(v_stop_4257_);
lean_dec(v_stop_4257_);
v_res_4262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4255_, v_i_boxed_4260_, v_stop_boxed_4261_, v_b_4258_);
lean_dec_ref(v_as_4255_);
return v_res_4262_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_4263_, size_t v_i_4264_, size_t v_stop_4265_, lean_object* v_b_4266_, lean_object* v___y_4267_){
_start:
{
lean_object* v_a_4270_; lean_object* v___y_4275_; uint8_t v___x_4277_; 
v___x_4277_ = lean_usize_dec_eq(v_i_4264_, v_stop_4265_);
if (v___x_4277_ == 0)
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; uint8_t v___x_4281_; 
v___x_4278_ = lean_array_uget_borrowed(v_as_4263_, v_i_4264_);
v___x_4279_ = lean_unsigned_to_nat(0u);
v___x_4280_ = lean_array_get_size(v___x_4278_);
v___x_4281_ = lean_nat_dec_lt(v___x_4279_, v___x_4280_);
if (v___x_4281_ == 0)
{
v_a_4270_ = v_b_4266_;
goto v___jp_4269_;
}
else
{
uint8_t v___x_4282_; 
v___x_4282_ = lean_nat_dec_le(v___x_4280_, v___x_4280_);
if (v___x_4282_ == 0)
{
if (v___x_4281_ == 0)
{
v_a_4270_ = v_b_4266_;
goto v___jp_4269_;
}
else
{
size_t v___x_4283_; size_t v___x_4284_; lean_object* v___x_4285_; 
v___x_4283_ = ((size_t)0ULL);
v___x_4284_ = lean_usize_of_nat(v___x_4280_);
v___x_4285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4278_, v___x_4283_, v___x_4284_, v_b_4266_);
v___y_4275_ = v___x_4285_;
goto v___jp_4274_;
}
}
else
{
size_t v___x_4286_; size_t v___x_4287_; lean_object* v___x_4288_; 
v___x_4286_ = ((size_t)0ULL);
v___x_4287_ = lean_usize_of_nat(v___x_4280_);
v___x_4288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4278_, v___x_4286_, v___x_4287_, v_b_4266_);
v___y_4275_ = v___x_4288_;
goto v___jp_4274_;
}
}
}
else
{
lean_object* v___x_4289_; 
v___x_4289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4289_, 0, v_b_4266_);
return v___x_4289_;
}
v___jp_4269_:
{
size_t v___x_4271_; size_t v___x_4272_; 
v___x_4271_ = ((size_t)1ULL);
v___x_4272_ = lean_usize_add(v_i_4264_, v___x_4271_);
v_i_4264_ = v___x_4272_;
v_b_4266_ = v_a_4270_;
goto _start;
}
v___jp_4274_:
{
if (lean_obj_tag(v___y_4275_) == 0)
{
lean_object* v_a_4276_; 
v_a_4276_ = lean_ctor_get(v___y_4275_, 0);
lean_inc(v_a_4276_);
lean_dec_ref_known(v___y_4275_, 1);
v_a_4270_ = v_a_4276_;
goto v___jp_4269_;
}
else
{
return v___y_4275_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4263_ = stack[0].m_obj;
size_t v_i_4264_ = stack[1].m_num;
size_t v_stop_4265_ = stack[2].m_num;
lean_object* v_b_4266_ = stack[3].m_obj;
lean_object* v___y_4267_ = stack[4].m_obj;
lean_object* v_res_4290_;
v_res_4290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4263_, v_i_4264_, v_stop_4265_, v_b_4266_, v___y_4267_);
stack->m_obj
 = v_res_4290_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4291_, lean_object* v_i_4292_, lean_object* v_stop_4293_, lean_object* v_b_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_){
_start:
{
size_t v_i_boxed_4297_; size_t v_stop_boxed_4298_; lean_object* v_res_4299_; 
v_i_boxed_4297_ = lean_unbox_usize(v_i_4292_);
lean_dec(v_i_4292_);
v_stop_boxed_4298_ = lean_unbox_usize(v_stop_4293_);
lean_dec(v_stop_4293_);
v_res_4299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4291_, v_i_boxed_4297_, v_stop_boxed_4298_, v_b_4294_, v___y_4295_);
lean_dec_ref(v___y_4295_);
lean_dec_ref(v_as_4291_);
return v_res_4299_;
}
}
lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4300_, lean_object* v_a_4301_){
_start:
{
lean_object* v_a_4304_; lean_object* v___y_4309_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; uint8_t v___x_4323_; 
v___x_4319_ = l_Lean_attributeMapRef;
v___x_4320_ = lean_st_ref_get(v___x_4319_);
v___x_4321_ = lean_unsigned_to_nat(0u);
v___x_4322_ = lean_array_get_size(v_es_4300_);
v___x_4323_ = lean_nat_dec_lt(v___x_4321_, v___x_4322_);
if (v___x_4323_ == 0)
{
v_a_4304_ = v___x_4320_;
goto v___jp_4303_;
}
else
{
uint8_t v___x_4324_; 
v___x_4324_ = lean_nat_dec_le(v___x_4322_, v___x_4322_);
if (v___x_4324_ == 0)
{
if (v___x_4323_ == 0)
{
v_a_4304_ = v___x_4320_;
goto v___jp_4303_;
}
else
{
size_t v___x_4325_; size_t v___x_4326_; lean_object* v___x_4327_; 
v___x_4325_ = ((size_t)0ULL);
v___x_4326_ = lean_usize_of_nat(v___x_4322_);
v___x_4327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4300_, v___x_4325_, v___x_4326_, v___x_4320_, v_a_4301_);
v___y_4309_ = v___x_4327_;
goto v___jp_4308_;
}
}
else
{
size_t v___x_4328_; size_t v___x_4329_; lean_object* v___x_4330_; 
v___x_4328_ = ((size_t)0ULL);
v___x_4329_ = lean_usize_of_nat(v___x_4322_);
v___x_4330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4300_, v___x_4328_, v___x_4329_, v___x_4320_, v_a_4301_);
v___y_4309_ = v___x_4330_;
goto v___jp_4308_;
}
}
v___jp_4303_:
{
lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v___x_4305_ = lean_box(0);
v___x_4306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4305_);
lean_ctor_set(v___x_4306_, 1, v_a_4304_);
v___x_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4306_);
return v___x_4307_;
}
v___jp_4308_:
{
if (lean_obj_tag(v___y_4309_) == 0)
{
lean_object* v_a_4310_; 
v_a_4310_ = lean_ctor_get(v___y_4309_, 0);
lean_inc(v_a_4310_);
lean_dec_ref_known(v___y_4309_, 1);
v_a_4304_ = v_a_4310_;
goto v___jp_4303_;
}
else
{
lean_object* v_a_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4318_; 
v_a_4311_ = lean_ctor_get(v___y_4309_, 0);
v_isSharedCheck_4318_ = !lean_is_exclusive(v___y_4309_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4313_ = v___y_4309_;
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_a_4311_);
lean_dec(v___y_4309_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
lean_object* v___x_4316_; 
if (v_isShared_4314_ == 0)
{
v___x_4316_ = v___x_4313_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
v___x_4316_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
return v___x_4316_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported_0interp(lean_interpreter_value* stack)
{
lean_object* v_es_4300_ = stack[0].m_obj;
lean_object* v_a_4301_ = stack[1].m_obj;
lean_object* v_res_4331_;
v_res_4331_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4300_, v_a_4301_);
stack->m_obj
 = v_res_4331_;
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4332_, v_a_4333_);
lean_dec_ref(v_a_4333_);
lean_dec_ref(v_es_4332_);
return v_res_4335_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4336_, size_t v_i_4337_, size_t v_stop_4338_, lean_object* v_b_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v___x_4342_; 
v___x_4342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4336_, v_i_4337_, v_stop_4338_, v_b_4339_);
return v___x_4342_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4336_ = stack[0].m_obj;
size_t v_i_4337_ = stack[1].m_num;
size_t v_stop_4338_ = stack[2].m_num;
lean_object* v_b_4339_ = stack[3].m_obj;
lean_object* v___y_4340_ = stack[4].m_obj;
lean_object* v_res_4343_;
v_res_4343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4336_, v_i_4337_, v_stop_4338_, v_b_4339_, v___y_4340_);
stack->m_obj
 = v_res_4343_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4344_, lean_object* v_i_4345_, lean_object* v_stop_4346_, lean_object* v_b_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
size_t v_i_boxed_4350_; size_t v_stop_boxed_4351_; lean_object* v_res_4352_; 
v_i_boxed_4350_ = lean_unbox_usize(v_i_4345_);
lean_dec(v_i_4345_);
v_stop_boxed_4351_ = lean_unbox_usize(v_stop_4346_);
lean_dec(v_stop_4346_);
v_res_4352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4344_, v_i_boxed_4350_, v_stop_boxed_4351_, v_b_4347_, v___y_4348_);
lean_dec_ref(v___y_4348_);
lean_dec_ref(v_as_4344_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4353_, lean_object* v_e_4354_){
_start:
{
lean_object* v_snd_4355_; lean_object* v_toAttributeImplCore_4356_; lean_object* v_fst_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4375_; 
v_snd_4355_ = lean_ctor_get(v_e_4354_, 1);
lean_inc(v_snd_4355_);
v_toAttributeImplCore_4356_ = lean_ctor_get(v_snd_4355_, 0);
v_fst_4357_ = lean_ctor_get(v_e_4354_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v_e_4354_);
if (v_isSharedCheck_4375_ == 0)
{
lean_object* v_unused_4376_; 
v_unused_4376_ = lean_ctor_get(v_e_4354_, 1);
lean_dec(v_unused_4376_);
v___x_4359_ = v_e_4354_;
v_isShared_4360_ = v_isSharedCheck_4375_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_fst_4357_);
lean_dec(v_e_4354_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4375_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v_newEntries_4361_; lean_object* v_map_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4374_; 
v_newEntries_4361_ = lean_ctor_get(v_s_4353_, 0);
v_map_4362_ = lean_ctor_get(v_s_4353_, 1);
v_isSharedCheck_4374_ = !lean_is_exclusive(v_s_4353_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4364_ = v_s_4353_;
v_isShared_4365_ = v_isSharedCheck_4374_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_map_4362_);
lean_inc(v_newEntries_4361_);
lean_dec(v_s_4353_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4374_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v_name_4366_; lean_object* v___x_4368_; 
v_name_4366_ = lean_ctor_get(v_toAttributeImplCore_4356_, 1);
lean_inc(v_name_4366_);
if (v_isShared_4360_ == 0)
{
lean_ctor_set_tag(v___x_4359_, 1);
lean_ctor_set(v___x_4359_, 1, v_newEntries_4361_);
v___x_4368_ = v___x_4359_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v_fst_4357_);
lean_ctor_set(v_reuseFailAlloc_4373_, 1, v_newEntries_4361_);
v___x_4368_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
lean_object* v___x_4369_; lean_object* v___x_4371_; 
v___x_4369_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4362_, v_name_4366_, v_snd_4355_);
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 1, v___x_4369_);
lean_ctor_set(v___x_4364_, 0, v___x_4368_);
v___x_4371_ = v___x_4364_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v___x_4368_);
lean_ctor_set(v_reuseFailAlloc_4372_, 1, v___x_4369_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4377_, lean_object* v_s_4378_){
_start:
{
lean_object* v_newEntries_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v_newEntries_4379_ = lean_ctor_get(v_s_4378_, 0);
lean_inc(v_newEntries_4379_);
lean_dec_ref(v_s_4378_);
v___x_4380_ = l_List_reverse___redArg(v_newEntries_4379_);
v___x_4381_ = lean_array_mk(v___x_4380_);
lean_inc_ref_n(v___x_4381_, 2);
v___x_4382_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4382_, 0, v___x_4381_);
lean_ctor_set(v___x_4382_, 1, v___x_4381_);
lean_ctor_set(v___x_4382_, 2, v___x_4381_);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4383_, lean_object* v_s_4384_){
_start:
{
lean_object* v_res_4385_; 
v_res_4385_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4383_, v_s_4384_);
lean_dec_ref(v_x_4383_);
return v_res_4385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4386_){
_start:
{
lean_object* v_newEntries_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4398_; 
v_newEntries_4387_ = lean_ctor_get(v_s_4386_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v_s_4386_);
if (v_isSharedCheck_4398_ == 0)
{
lean_object* v_unused_4399_; 
v_unused_4399_ = lean_ctor_get(v_s_4386_, 1);
lean_dec(v_unused_4399_);
v___x_4389_ = v_s_4386_;
v_isShared_4390_ = v_isSharedCheck_4398_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_newEntries_4387_);
lean_dec(v_s_4386_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4398_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4396_; 
v___x_4391_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4392_ = l_List_lengthTR___redArg(v_newEntries_4387_);
lean_dec(v_newEntries_4387_);
v___x_4393_ = l_Nat_reprFast(v___x_4392_);
v___x_4394_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4394_, 0, v___x_4393_);
if (v_isShared_4390_ == 0)
{
lean_ctor_set_tag(v___x_4389_, 5);
lean_ctor_set(v___x_4389_, 1, v___x_4394_);
lean_ctor_set(v___x_4389_, 0, v___x_4391_);
v___x_4396_ = v___x_4389_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v___x_4391_);
lean_ctor_set(v_reuseFailAlloc_4397_, 1, v___x_4394_);
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
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4400_){
_start:
{
lean_object* v_newEntries_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; 
v_newEntries_4401_ = lean_ctor_get(v_s_4400_, 0);
lean_inc(v_newEntries_4401_);
lean_dec_ref(v_s_4400_);
v___x_4402_ = l_List_reverse___redArg(v_newEntries_4401_);
v___x_4403_ = lean_array_mk(v___x_4402_);
return v___x_4403_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___f_4416_; lean_object* v___f_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4413_ = 0;
v___x_4414_ = lean_box(0);
v___x_4415_ = lean_box(2);
v___f_4416_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4417_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4418_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4419_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4420_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4421_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4422_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_4422_, 0, v___x_4421_);
lean_ctor_set(v___x_4422_, 1, v___x_4420_);
lean_ctor_set(v___x_4422_, 2, v___x_4419_);
lean_ctor_set(v___x_4422_, 3, v___x_4418_);
lean_ctor_set(v___x_4422_, 4, v___f_4417_);
lean_ctor_set(v___x_4422_, 5, v___f_4416_);
lean_ctor_set(v___x_4422_, 6, v___x_4415_);
lean_ctor_set(v___x_4422_, 7, v___x_4414_);
lean_ctor_set_uint8(v___x_4422_, sizeof(void*)*8, v___x_4413_);
lean_ctor_set_uint8(v___x_4422_, sizeof(void*)*8 + 1, v___x_4413_);
return v___x_4422_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___f_4423_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4424_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4424_);
lean_ctor_set(v___x_4425_, 1, v___f_4423_);
return v___x_4425_;
}
}
lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; 
v___x_4427_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4428_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4427_);
return v___x_4428_;
}
}
LEAN_EXPORT void l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4429_;
v_res_4429_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4429_;
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4430_){
_start:
{
lean_object* v_res_4431_; 
v_res_4431_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4431_;
}
}
lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4432_){
_start:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; uint8_t v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4434_ = l_Lean_attributeMapRef;
v___x_4435_ = lean_st_ref_get(v___x_4434_);
v___x_4436_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4435_, v_n_4432_);
lean_dec(v___x_4435_);
v___x_4437_ = lean_box(v___x_4436_);
v___x_4438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4438_, 0, v___x_4437_);
return v___x_4438_;
}
}
LEAN_EXPORT void l_Lean_isBuiltinAttribute_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_4432_ = stack[0].m_obj;
lean_object* v_res_4439_;
v_res_4439_ = l_Lean_isBuiltinAttribute(v_n_4432_);
stack->m_obj
 = v_res_4439_;
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4440_, lean_object* v_a_4441_){
_start:
{
lean_object* v_res_4442_; 
v_res_4442_ = l_Lean_isBuiltinAttribute(v_n_4440_);
lean_dec(v_n_4440_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4443_, lean_object* v_x_4444_){
_start:
{
if (lean_obj_tag(v_x_4444_) == 0)
{
return v_x_4443_;
}
else
{
lean_object* v_key_4445_; lean_object* v_tail_4446_; lean_object* v___x_4447_; 
v_key_4445_ = lean_ctor_get(v_x_4444_, 0);
v_tail_4446_ = lean_ctor_get(v_x_4444_, 2);
lean_inc(v_key_4445_);
v___x_4447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4447_, 0, v_key_4445_);
lean_ctor_set(v___x_4447_, 1, v_x_4443_);
v_x_4443_ = v___x_4447_;
v_x_4444_ = v_tail_4446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4449_, lean_object* v_x_4450_){
_start:
{
lean_object* v_res_4451_; 
v_res_4451_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4449_, v_x_4450_);
lean_dec(v_x_4450_);
return v_res_4451_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4452_, size_t v_i_4453_, size_t v_stop_4454_, lean_object* v_b_4455_){
_start:
{
uint8_t v___x_4456_; 
v___x_4456_ = lean_usize_dec_eq(v_i_4453_, v_stop_4454_);
if (v___x_4456_ == 0)
{
lean_object* v___x_4457_; lean_object* v___x_4458_; size_t v___x_4459_; size_t v___x_4460_; 
v___x_4457_ = lean_array_uget_borrowed(v_as_4452_, v_i_4453_);
v___x_4458_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4455_, v___x_4457_);
v___x_4459_ = ((size_t)1ULL);
v___x_4460_ = lean_usize_add(v_i_4453_, v___x_4459_);
v_i_4453_ = v___x_4460_;
v_b_4455_ = v___x_4458_;
goto _start;
}
else
{
return v_b_4455_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4452_ = stack[0].m_obj;
size_t v_i_4453_ = stack[1].m_num;
size_t v_stop_4454_ = stack[2].m_num;
lean_object* v_b_4455_ = stack[3].m_obj;
lean_object* v_res_4462_;
v_res_4462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4452_, v_i_4453_, v_stop_4454_, v_b_4455_);
stack->m_obj
 = v_res_4462_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4463_, lean_object* v_i_4464_, lean_object* v_stop_4465_, lean_object* v_b_4466_){
_start:
{
size_t v_i_boxed_4467_; size_t v_stop_boxed_4468_; lean_object* v_res_4469_; 
v_i_boxed_4467_ = lean_unbox_usize(v_i_4464_);
lean_dec(v_i_4464_);
v_stop_boxed_4468_ = lean_unbox_usize(v_stop_4465_);
lean_dec(v_stop_4465_);
v_res_4469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4463_, v_i_boxed_4467_, v_stop_boxed_4468_, v_b_4466_);
lean_dec_ref(v_as_4463_);
return v_res_4469_;
}
}
lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v_buckets_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; uint8_t v___x_4477_; 
v___x_4471_ = l_Lean_attributeMapRef;
v___x_4472_ = lean_st_ref_get(v___x_4471_);
v_buckets_4473_ = lean_ctor_get(v___x_4472_, 1);
lean_inc_ref(v_buckets_4473_);
lean_dec(v___x_4472_);
v___x_4474_ = lean_box(0);
v___x_4475_ = lean_unsigned_to_nat(0u);
v___x_4476_ = lean_array_get_size(v_buckets_4473_);
v___x_4477_ = lean_nat_dec_lt(v___x_4475_, v___x_4476_);
if (v___x_4477_ == 0)
{
lean_object* v___x_4478_; 
lean_dec_ref(v_buckets_4473_);
v___x_4478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4478_, 0, v___x_4474_);
return v___x_4478_;
}
else
{
size_t v___x_4479_; size_t v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; 
v___x_4479_ = ((size_t)0ULL);
v___x_4480_ = lean_usize_of_nat(v___x_4476_);
v___x_4481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4473_, v___x_4479_, v___x_4480_, v___x_4474_);
lean_dec_ref(v_buckets_4473_);
v___x_4482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4481_);
return v___x_4482_;
}
}
}
LEAN_EXPORT void l_Lean_getBuiltinAttributeNames_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4483_;
v_res_4483_ = l_Lean_getBuiltinAttributeNames();
stack->m_obj
 = v_res_4483_;
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4484_){
_start:
{
lean_object* v_res_4485_; 
v_res_4485_ = l_Lean_getBuiltinAttributeNames();
return v_res_4485_;
}
}
lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4487_){
_start:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4489_ = l_Lean_attributeMapRef;
v___x_4490_ = lean_st_ref_get(v___x_4489_);
v___x_4491_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4490_, v_attrName_4487_);
lean_dec(v___x_4490_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v___x_4492_; uint8_t v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___x_4492_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4493_ = 1;
v___x_4494_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4487_, v___x_4493_);
v___x_4495_ = lean_string_append(v___x_4492_, v___x_4494_);
lean_dec_ref(v___x_4494_);
v___x_4496_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4497_ = lean_string_append(v___x_4495_, v___x_4496_);
v___x_4498_ = lean_mk_io_user_error(v___x_4497_);
v___x_4499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4499_, 0, v___x_4498_);
return v___x_4499_;
}
else
{
lean_object* v_val_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4507_; 
lean_dec(v_attrName_4487_);
v_val_4500_ = lean_ctor_get(v___x_4491_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4502_ = v___x_4491_;
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_val_4500_);
lean_dec(v___x_4491_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4505_; 
if (v_isShared_4503_ == 0)
{
lean_ctor_set_tag(v___x_4502_, 0);
v___x_4505_ = v___x_4502_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_val_4500_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getBuiltinAttributeImpl_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_4487_ = stack[0].m_obj;
lean_object* v_res_4508_;
v_res_4508_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4487_);
stack->m_obj
 = v_res_4508_;
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4509_, lean_object* v_a_4510_){
_start:
{
lean_object* v_res_4511_; 
v_res_4511_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4509_);
return v_res_4511_;
}
}
uint8_t l_Lean_isAttribute(lean_object* v_env_4512_, lean_object* v_attrName_4513_){
_start:
{
lean_object* v___x_4514_; lean_object* v_toEnvExtension_4515_; lean_object* v_asyncMode_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; uint8_t v___x_4519_; lean_object* v___x_4520_; lean_object* v_map_4521_; uint8_t v___x_4522_; 
v___x_4514_ = l_Lean_attributeExtension;
v_toEnvExtension_4515_ = lean_ctor_get(v___x_4514_, 0);
v_asyncMode_4516_ = lean_ctor_get(v_toEnvExtension_4515_, 2);
v___x_4517_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4518_ = lean_box(0);
v___x_4519_ = 0;
v___x_4520_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4517_, v___x_4514_, v_env_4512_, v_asyncMode_4516_, v___x_4518_, v___x_4519_);
v_map_4521_ = lean_ctor_get(v___x_4520_, 1);
lean_inc_ref(v_map_4521_);
lean_dec(v___x_4520_);
v___x_4522_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4521_, v_attrName_4513_);
lean_dec_ref(v_map_4521_);
return v___x_4522_;
}
}
LEAN_EXPORT void l_Lean_isAttribute_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_4512_ = stack[0].m_obj;
lean_object* v_attrName_4513_ = stack[1].m_obj;
uint8_t v_res_4523_;
v_res_4523_ = l_Lean_isAttribute(v_env_4512_, v_attrName_4513_);
stack->m_num = v_res_4523_;
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4524_, lean_object* v_attrName_4525_){
_start:
{
uint8_t v_res_4526_; lean_object* v_r_4527_; 
v_res_4526_ = l_Lean_isAttribute(v_env_4524_, v_attrName_4525_);
lean_dec(v_attrName_4525_);
v_r_4527_ = lean_box(v_res_4526_);
return v_r_4527_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4528_){
_start:
{
lean_object* v___x_4529_; lean_object* v_toEnvExtension_4530_; lean_object* v_asyncMode_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; uint8_t v___x_4534_; lean_object* v___x_4535_; lean_object* v_map_4536_; lean_object* v_buckets_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; uint8_t v___x_4541_; 
v___x_4529_ = l_Lean_attributeExtension;
v_toEnvExtension_4530_ = lean_ctor_get(v___x_4529_, 0);
v_asyncMode_4531_ = lean_ctor_get(v_toEnvExtension_4530_, 2);
v___x_4532_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4533_ = lean_box(0);
v___x_4534_ = 0;
v___x_4535_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4532_, v___x_4529_, v_env_4528_, v_asyncMode_4531_, v___x_4533_, v___x_4534_);
v_map_4536_ = lean_ctor_get(v___x_4535_, 1);
lean_inc_ref(v_map_4536_);
lean_dec(v___x_4535_);
v_buckets_4537_ = lean_ctor_get(v_map_4536_, 1);
lean_inc_ref(v_buckets_4537_);
lean_dec_ref(v_map_4536_);
v___x_4538_ = lean_box(0);
v___x_4539_ = lean_unsigned_to_nat(0u);
v___x_4540_ = lean_array_get_size(v_buckets_4537_);
v___x_4541_ = lean_nat_dec_lt(v___x_4539_, v___x_4540_);
if (v___x_4541_ == 0)
{
lean_dec_ref(v_buckets_4537_);
return v___x_4538_;
}
else
{
size_t v___x_4542_; size_t v___x_4543_; lean_object* v___x_4544_; 
v___x_4542_ = ((size_t)0ULL);
v___x_4543_ = lean_usize_of_nat(v___x_4540_);
v___x_4544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4537_, v___x_4542_, v___x_4543_, v___x_4538_);
lean_dec_ref(v_buckets_4537_);
return v___x_4544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4545_, lean_object* v_attrName_4546_){
_start:
{
lean_object* v___x_4547_; lean_object* v_toEnvExtension_4548_; lean_object* v_asyncMode_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; uint8_t v___x_4552_; lean_object* v___x_4553_; lean_object* v_map_4554_; lean_object* v___x_4555_; 
v___x_4547_ = l_Lean_attributeExtension;
v_toEnvExtension_4548_ = lean_ctor_get(v___x_4547_, 0);
v_asyncMode_4549_ = lean_ctor_get(v_toEnvExtension_4548_, 2);
v___x_4550_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4551_ = lean_box(0);
v___x_4552_ = 0;
v___x_4553_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4550_, v___x_4547_, v_env_4545_, v_asyncMode_4549_, v___x_4551_, v___x_4552_);
v_map_4554_ = lean_ctor_get(v___x_4553_, 1);
lean_inc_ref(v_map_4554_);
lean_dec(v___x_4553_);
v___x_4555_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4554_, v_attrName_4546_);
lean_dec_ref(v_map_4554_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v___x_4556_; uint8_t v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; 
v___x_4556_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4557_ = 1;
v___x_4558_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4546_, v___x_4557_);
v___x_4559_ = lean_string_append(v___x_4556_, v___x_4558_);
lean_dec_ref(v___x_4558_);
v___x_4560_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4561_ = lean_string_append(v___x_4559_, v___x_4560_);
v___x_4562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4561_);
return v___x_4562_;
}
else
{
lean_object* v_val_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
lean_dec(v_attrName_4546_);
v_val_4563_ = lean_ctor_get(v___x_4555_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4555_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_val_4563_);
lean_dec(v___x_4555_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_val_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___lam__0(lean_object* v___x_4571_, lean_object* v___x_4572_, lean_object* v_s_4573_){
_start:
{
lean_object* v_addEntryFn_4574_; lean_object* v_importedEntries_4575_; lean_object* v_state_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4584_; 
v_addEntryFn_4574_ = lean_ctor_get(v___x_4571_, 3);
lean_inc(v_addEntryFn_4574_);
lean_dec_ref(v___x_4571_);
v_importedEntries_4575_ = lean_ctor_get(v_s_4573_, 0);
v_state_4576_ = lean_ctor_get(v_s_4573_, 1);
v_isSharedCheck_4584_ = !lean_is_exclusive(v_s_4573_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4578_ = v_s_4573_;
v_isShared_4579_ = v_isSharedCheck_4584_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_state_4576_);
lean_inc(v_importedEntries_4575_);
lean_dec(v_s_4573_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4584_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v_state_4580_; lean_object* v___x_4582_; 
v_state_4580_ = lean_apply_2(v_addEntryFn_4574_, v_state_4576_, v___x_4572_);
if (v_isShared_4579_ == 0)
{
lean_ctor_set(v___x_4578_, 1, v_state_4580_);
v___x_4582_ = v___x_4578_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_importedEntries_4575_);
lean_ctor_set(v_reuseFailAlloc_4583_, 1, v_state_4580_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
}
}
lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4585_, lean_object* v_builderId_4586_, lean_object* v_ref_4587_, lean_object* v_args_4588_){
_start:
{
lean_object* v_entry_4590_; lean_object* v___x_4591_; 
v_entry_4590_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4590_, 0, v_builderId_4586_);
lean_ctor_set(v_entry_4590_, 1, v_ref_4587_);
lean_ctor_set(v_entry_4590_, 2, v_args_4588_);
lean_inc_ref(v_entry_4590_);
v___x_4591_ = l_Lean_mkAttributeImplOfEntry(v_entry_4590_);
if (lean_obj_tag(v___x_4591_) == 0)
{
lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4625_; 
v_a_4592_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4594_ = v___x_4591_;
v_isShared_4595_ = v_isSharedCheck_4625_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v___x_4591_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4625_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v_toAttributeImplCore_4596_; lean_object* v_name_4597_; uint8_t v___x_4598_; 
v_toAttributeImplCore_4596_ = lean_ctor_get(v_a_4592_, 0);
v_name_4597_ = lean_ctor_get(v_toAttributeImplCore_4596_, 1);
lean_inc_ref(v_env_4585_);
v___x_4598_ = l_Lean_isAttribute(v_env_4585_, v_name_4597_);
if (v___x_4598_ == 0)
{
lean_object* v___x_4599_; lean_object* v_toEnvExtension_4600_; lean_object* v_asyncMode_4601_; uint8_t v_logWrites_4602_; lean_object* v___x_4603_; lean_object* v___f_4604_; lean_object* v___x_4605_; uint8_t v___x_4606_; 
v___x_4599_ = l_Lean_attributeExtension;
v_toEnvExtension_4600_ = lean_ctor_get(v___x_4599_, 0);
v_asyncMode_4601_ = lean_ctor_get(v_toEnvExtension_4600_, 2);
v_logWrites_4602_ = lean_ctor_get_uint8(v_toEnvExtension_4600_, sizeof(void*)*6);
v___x_4603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4603_, 0, v_entry_4590_);
lean_ctor_set(v___x_4603_, 1, v_a_4592_);
v___f_4604_ = lean_alloc_closure((void*)(l_Lean_registerAttributeOfBuilder___lam__0), 3, 2);
lean_closure_set(v___f_4604_, 0, v___x_4599_);
lean_closure_set(v___f_4604_, 1, v___x_4603_);
v___x_4605_ = lean_box(0);
v___x_4606_ = 1;
if (v_logWrites_4602_ == 0)
{
lean_object* v___x_4607_; lean_object* v___x_4609_; 
lean_inc_ref(v_toEnvExtension_4600_);
v___x_4607_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4600_, v_env_4585_, v___f_4604_, v_asyncMode_4601_, v___x_4605_, v___x_4606_);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 0, v___x_4607_);
v___x_4609_ = v___x_4594_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v___x_4607_);
v___x_4609_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
return v___x_4609_;
}
}
else
{
lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4614_; 
lean_inc_ref_n(v_toEnvExtension_4600_, 2);
v___x_4611_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4600_, v_env_4585_);
lean_dec_ref(v_env_4585_);
v___x_4612_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4600_, v___x_4611_, v___f_4604_, v_asyncMode_4601_, v___x_4605_, v___x_4606_);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 0, v___x_4612_);
v___x_4614_ = v___x_4594_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v___x_4612_);
v___x_4614_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
return v___x_4614_;
}
}
}
else
{
lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4623_; 
lean_inc(v_name_4597_);
lean_dec(v_a_4592_);
lean_dec_ref_known(v_entry_4590_, 3);
lean_dec_ref(v_env_4585_);
v___x_4616_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4617_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4597_, v___x_4598_);
v___x_4618_ = lean_string_append(v___x_4616_, v___x_4617_);
lean_dec_ref(v___x_4617_);
v___x_4619_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4620_ = lean_string_append(v___x_4618_, v___x_4619_);
v___x_4621_ = lean_mk_io_user_error(v___x_4620_);
if (v_isShared_4595_ == 0)
{
lean_ctor_set_tag(v___x_4594_, 1);
lean_ctor_set(v___x_4594_, 0, v___x_4621_);
v___x_4623_ = v___x_4594_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v___x_4621_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
}
}
else
{
lean_object* v_a_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4633_; 
lean_dec_ref_known(v_entry_4590_, 3);
lean_dec_ref(v_env_4585_);
v_a_4626_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4633_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4628_ = v___x_4591_;
v_isShared_4629_ = v_isSharedCheck_4633_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_a_4626_);
lean_dec(v___x_4591_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4633_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4631_; 
if (v_isShared_4629_ == 0)
{
v___x_4631_ = v___x_4628_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v_a_4626_);
v___x_4631_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
return v___x_4631_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_registerAttributeOfBuilder_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_4585_ = stack[0].m_obj;
lean_object* v_builderId_4586_ = stack[1].m_obj;
lean_object* v_ref_4587_ = stack[2].m_obj;
lean_object* v_args_4588_ = stack[3].m_obj;
lean_object* v_res_4634_;
v_res_4634_ = l_Lean_registerAttributeOfBuilder(v_env_4585_, v_builderId_4586_, v_ref_4587_, v_args_4588_);
stack->m_obj
 = v_res_4634_;
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4635_, lean_object* v_builderId_4636_, lean_object* v_ref_4637_, lean_object* v_args_4638_, lean_object* v_a_4639_){
_start:
{
lean_object* v_res_4640_; 
v_res_4640_ = l_Lean_registerAttributeOfBuilder(v_env_4635_, v_builderId_4636_, v_ref_4637_, v_args_4638_);
return v_res_4640_;
}
}
lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_){
_start:
{
if (lean_obj_tag(v_x_4641_) == 0)
{
lean_object* v_a_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; 
v_a_4645_ = lean_ctor_get(v_x_4641_, 0);
lean_inc(v_a_4645_);
lean_dec_ref_known(v_x_4641_, 1);
v___x_4646_ = l_Lean_stringToMessageData(v_a_4645_);
v___x_4647_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4646_, v___y_4642_, v___y_4643_);
return v___x_4647_;
}
else
{
lean_object* v_a_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4655_; 
v_a_4648_ = lean_ctor_get(v_x_4641_, 0);
v_isSharedCheck_4655_ = !lean_is_exclusive(v_x_4641_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4650_ = v_x_4641_;
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_a_4648_);
lean_dec(v_x_4641_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v___x_4653_; 
if (v_isShared_4651_ == 0)
{
lean_ctor_set_tag(v___x_4650_, 0);
v___x_4653_ = v___x_4650_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v_a_4648_);
v___x_4653_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
return v___x_4653_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4641_ = stack[0].m_obj;
lean_object* v___y_4642_ = stack[1].m_obj;
lean_object* v___y_4643_ = stack[2].m_obj;
lean_object* v_res_4656_;
v_res_4656_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4641_, v___y_4642_, v___y_4643_);
stack->m_obj
 = v_res_4656_;
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_){
_start:
{
lean_object* v_res_4661_; 
v_res_4661_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4657_, v___y_4658_, v___y_4659_);
lean_dec(v___y_4659_);
lean_dec_ref(v___y_4658_);
return v_res_4661_;
}
}
lean_object* l_Lean_Attribute_add(lean_object* v_declName_4662_, lean_object* v_attrName_4663_, lean_object* v_stx_4664_, uint8_t v_kind_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_){
_start:
{
lean_object* v___x_4669_; lean_object* v_env_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
v___x_4669_ = lean_st_ref_get(v_a_4667_);
v_env_4670_ = lean_ctor_get(v___x_4669_, 0);
lean_inc_ref(v_env_4670_);
lean_dec(v___x_4669_);
v___x_4671_ = l_Lean_getAttributeImpl(v_env_4670_, v_attrName_4663_);
v___x_4672_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4671_, v_a_4666_, v_a_4667_);
if (lean_obj_tag(v___x_4672_) == 0)
{
lean_object* v_a_4673_; lean_object* v_add_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
v_a_4673_ = lean_ctor_get(v___x_4672_, 0);
lean_inc(v_a_4673_);
lean_dec_ref_known(v___x_4672_, 1);
v_add_4674_ = lean_ctor_get(v_a_4673_, 1);
lean_inc_ref(v_add_4674_);
lean_dec(v_a_4673_);
v___x_4675_ = lean_box(v_kind_4665_);
lean_inc(v_a_4667_);
lean_inc_ref(v_a_4666_);
v___x_4676_ = lean_apply_6(v_add_4674_, v_declName_4662_, v_stx_4664_, v___x_4675_, v_a_4666_, v_a_4667_, lean_box(0));
return v___x_4676_;
}
else
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4684_; 
lean_dec(v_stx_4664_);
lean_dec(v_declName_4662_);
v_a_4677_ = lean_ctor_get(v___x_4672_, 0);
v_isSharedCheck_4684_ = !lean_is_exclusive(v___x_4672_);
if (v_isSharedCheck_4684_ == 0)
{
v___x_4679_ = v___x_4672_;
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v___x_4672_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4682_; 
if (v_isShared_4680_ == 0)
{
v___x_4682_ = v___x_4679_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_a_4677_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Attribute_add_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_4662_ = stack[0].m_obj;
lean_object* v_attrName_4663_ = stack[1].m_obj;
lean_object* v_stx_4664_ = stack[2].m_obj;
uint8_t v_kind_4665_ = stack[3].m_num;
lean_object* v_a_4666_ = stack[4].m_obj;
lean_object* v_a_4667_ = stack[5].m_obj;
lean_object* v_res_4685_;
v_res_4685_ = l_Lean_Attribute_add(v_declName_4662_, v_attrName_4663_, v_stx_4664_, v_kind_4665_, v_a_4666_, v_a_4667_);
stack->m_obj
 = v_res_4685_;
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
lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4695_, lean_object* v_x_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_){
_start:
{
lean_object* v___x_4700_; 
v___x_4700_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4696_, v___y_4697_, v___y_4698_);
return v___x_4700_;
}
}
LEAN_EXPORT void l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4696_ = stack[1].m_obj;
lean_object* v___y_4697_ = stack[2].m_obj;
lean_object* v___y_4698_ = stack[3].m_obj;
lean_object* v_res_4701_;
v_res_4701_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_box(0), v_x_4696_, v___y_4697_, v___y_4698_);
stack->m_obj
 = v_res_4701_;
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4702_, lean_object* v_x_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
lean_object* v_res_4707_; 
v_res_4707_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4702_, v_x_4703_, v___y_4704_, v___y_4705_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
return v_res_4707_;
}
}
lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4708_, lean_object* v_attrName_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_){
_start:
{
lean_object* v___x_4713_; lean_object* v_env_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; 
v___x_4713_ = lean_st_ref_get(v_a_4711_);
v_env_4714_ = lean_ctor_get(v___x_4713_, 0);
lean_inc_ref(v_env_4714_);
lean_dec(v___x_4713_);
v___x_4715_ = l_Lean_getAttributeImpl(v_env_4714_, v_attrName_4709_);
v___x_4716_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4715_, v_a_4710_, v_a_4711_);
if (lean_obj_tag(v___x_4716_) == 0)
{
lean_object* v_a_4717_; lean_object* v_erase_4718_; lean_object* v___x_4719_; 
v_a_4717_ = lean_ctor_get(v___x_4716_, 0);
lean_inc(v_a_4717_);
lean_dec_ref_known(v___x_4716_, 1);
v_erase_4718_ = lean_ctor_get(v_a_4717_, 2);
lean_inc_ref(v_erase_4718_);
lean_dec(v_a_4717_);
lean_inc(v_a_4711_);
lean_inc_ref(v_a_4710_);
v___x_4719_ = lean_apply_4(v_erase_4718_, v_declName_4708_, v_a_4710_, v_a_4711_, lean_box(0));
return v___x_4719_;
}
else
{
lean_object* v_a_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4727_; 
lean_dec(v_declName_4708_);
v_a_4720_ = lean_ctor_get(v___x_4716_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4716_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4722_ = v___x_4716_;
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_a_4720_);
lean_dec(v___x_4716_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4725_; 
if (v_isShared_4723_ == 0)
{
v___x_4725_ = v___x_4722_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_a_4720_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
return v___x_4725_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Attribute_erase_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_4708_ = stack[0].m_obj;
lean_object* v_attrName_4709_ = stack[1].m_obj;
lean_object* v_a_4710_ = stack[2].m_obj;
lean_object* v_a_4711_ = stack[3].m_obj;
lean_object* v_res_4728_;
v_res_4728_ = l_Lean_Attribute_erase(v_declName_4708_, v_attrName_4709_, v_a_4710_, v_a_4711_);
stack->m_obj
 = v_res_4728_;
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4729_, lean_object* v_attrName_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_){
_start:
{
lean_object* v_res_4734_; 
v_res_4734_ = l_Lean_Attribute_erase(v_declName_4729_, v_attrName_4730_, v_a_4731_, v_a_4732_);
lean_dec(v_a_4732_);
lean_dec_ref(v_a_4731_);
return v_res_4734_;
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___lam__0(lean_object* v___y_4735_, lean_object* v_ps_4736_){
_start:
{
lean_object* v_importedEntries_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4744_; 
v_importedEntries_4737_ = lean_ctor_get(v_ps_4736_, 0);
v_isSharedCheck_4744_ = !lean_is_exclusive(v_ps_4736_);
if (v_isSharedCheck_4744_ == 0)
{
lean_object* v_unused_4745_; 
v_unused_4745_ = lean_ctor_get(v_ps_4736_, 1);
lean_dec(v_unused_4745_);
v___x_4739_ = v_ps_4736_;
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_importedEntries_4737_);
lean_dec(v_ps_4736_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4742_; 
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 1, v___y_4735_);
v___x_4742_ = v___x_4739_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v_importedEntries_4737_);
lean_ctor_set(v_reuseFailAlloc_4743_, 1, v___y_4735_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4746_, lean_object* v_x_4747_){
_start:
{
if (lean_obj_tag(v_x_4747_) == 0)
{
return v_x_4746_;
}
else
{
lean_object* v_key_4748_; lean_object* v_value_4749_; lean_object* v_tail_4750_; lean_object* v_newEntries_4751_; lean_object* v_map_4752_; uint8_t v___x_4753_; 
v_key_4748_ = lean_ctor_get(v_x_4747_, 0);
lean_inc(v_key_4748_);
v_value_4749_ = lean_ctor_get(v_x_4747_, 1);
lean_inc(v_value_4749_);
v_tail_4750_ = lean_ctor_get(v_x_4747_, 2);
lean_inc(v_tail_4750_);
lean_dec_ref_known(v_x_4747_, 3);
v_newEntries_4751_ = lean_ctor_get(v_x_4746_, 0);
v_map_4752_ = lean_ctor_get(v_x_4746_, 1);
v___x_4753_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4752_, v_key_4748_);
if (v___x_4753_ == 0)
{
lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4762_; 
lean_inc_ref(v_map_4752_);
lean_inc(v_newEntries_4751_);
v_isSharedCheck_4762_ = !lean_is_exclusive(v_x_4746_);
if (v_isSharedCheck_4762_ == 0)
{
lean_object* v_unused_4763_; lean_object* v_unused_4764_; 
v_unused_4763_ = lean_ctor_get(v_x_4746_, 1);
lean_dec(v_unused_4763_);
v_unused_4764_ = lean_ctor_get(v_x_4746_, 0);
lean_dec(v_unused_4764_);
v___x_4755_ = v_x_4746_;
v_isShared_4756_ = v_isSharedCheck_4762_;
goto v_resetjp_4754_;
}
else
{
lean_dec(v_x_4746_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4762_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v___x_4757_; lean_object* v___x_4759_; 
v___x_4757_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4752_, v_key_4748_, v_value_4749_);
if (v_isShared_4756_ == 0)
{
lean_ctor_set(v___x_4755_, 1, v___x_4757_);
v___x_4759_ = v___x_4755_;
goto v_reusejp_4758_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_newEntries_4751_);
lean_ctor_set(v_reuseFailAlloc_4761_, 1, v___x_4757_);
v___x_4759_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4758_;
}
v_reusejp_4758_:
{
v_x_4746_ = v___x_4759_;
v_x_4747_ = v_tail_4750_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4749_);
lean_dec(v_key_4748_);
v_x_4747_ = v_tail_4750_;
goto _start;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4766_, size_t v_i_4767_, size_t v_stop_4768_, lean_object* v_b_4769_){
_start:
{
uint8_t v___x_4770_; 
v___x_4770_ = lean_usize_dec_eq(v_i_4767_, v_stop_4768_);
if (v___x_4770_ == 0)
{
lean_object* v___x_4771_; lean_object* v___x_4772_; size_t v___x_4773_; size_t v___x_4774_; 
v___x_4771_ = lean_array_uget_borrowed(v_as_4766_, v_i_4767_);
lean_inc(v___x_4771_);
v___x_4772_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4769_, v___x_4771_);
v___x_4773_ = ((size_t)1ULL);
v___x_4774_ = lean_usize_add(v_i_4767_, v___x_4773_);
v_i_4767_ = v___x_4774_;
v_b_4769_ = v___x_4772_;
goto _start;
}
else
{
return v_b_4769_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4766_ = stack[0].m_obj;
size_t v_i_4767_ = stack[1].m_num;
size_t v_stop_4768_ = stack[2].m_num;
lean_object* v_b_4769_ = stack[3].m_obj;
lean_object* v_res_4776_;
v_res_4776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4766_, v_i_4767_, v_stop_4768_, v_b_4769_);
stack->m_obj
 = v_res_4776_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4777_, lean_object* v_i_4778_, lean_object* v_stop_4779_, lean_object* v_b_4780_){
_start:
{
size_t v_i_boxed_4781_; size_t v_stop_boxed_4782_; lean_object* v_res_4783_; 
v_i_boxed_4781_ = lean_unbox_usize(v_i_4778_);
lean_dec(v_i_4778_);
v_stop_boxed_4782_ = lean_unbox_usize(v_stop_4779_);
lean_dec(v_stop_4779_);
v_res_4783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4777_, v_i_boxed_4781_, v_stop_boxed_4782_, v_b_4780_);
lean_dec_ref(v_as_4777_);
return v_res_4783_;
}
}
lean_object* lean_update_env_attributes(lean_object* v_env_4784_){
_start:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___y_4791_; lean_object* v_toEnvExtension_4803_; lean_object* v_asyncMode_4804_; lean_object* v_buckets_4805_; lean_object* v___x_4806_; uint8_t v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; uint8_t v___x_4811_; 
v___x_4786_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4787_ = l_Lean_attributeMapRef;
v___x_4788_ = lean_st_ref_get(v___x_4787_);
v___x_4789_ = l_Lean_attributeExtension;
v_toEnvExtension_4803_ = lean_ctor_get(v___x_4789_, 0);
v_asyncMode_4804_ = lean_ctor_get(v_toEnvExtension_4803_, 2);
v_buckets_4805_ = lean_ctor_get(v___x_4788_, 1);
lean_inc_ref(v_buckets_4805_);
lean_dec(v___x_4788_);
v___x_4806_ = lean_box(0);
v___x_4807_ = 0;
lean_inc_ref(v_env_4784_);
v___x_4808_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4786_, v___x_4789_, v_env_4784_, v_asyncMode_4804_, v___x_4806_, v___x_4807_);
v___x_4809_ = lean_unsigned_to_nat(0u);
v___x_4810_ = lean_array_get_size(v_buckets_4805_);
v___x_4811_ = lean_nat_dec_lt(v___x_4809_, v___x_4810_);
if (v___x_4811_ == 0)
{
lean_dec_ref(v_buckets_4805_);
v___y_4791_ = v___x_4808_;
goto v___jp_4790_;
}
else
{
size_t v___x_4812_; size_t v___x_4813_; lean_object* v___x_4814_; 
v___x_4812_ = ((size_t)0ULL);
v___x_4813_ = lean_usize_of_nat(v___x_4810_);
v___x_4814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4805_, v___x_4812_, v___x_4813_, v___x_4808_);
lean_dec_ref(v_buckets_4805_);
v___y_4791_ = v___x_4814_;
goto v___jp_4790_;
}
v___jp_4790_:
{
lean_object* v_toEnvExtension_4792_; lean_object* v_asyncMode_4793_; uint8_t v_logWrites_4794_; lean_object* v___f_4795_; lean_object* v___x_4796_; uint8_t v___x_4797_; 
v_toEnvExtension_4792_ = lean_ctor_get(v___x_4789_, 0);
v_asyncMode_4793_ = lean_ctor_get(v_toEnvExtension_4792_, 2);
v_logWrites_4794_ = lean_ctor_get_uint8(v_toEnvExtension_4792_, sizeof(void*)*6);
v___f_4795_ = lean_alloc_closure((void*)(l_Lean_updateEnvAttributesImpl___lam__0), 2, 1);
lean_closure_set(v___f_4795_, 0, v___y_4791_);
v___x_4796_ = lean_box(0);
v___x_4797_ = 1;
if (v_logWrites_4794_ == 0)
{
lean_object* v___x_4798_; lean_object* v___x_4799_; 
lean_inc_ref(v_toEnvExtension_4792_);
v___x_4798_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4792_, v_env_4784_, v___f_4795_, v_asyncMode_4793_, v___x_4796_, v___x_4797_);
v___x_4799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4799_, 0, v___x_4798_);
return v___x_4799_;
}
else
{
lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; 
lean_inc_ref_n(v_toEnvExtension_4792_, 2);
v___x_4800_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4792_, v_env_4784_);
lean_dec_ref(v_env_4784_);
v___x_4801_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4792_, v___x_4800_, v___f_4795_, v_asyncMode_4793_, v___x_4796_, v___x_4797_);
v___x_4802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4802_, 0, v___x_4801_);
return v___x_4802_;
}
}
}
}
LEAN_EXPORT void lean_update_env_attributes_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_4784_ = stack[0].m_obj;
lean_object* v_res_4815_;
v_res_4815_ = lean_update_env_attributes(v_env_4784_);
stack->m_obj
 = v_res_4815_;
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4816_, lean_object* v_a_4817_){
_start:
{
lean_object* v_res_4818_; 
v_res_4818_ = lean_update_env_attributes(v_env_4816_);
return v_res_4818_;
}
}
lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v_size_4822_; lean_object* v___x_4823_; 
v___x_4820_ = l_Lean_attributeMapRef;
v___x_4821_ = lean_st_ref_get(v___x_4820_);
v_size_4822_ = lean_ctor_get(v___x_4821_, 0);
lean_inc(v_size_4822_);
lean_dec(v___x_4821_);
v___x_4823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4823_, 0, v_size_4822_);
return v___x_4823_;
}
}
LEAN_EXPORT void lean_get_num_attributes_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4824_;
v_res_4824_ = lean_get_num_attributes();
stack->m_obj
 = v_res_4824_;
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4825_){
_start:
{
lean_object* v_res_4826_; 
v_res_4826_ = lean_get_num_attributes();
return v_res_4826_;
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
